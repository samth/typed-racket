#lang racket/base

;; Functions in this file implement the substitution function in
;; figure 8, pg 8 of "Logical Types for Untyped Languages"

(require "../utils/utils.rkt"
         "../utils/tc-utils.rkt"
         racket/match
         (contract-req)
         "../env/lexical-env.rkt"
         "../types/utils.rkt"
         "../types/prop-ops.rkt"
         "../types/subtype.rkt"
         "../types/path-type.rkt"
         "../types/subtract.rkt"
         "../types/overlap.rkt"
         (except-in "../types/abbrev.rkt" -> ->* one-of/c)
         (only-in "../infer/infer.rkt" intersect restrict)
         "../rep/core-rep.rkt"
         "../rep/type-rep.rkt"
         "../rep/object-rep.rkt"
         "../rep/prop-rep.rkt"
         "../rep/rep-utils.rkt"
         "../rep/values-rep.rkt")

(provide instantiate-obj+simplify)

(provide/cond-contract
 [values->tc-results (->* (SomeValues? (listof OptObject?))
                          ((listof Type?))
                          full-tc-results/c)]
 [values->tc-results/explicit-subst
  (-> SomeValues?
      (listof (cons/c exact-nonnegative-integer?
                      (cons/c OptObject?
                              Type?)))
      full-tc-results/c)]
 [erase-identifiers (-> tc-results/c
                        (listof identifier?)
                        tc-results/c)])


;; Substitutes the given objects into the values and turns it into a
;; tc-result.  This matches up to the substitutions in the T-App rule
;; from the ICFP paper.
;; NOTE! 'os' should contain no unbound relative addresses (i.e. "free" 
;;       De Bruijn indices) as those indices will NOT be updated if they
;;        are substituted under binders.
(define (values->tc-results v objs [types '()])
  (values->tc-results/explicit-subst
   v
   (for/list ([o (in-list objs)]
              [t (in-list/rest types Univ)]
              [idx (in-naturals)])
     (list* idx o t))))

(define (values->tc-results/explicit-subst v subst)
  (define res->tc-res
    (match-lambda
      [(Result: t ps o n-exi) (-tc-result t ps o (not (zero? n-exi)))]))

  (match (instantiate-obj+simplify v subst)
    [(AnyValues: p)
     (-tc-any-results p)]
    [(Values: rs)
     (-tc-results (map res->tc-res rs) #f)]
    [(ValuesDots: rs dty dbound)
     (-tc-results (map res->tc-res rs) (make-RestDots dty dbound))]))

;; erase-identifiers
;; replaces all occurrences of the given identifiers with -empty-obj,
;; tracking polarity in the same way as instantiate-obj+simplify below:
;; props about an erased identifier become tt in positive positions and
;; ff in negative ones (a plain substitution of -empty-obj would let the
;; prop constructors collapse them to tt everywhere, which is unsound
;; underneath function domains)
(define (erase-identifiers res names)
  (define (erased? nm)
    (and (identifier? nm)
         (member nm names free-identifier=?)
         #t))
  (let subst/pol ([rep res] [pol #t])
    (define (subst rep) (subst/pol rep pol))
    (define (subst/flip rep) (subst/pol rep (not pol)))
    (match rep
      ;; the domain (incl. rest/keyword args) is a negative position
      [(Arrow: dom rst kws rng rng-T+)
       (make-Arrow (map subst/flip dom)
                   (and rst (subst/flip rst))
                   (map subst/flip kws)
                   (subst rng)
                   rng-T+)]
      [(DepFun: dom pre rng)
       (make-DepFun (map subst/flip dom)
                    (subst/flip pre)
                    (subst rng))]
      [(Path: _ (? erased?)) -empty-obj]
      [(TypeProp: (Path: _ (? erased?)) _) (if pol -tt -ff)]
      [(NotTypeProp: (Path: _ (? erased?)) _) (if pol -tt -ff)]
      ;; the type in a NotTypeProp is underneath a negation,
      ;; so polarity flips
      [(NotTypeProp: obj prop-ty)
       (make-NotTypeProp (subst obj) (subst/flip prop-ty))]
      [(LeqProp: lhs rhs)
       (define new-lhs (subst lhs))
       (define new-rhs (subst rhs))
       (if (and (not pol)
                (or (Empty? new-lhs) (Empty? new-rhs)))
           -ff
           (make-LeqProp new-lhs new-rhs))]
      [(tc-result: t ps (Path: _ (? erased?)))
       (-tc-result (subst t)
                   (if pol (subst ps) (-PS -ff -ff))
                   -empty-obj)]
      [(Result: t ps (Path: _ (? erased?)))
       (make-Result (subst t)
                    (if pol (subst ps) (-PS -ff -ff))
                    -empty-obj)]
      [_ (Rep-fmap rep subst)])))

(define (instantiate-obj+simplify rep mapping)
  ;; lookup: if idx has a mapping,
  ;; then returns (cons/c OptObject? Type?),
  ;; else returns #f
  (define (lookup idx) (match (assv idx mapping)
                         [(cons _ entry) entry]
                         [_ #f]))
  ;; pol tracks the polarity of the current position: #t in positive
  ;; positions, where a prop is a fact we learn and so may soundly be
  ;; weakened, #f in negative positions (underneath a function domain,
  ;; or a negated type), where a prop is an obligation the context must
  ;; discharge and so may only be strengthened. When a variable being
  ;; substituted away has no object (Empty), props mentioning it can no
  ;; longer be expressed: they become tt in positive positions but must
  ;; become ff in negative ones — erasing an obligation to tt would let
  ;; arguments that never discharge it slip through (see figure 8 of the
  ;; paper, where substitution carries this polarity).
  (let subst/lvl ([rep rep] [lvl 0] [pol #t])
    (define (subst rep) (subst/lvl rep lvl pol))
    (define (subst/flip rep) (subst/lvl rep lvl (not pol)))
    (match rep
      ;; Functions
      ;; increment the level of the substituted object;
      ;; the domain (incl. rest/keyword args) is a negative position
      [(Arrow: dom rst kws rng rng-T+)
       (make-Arrow (map subst/flip dom)
                   (and rst (subst/flip rst))
                   (map subst/flip kws)
                   (subst/lvl rng (add1 lvl) pol)
                   rng-T+)]
      [(DepFun: dom pre rng)
       (make-DepFun (for/list ([d (in-list dom)])
                      (subst/lvl d (add1 lvl) (not pol)))
                    (subst/lvl pre (add1 lvl) (not pol))
                    (subst/lvl rng (add1 lvl) pol))]
      [(Intersection: ts raw-prop)
       (-refine (make-Intersection (map subst ts))
                (subst/lvl raw-prop (add1 lvl) pol))]
      [(Path: flds (cons (== lvl) (app lookup (cons o _))))
       (make-Path (map subst flds) o)]
      ;; restrict with the type for results and props
      [(TypeProp: (Path: flds (cons (== lvl) (app lookup (? pair? entry))))
                  prop-ty)
       (define o (make-Path (map subst flds) (car entry)))
       (define o-ty (or (path-type flds (cdr entry)) Univ))
       (define new-prop-ty (intersect prop-ty o-ty o))
       (cond
         [(Bottom? new-prop-ty) -ff]
         [(and (not (F? prop-ty))  (subtype o-ty prop-ty)) -tt]
         [(Empty? o) (if pol -tt -ff)]
         [else (-is-type o new-prop-ty)])]
      [(NotTypeProp: (Path: flds (cons (== lvl) (app lookup (? pair? entry))))
                     prop-ty)
       (define o (make-Path (map subst flds) (car entry)))
       (define o-ty (or (path-type flds (cdr entry)) Univ))
       (define new-o-ty (subtract o-ty prop-ty o))
       (define new-prop-ty (restrict prop-ty o-ty o))
       (cond
         [(or (Bottom? new-o-ty)
              (Univ? new-prop-ty))
          -ff]
         ;; no overlap between the type of the object and the
         ;; negated type: the prop is known to hold
         [(Bottom? new-prop-ty) -tt]
         [(Empty? o) (if pol -tt -ff)]
         [else (-not-type o new-prop-ty)])]
      ;; the type in a NotTypeProp is underneath a negation,
      ;; so polarity flips
      [(NotTypeProp: obj prop-ty)
       (make-NotTypeProp (subst obj) (subst/flip prop-ty))]
      [(LeqProp: lhs rhs)
       (define new-lhs (subst lhs))
       (define new-rhs (subst rhs))
       (if (and (not pol)
                (or (Empty? new-lhs) (Empty? new-rhs)))
           -ff
           (make-LeqProp new-lhs new-rhs))]
      [(tc-result: orig-t
                   orig-ps
                   (Path: flds (cons (== lvl) (app lookup (? pair? entry)))))
       (define o (make-Path (map subst flds) (car entry)))
       (define t (intersect orig-t (or (path-type flds (cdr entry)) Univ)))
       (define ps (if (and (not pol) (Empty? o))
                      (-PS -ff -ff)
                      (subst orig-ps)))
       (-tc-result t ps o)]
      [(Result: orig-t
                orig-ps
                (Path: flds (cons (== lvl) (app lookup (? pair? entry)))))
       (define o (make-Path (map subst flds) (car entry)))
       (define t (intersect orig-t (or (path-type flds (cdr entry)) Univ)))
       ;; in a negative position a Result whose object is erased is an
       ;; obligation that can no longer be stated; strengthen the props
       ;; to ff rather than silently dropping the object requirement
       (define ps (if (and (not pol) (Empty? o))
                      (-PS -ff -ff)
                      (subst orig-ps)))
       (make-Result t ps o)]
      ;; else default fold over subfields
      [_ (Rep-fmap rep subst)])))


