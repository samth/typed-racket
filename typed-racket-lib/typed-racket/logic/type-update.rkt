#lang racket/base

(require (except-in "../utils/utils.rkt" infer)
         racket/match racket/function racket/lazy-require racket/list unstable/function
         (except-in racket/contract ->* -> )
         (prefix-in c: (contract-req))
         (utils tc-utils)
         (logic proves)
         (env lookup lexical-env type-env-structs)
         (rep type-rep object-rep filter-rep rep-utils)
         (types tc-result resolve union remove-intersect numeric-tower refine restrict)
         (typecheck tc-subst tc-envops)
         (except-in "../types/abbrev.rkt" one-of/c -> ->*))

 (lazy-require
  #;("../types/remove-intersect.rkt" (overlap))
  ("../types/type-ref-path.rkt" (type-unref/rev-path))
  ("../types/subtype.rkt" (subtype))
  ("../types/filter-ops.rkt" (-and -or)))

(provide update-type/env update-function/arg-types update-type
         unabstract-doms/arg-objs unabstract-rng/arg-objs unabstract-expected/arg-objs)


;; update-type   (formerly simply 'update')
;; it is intended to be used for updating the types of identifiers
;; in some type environment Γ
;; This is update from the ICFP 2010 paper, but with a slight addition:
;; t -- the type to be updated!
;; new-t -- the new type we are updating things with!
;; positive? -- #t for positive (it *is* this type), #f for negative (it is *not* this type)
;; path-list -- down which path into t are we updating?
;; notify -- function to relay that a noteworthy type update has occurred
;; NOTE: Why 'notify'? If we update a type and suddenly have
;; a new integer that has bounds associated with it (i.e. a Byte and [0,255]
;; or if we suddenly have a Refine'd type, then we should notify the caller
;; since we are unable to deal with that new filter/proposition directly --
;; by passing the info to 'notify' and just using the type 'notify' returns
;; we allow callers to speficy the details of how to handle those various issues
(define/cond-contract (update-type orig-t new-t pos? path-list notify)
  (Type/c ;; old type
   Type/c ;; new type
   boolean? ;; #t if positive fact, #f if negative
   (listof PathElem?) ;; path down which to update
   (c:-> Type/c Type/c (or/c #f (listof PathElem?)) Type/c) ;; notification function
   . c:-> .
   Type/c)
  
  ;; build-type: build a type while propogating bottom
  (define (build-type constructor . args)
    (if (memf Bottom? args) -Bottom (apply constructor args)))

  ;; internal update driver
  (define/cond-contract (update orig-t ft reversed-path path-stack)
    (c:-> Type/c Type/c (listof PathElem?) (listof PathElem?)
          Type/c)
    (define (push)
      (and path-stack (cons (car reversed-path) path-stack)))
    (define-values (path-elem rst)
      (match reversed-path
        [(cons h t) (values h t)]
        [_ (values #f #f)]))
    (match (resolve orig-t)
      ;; pair ops
      [(Pair: a d)
       #:when (CarPE? path-elem)
       (define a* (update a ft rst (push)))
       (build-type -pair a* d)]
      [(Pair: a d)
       #:when (CdrPE? path-elem)
       (define d* (update d ft rst (push)))
       (build-type -pair a d*)]

      ;; struct ops
      [(Struct: nm par flds proc poly pred)
       #:when (and (StructPE? path-elem)
                   (match path-elem
                     [(StructPE: (? (λ (s) (subtype orig-t s)) s) _) #t]
                     [_ #f]))
       ;; note: this updates fields regardless of whether or not they are
       ;; a polymorphic field. Because subtyping is nominal and accessor 
       ;; functions do not reflect this, this behavior is unobservable
       ;; except when an a variable aliases the field in a let binding
       (match-define (StructPE: _ idx) path-elem)
       (let*-values ([(lhs rhs) (split-at flds idx)]
                     [(ty* acc-id) (match rhs
                                     [(cons (fld: ty acc-id #f) _)
                                      (values (update ty ft rst (push)) acc-id)]
                                     [_ (int-err "update on mutable struct field")])]) 
         (cond 
           [(Bottom? ty*) ty*]
           [else (let ([flds* (append lhs (cons (make-fld ty* acc-id #f) (cdr rhs)))])
                   (make-Struct nm par flds* proc poly pred))]))]
      
      ;; syntax ops
      [(Syntax: t) #:when (SyntaxPE? path-elem)
       (build-type -Syntax (update t ft rst (push)))]
      
      ;; promise op
      [(Promise: t) #:when (ForcePE? path-elem)
       (build-type -Promise (update t ft rst (push)))]
      
      
      ;; length ops
      [vt #:when (LengthPE? path-elem)
          (cond
            [(and (null? rst)
                  (overlap vt -VectorTop)
                  (overlap ft -Nat)) 
             vt]
            [else -Bottom])]
      
      ;; class field ops
      ;;
      ;; A refinement of a private field in a class is really a refinement of the
      ;; return type of the accessor function for that field (rather than a variable).
      ;; We cannot just refine the type of the argument to the accessor, since that
      ;; is an object type that doesn't mention private fields. Thus we use the
      ;; FieldPE path element as a marker to refine the result of the accessor
      ;; function.
      [(Function: (list (arr: doms (Values: (list (Result: rng _ _))) _ _ _ _)))
       #:when (FieldPE? path-elem)
       (make-Function
        (list (make-arr* doms (update rng ft rst (push)))))]
      
      ;; otherwise
      [t #:when (null? reversed-path)
       (if pos?
           (restrict/notify t ft path-stack notify)
           (notify t (remove t ft) path-stack))]
      
      [(Union: ts)
       (define new-t (apply Un (map (λ (t) (update t ft reversed-path #f)) ts)))
       (notify orig-t new-t path-stack)]

      ;; refine'd types -- go ahead and update the refined type
      [(Refine-unsafe: t p)
       (unsafe-make-Refine* (update t ft reversed-path path-stack) p)]
      
      [_
       (let ([t (type-unref/rev-path ft reversed-path Univ)])
         (if (overlap orig-t t)
             t
             -Bottom))]))

  (update orig-t new-t (reverse path-list) '()))




(define (update-type/env ty env)
  ;(define new-props '())
  
  (define (do-type ty)
    (type-case
     (#:Type do-type #:Filter do-filter #:Object do-obj)
     ty))
  
  (define (do-filter f)
    (filter-case (#:Type do-type
                  #:Filter do-filter
                  #:Object do-obj)
                 f
                 [#:TypeFilter t o 
                  (let ([ty (lookup-obj-type o env #:fail (λ (_) #f))])
                    (cond
                      [(and ty (not (overlap t ty))) -bot]
                      [else f]))]
                 [#:NotTypeFilter t o
                  (let ([ty (lookup-obj-type o env #:fail (λ (_) #f))])
                    (cond
                      [(and ty (subtype t ty #:env env #:obj o)) -bot]
                      [else f]))]
                 [#:AndFilter fs (apply -and (map do-filter fs))]
                 [#:OrFilter fs (apply -or (map do-filter fs))]
                 [#:SLI sli
                        (let ([env-slis (env-SLIs env)])
                          (cond
                            [(SLIs-imply? env-slis sli) -top]
                            [(Bot? (add-SLI sli env-slis)) -bot]
                            [else sli]))]))
  
  (define (do-obj o)
    (object-case (#:Type do-type
                  #:Object do-obj
                  #:PathElem do-pe)
                 o))
  
  (define (do-pe pe)
    (pathelem-case (#:Type do-type
                    #:PathElem do-pe)
                   pe))
  (do-type ty))





(define (update-function/arg-types args-res f-type)
 ;; TODO support polymorphic functions
  ;; e.g. match-define: no matching clause for (All (a) (-> (Listof a) Index))
  ;; if match-define (Function: (list (arr: domss rngs rests drests kwss dep?s) ...))
  ;; grab objects for the arguments if there is one
  (define-values (arg-tys arg-objs)
    (for/lists (a b) ([tcres (in-list args-res)])
      (match tcres
        [(tc-result1: t _ o)
         (values t (and (or (Path? o) (LExp? o))
                        o))]
        [_ (int-err "unknown tc-result type for argument ~a" tcres)])))
  
  (match f-type
    [(Function: (list (and arrs (arr: domss rngs rests drests kwss dep?s)) ...)) 
     #:when (ormap values dep?s)
     (define new-arrs 
       (for/list ([arr (in-list arrs)]
                  [doms (in-list domss)]
                  [rng (in-list rngs)]
                  [rest (in-list rests)]
                  [drest (in-list drests)]
                  [kws (in-list kwss)]
                  [dep? (in-list dep?s)])
         (cond
           [(not dep?) arr]
           [else
            (define tmp-ids (genids (length doms) 'arg))
            (define-values (tmp-doms tmp-rng)
              ((instantiate-many tmp-ids) doms rng))
            ;; replace tmp ids w/ objects when possible in domains
            (define doms*
              (for/list ([d (in-list tmp-doms)])
                (for/fold ([d* d])
                          ([o (in-list arg-objs)]
                           [o-ty (in-list arg-tys)]
                           [id (in-list tmp-ids)])
                  (if o (subst-type d* id o #t o-ty) d*))))
            ;; replace tmp ids w/ objects when possible in the range
            (define rng*
              (for/fold ([r* tmp-rng])
                        ([o (in-list arg-objs)]
                         [o-ty (in-list arg-tys)]
                         [id (in-list tmp-ids)])
                (if o (subst-result r* id o #t o-ty) r*)))
            ;; build props that represent domain's types
            (define dom-ty-props
              (for/list ([tmp-id (in-list tmp-ids)]
                         [o (in-list arg-objs)]
                         [ty (in-list arg-tys)]) ;; was doms*
                (-filter ty (or o (-id-path tmp-id)))))
            ;; update the lexical environment with domain types
            (define-values (env* _)
              (env+props (lexical-env) dom-ty-props #:ingore-non-identifier-ids? #f))
            
            (cond
              [(not env*) (make-arr (map (λ _ Univ) doms) 
                                    rng*
                                    rest
                                    drest
                                    kws
                                    dep?)]
              [else
               (define updated-doms (for/list ([d (in-list doms*)])
                                      (abstract-idents tmp-ids (update-type/env d env*))))
               (define updated-rng (abstract-idents tmp-ids (update-type/env rng* env*)))
               (make-arr updated-doms updated-rng rest drest kws dep?)])])))
     (make-Function new-arrs)]
    [_ f-type]))


;; unabstract-arg-objs : (listof Type) (listof Object)
;; replaces DeBruijn index variables in 'doms' with
;; the objects given in 'objs'
;; -- this allows type inference to more accurately reason about
;; subtyping information since the environment contains type information
;; only about realized objects (no DeBruijns)
(define (unabstract-doms/arg-objs doms objs argtys)
  ;;TODO(AMK) if would be nice to do this subst in one pass with
  ;; a multi-substitution instead of repeaded single substitutions
  (for/list ([dom (in-list doms)])
    (for/fold ([dom dom])
              ([(obj arg-num) (in-indexed (in-list objs))]
               [ty (in-list argtys)])
      (subst-type dom (list 0 arg-num) obj #t ty))))

(define (unabstract-rng/arg-objs rng objs argtys)
  ;;TODO(AMK) if would be nice to do this subst in one pass with
  ;; a multi-substitution instead of repeaded single substitutions
  (for/fold ([rng rng])
            ([(obj arg-num) (in-indexed (in-list objs))]
             [ty (in-list argtys)])
    (subst-result rng (list 0 arg-num) obj #t ty)))

(define (unabstract-expected/arg-objs exptd objs argtys)
  (for/fold ([exptd exptd])
            ([(obj arg-num) (in-indexed (in-list objs))]
             [ty (in-list argtys)])
    (subst-tc-results exptd (list 0 arg-num) obj #t ty)))

