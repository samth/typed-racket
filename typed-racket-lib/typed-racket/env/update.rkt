#lang racket/base
(require (except-in "../utils/utils.rkt" infer)
         racket/match racket/function racket/lazy-require
         (except-in racket/contract ->* -> )
         (prefix-in c: (contract-req))
         (utils tc-utils)
         (env lexical-env lookup type-env-structs)
         (logic prop-ops)
         (rep type-rep object-rep filter-rep rep-utils)
         (typecheck tc-subst)
         (except-in "../types/abbrev.rkt" one-of/c)
         (for-syntax racket/base))

(lazy-require
 ("../types/remove-intersect.rkt" (overlap remove))
 ("../types/restrict.rkt" (restrict))
 ("../types/type-ref-path.rkt" (try/obj-ty+path->ty))
 ("../types/numeric-tower.rkt" (integer-type int-type-bounds bounded-int-type?)) 
 ("../logic/type-update.rkt" (update-type))
 ("../types/subtype.rkt" (subtype))
 ("../types/union.rkt" (Un)))

(provide update-env/atom update-env/obj-type atomic-prop?)

(define-for-syntax (DEBUG)
  #f)

(define-syntax (LOG stx)
  (if (DEBUG)
      (syntax-case stx ()
        [(_ args ...)
         #'(printf args ...)])
      #'(void)))

(define (atomic-prop? p)
         (or (Bot? p) (Top? p) (TypeFilter? p) (NotTypeFilter? p)))

;; remove from the negative type info types that are impossible
;; based on the current positive facts in the environment
(define/cond-contract (recalc-negative-type ty+ ty-)
  (c:-> Type? Type? Type?)
  (match ty-
    [(Union: ts)
     (apply Un (filter (curry overlap ty+) ts))]
    [else (if (overlap ty+ ty-)
              ty-
              -Nothing)]))

(define (update-env/obj-type env o t contra-env)
  (update-env/type+ env t o contra-env))


(define/cond-contract (make-positive-notifier x new-props-box env)
  (c:-> identifier? (box/c (listof Filter?)) env?
        (c:-> Type/c Type/c (or/c #f (listof PathElem?))
              Type/c))
  (λ (old-t new-t path-stack)
    (define obj (and path-stack (make-Path (reverse path-stack) x)))
    (cond
      ;; we're in a context where we shouldn't assume things (e.g. nested in a union type)
      [(not path-stack) new-t]
      ;; we are now a more specific int type w/ bounds -- go ahead and add the bounds!
      [(bounded-int-type? new-t)
       (define-values (new-low new-high) (int-type-bounds new-t))
       (when new-low
         (define leqsli (-leqSLI (-lexp new-low) (-lexp (list 1 obj))))
         (unless (SLIs-contain? (env-SLIs env) leqsli)
           (set-box! new-props-box
                     (cons leqsli (unbox new-props-box)))))
       (when new-high
         (define leqsli (-leqSLI (-lexp (list 1 obj)) (-lexp new-high)))
         (unless (SLIs-contain? (env-SLIs env) leqsli)
           (set-box! new-props-box
                     (cons leqsli (unbox new-props-box)))))
       new-t]
      ;; we used to be a union and now we're not --- check if there are props
      ;; nested inside the union we can now assume to be true!
      [(and (Union? old-t) (not (Union? new-t)))
       (define-values (t* nested-props) (extract-props-from-type obj new-t))
       (when (not (null? nested-props))
         (set-box! new-props-box (append nested-props (unbox new-props-box))))
       ((make-positive-notifier x new-props-box env) new-t t* path-stack)]
      ;; we can infer the length of heterogeneous vectors from their list of types, of course!
      [(HeterogeneousVector? new-t)
       (define eqsli (-eqSLI (-lexp (-acc-path -len obj))
                             (-lexp (length (HeterogeneousVector-elems new-t)))))
       (unless (SLIs-contain? (env-SLIs env) eqsli)
         (set-box! new-props-box
                   (cons eqsli (unbox new-props-box))))
       new-t]
      [else
       (match new-t
         ;; if we're now a refinement, assume the refining proposition and just return
         ;; the refined type (recursively, of course)
         [(Refine-unsafe: t p)
          (define prop (subst-filter p (list 0 0) obj #t))
          (when (not (Top? p))
            (set-box! new-props-box (cons p (unbox new-props-box))))
          ((make-positive-notifier x new-props-box env) old-t t path-stack)]
         [_ new-t])])))

(define/cond-contract (update-env/type+ env new-o-ty o contra-env)
  (c:-> env? Type? Object? procedure?
        (values (c:or/c env? #f) ;; updated environment
                (c:listof Filter?))) ;; new derived filters
  (LOG "update-env/type+: ~a with ~a\n" o new-o-ty)
  (define new-props-box (box '()))
  (match o
    ;; we're updating a path object
    [(Path: π (? identifier? x))
     (define notify (make-positive-notifier x new-props-box env))
     ;; grab the type we know for x right now
     (define x-ty+
       (let ([env-type (lookup-id-type x env #:fail (const #f))])
         ;; look up the type, if its a refinement for some reason
         ;; tease apart the type and props
         (let loop ([env-type env-type])
           (match env-type
             [(Refine/obj: o rt rp)
              (set-box! new-props-box (cons rp (unbox new-props-box)))
              (loop rt)]
             [_ env-type]))))
     ;;TODO lookup-id-type can get global 
     (LOG "update-env/type+: x-ty+: ~a\n" x-ty+)
     ;; grab the type we know x is not right now
     (define x-ty- (lookup-id-not-type x env #:fail (const #f)))
     (LOG "update-env/type+: x-ty-: ~a\n" x-ty-)
     ;; combine our current info w/ the new type info
     ;; to redefine the positive and negative types for this id
     (define-values (new-x-ty+ new-x-ty-)
       (cond
         [(not x-ty+) (values (try/obj-ty+path->ty new-o-ty π #:fail-type -Any)
                              (or x-ty- -Nothing))]
         [(not x-ty-)
          (with-lexical-env
           (env-erase-id-type env x)
           (values (update-type x-ty+ new-o-ty #t π notify)
                   -Nothing))]
         [else
          (with-lexical-env
           (env-erase-id-type env x)
           (let* ([new-x-ty+ (update-type x-ty+ new-o-ty #t π notify)]
                  [new-x-ty+ (update-type new-x-ty+ x-ty- #f null notify)])
             (values new-x-ty+
                     (recalc-negative-type new-x-ty+ x-ty-))))]))
     (LOG "update-env/type+: new-x-ty+: ~a\n" new-x-ty+)
     (LOG "update-env/type+: new-x-ty-: ~a\n" new-x-ty-)
     ;; extend the environment (or fail if contradictory info derived)
     (cond
       [(Nothing? new-x-ty+)
        (values (contra-env) '())]
       [(type-equal? new-x-ty- -Any)
        (values (contra-env) '())]
       [else
        (define xobj (-id-path x))
        (match new-x-ty+
          [(Refine/obj: xobj r-t r-p)
           (values (naive-extend/id-type- (env-erase-id-type env x) x new-x-ty-)
                   (list* (-is-type xobj r-t) r-p (unbox new-props-box)))]
          [_ (values (naive-extend/id-type-info env x new-x-ty+ new-x-ty-)
                     (unbox new-props-box))])])]
    ;; we're updating a linear expression's type
    [(? LExp? l)
     ;; grab the type we know l is currently and
     ;; combine it with the new type
     (define l-ty
       (with-lexical-env
        empty-env
        (restrict (lookup-obj-type l env #:fail (const (integer-type))) new-o-ty)))
     ;; grab bounds if they're new
     (when (bounded-int-type? l-ty)
       (define-values (new-low new-high) (int-type-bounds new-o-ty))
       (when new-low
         (let ([leqsli (-leqSLI (-lexp new-low) l)])
           (unless (and (SLI? leqsli) (SLIs-contain? (env-SLIs env) leqsli))
             (set-box! new-props-box
                       (cons leqsli (unbox new-props-box))))))
       (when new-high
         (let ([leqsli (-leqSLI l (-lexp new-high))])
           (unless (and (SLI? leqsli) (SLIs-contain? (env-SLIs env) leqsli))
             (set-box! new-props-box
                       (cons leqsli (unbox new-props-box)))))))
     
     (values (naive-extend/lexp-type env l l-ty) (unbox new-props-box))]
    [_ (int-err "invalid object for updating the environment! ~a" o)]))

(define/cond-contract (update-env/type- env new-o-ty o contra-env)
  (c:-> env? Type? Object? (c:or/c #f procedure?)
        (values (c:or/c env? #f) (c:listof Filter?)))
  (LOG "update-env/type-\n")
  (define new-props-box (box '()))
  (match o
    [(Path: π (? identifier? x))
     (define notify (make-positive-notifier x new-props-box env))
     
     (define x-ty+ (lookup-id-type x env #:fail (const #f))) ;; x is of type T
     (LOG "update-env/type- x-ty+: ~a\n" x-ty+)
     (define x-ty- (lookup-id-not-type x env #:fail (const #f))) ;; env says x is not of type T-
     (LOG "update-env/type- x-ty-: ~a\n" x-ty-)
     (define-values (new-x-ty+ new-x-ty-)
       (cond
         [(and x-ty+ x-ty-)
          (with-lexical-env
           (env-erase-id-type env x)
           (let ([new-x-ty+ (update-type (update-type x-ty+ new-o-ty #f π notify) x-ty- #f null notify)])
             (values new-x-ty+
                     (recalc-negative-type
                      new-x-ty+
                      (Un x-ty- (try/obj-ty+path->ty new-o-ty π #:fail-type -Nothing))))))]
         [x-ty+
          (values (update-type x-ty+ new-o-ty #f π notify)
                  (try/obj-ty+path->ty new-o-ty π #:fail-type -Nothing))]
         [x-ty-
          (values -Any
                  (Un x-ty- (try/obj-ty+path->ty new-o-ty π #:fail-type -Nothing)))]
         ;; (or x-ty- (obj-ty+path->id-ty new-o-ty π -Nothing))
         [else
          (values -Any (try/obj-ty+path->ty new-o-ty π #:fail-type -Nothing))]))
     
     (LOG "update-env/type- new-x-ty+: ~a\n" new-x-ty+)
     (LOG "update-env/type- new-x-ty-: ~a\n" new-x-ty-)
     (cond
       [(type-equal? new-x-ty- -Any)
        (values (contra-env) '())]
       [(Nothing? new-x-ty+)
        (values (contra-env) '())]
       [else
        (define xobj (-id-path x))
        (match new-x-ty+
          [(Refine/obj: xobj r-t r-p)
           (values (naive-extend/id-type-info env x -Any new-x-ty-)
                   (list* (-is-type xobj r-t) r-p (unbox new-props-box)))]
          [_ (values (naive-extend/id-type-info env x new-x-ty+ new-x-ty-)
                     (unbox new-props-box))])])]
    [(? LExp? l)
     ;; note: not currently *storing* negative type info about lexps
     ;; this could change in the future...
     (define l-ty
       (remove (lookup-obj-type l env #:fail (const (integer-type))) new-o-ty))
     ;; TODO(amk) maybe do something more complex here with LExp and SLI info?
     (cond
       [(Bottom? l-ty)
        (values (contra-env) '())]
       [else
        (values (naive-extend/lexp-type env l l-ty) (unbox new-props-box))])]
    [_ (int-err "invalid object for updating the environment! ~a" o)]))


;; update-env/atom
;; the 'contra-env' argument is a function that either:
;;    a) produces the desired representation of a trivial environment
;;       (i.e. an environment containing Bottom)
;;    or
;;    b) is a continuation that bails out of the current computation
;; Function description:
;; - Updates an environment w/ an atomic fact.
;; - If the update exposed some new information from exposing a Refine type that
;;   was previously nested within a larger type (e.g. a union) we return this
;;   new information (since this new info could be arbitrarily comlpex, and we're
;;   a simple update function not suited to reason about arbitrary propositions)
;;
;; TODO(AMK): there are more complex refinement cases to consider such as 
;; 1. what about updating refinements that cannot be deconstructed? (i.e. nested
;;    inside other types inside of unions?)
(define/cond-contract (update-env/atom env prop [contra-env (λ _ #f)])
  (c:-> env? atomic-prop? procedure?
        (values (c:or/c env? #f) (c:listof Filter?)))

  (LOG "update-env/atom\n env: ~a\n prop: ~a\n\n"
       env prop)
  
  (define-values (env* new-props)
    (match prop
      [(? Top?) (values env '())]
      [(? Bot?) (values (contra-env) '())]
      [(TypeFilter: t o)
       (update-env/type+ env t o contra-env)]
      [(NotTypeFilter: t o)
       (update-env/type- env t o contra-env)]
      [_ (int-err "invalid update-env prop: ~a" prop)]))

  (LOG "update-env/atom\n new env: ~a\n new props: ~a\n\n"
       env* new-props)

  (values env* new-props))
