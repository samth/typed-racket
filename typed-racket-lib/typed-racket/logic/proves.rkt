#lang racket/base
(require (except-in "../utils/utils.rkt" infer)
         racket/match racket/function racket/lazy-require racket/list unstable/function
         racket/trace
         (except-in racket/contract ->* -> )
         (prefix-in c: (contract-req))
         (utils tc-utils)
         (env lexical-env lookup type-env-structs)
         (logic prop-ops)
         (rep type-rep object-rep filter-rep rep-utils)
         (typecheck tc-subst tc-metafunctions)
         (except-in "../types/abbrev.rkt" one-of/c)
         (for-syntax racket/base))

(lazy-require
 ("../types/remove-intersect.rkt" (overlap))
 ("../types/type-ref-path.rkt" (id-ty+path->obj-ty obj-ty+path->id-ty))
 ("../types/filter-ops.rkt" (-and -or invert-filter))
 ("../types/numeric-tower.rkt" (integer-type int-type-bounds bounded-int-type?)) 
 ("type-update.rkt" (update-type))
 ("../types/subtype.rkt" (subtype))
 ("../types/union.rkt" (Un)))

(provide proves witnesses update-env/atom simple-proves update-env/obj-type)

(define (simple-proves axioms goal)
  (proves empty-env axioms goal))

(define-for-syntax (DEBUG)
  #f)

(define-syntax (LOG stx)
  (if (DEBUG)
      (syntax-case stx ()
        [(_ args ...)
         #'(printf args ...)])
      #'(void)))

(define-syntax (LOG! stx)
  (if (DEBUG)
      (syntax-case stx ()
        [(_ args ...)
         #'(begin args ...)])
      #'(void)))

(define-syntax (define-for-LOG stx)
  (if (DEBUG)
      (syntax-case stx ()
        [(_ args ...)
         #'(define args ...)])
      #'(void)))

(define-for-LOG DEPTH -1)
(define-for-LOG (DIVE!) (set! DEPTH (add1 DEPTH)))
(define-for-LOG (RISE!) (set! DEPTH (sub1 DEPTH)))

(define/cond-contract (proves env assumptions goal)
  (c:-> env? (listof Filter/c) Filter/c
        boolean?)
  (LOG! (DIVE!))

  (LOG "proves(~a) START!\n env: ~a\n assumptions: ~a\n goal: ~a\n\n"
       DEPTH env assumptions goal)
  
  (define v
    (let/ec exit*
      (define (exit) (exit* #t))
      ;; combine the new props w/ the props already in the environment
      (define-values (compound-props atoms slis)
        (combine-props (apply append (map flatten-nested-props assumptions)) 
                       (env-props+SLIs env)
                       exit))

      (LOG "proves(~a) combined props!\n compound-props: ~a\n atoms: ~a\n slis: ~a\n\n"
           DEPTH compound-props atoms slis)
      
      ;; update the environment based on all the known atoms
      (define-values (env* new-compound-props)
        (let loop ([Γ (replace-props env slis)]
                   [work-list atoms]
                   [complexs '()])
          (match work-list
            [(list) (values Γ complexs)]
            [(list f rst ...)
             (match f
               [(TypeFilter: (? Refine? r) o)
                (LOG "P(~a) initial loop: new refinement: ~a\n\n" DEPTH f)
                (match-let ([(Refine/obj: o t p) r])
                  (loop Γ (list* (-is-type o t) p rst) complexs))]
               [(NotTypeFilter: (? Refine? r) o)
                (match-let* ([(Refine/obj: o t p) r]
                             [is-not-t (-is-not-type o t)]
                             [not-p (invert-filter p)])
                  (LOG "P(~a) initial loop:  negating refinement: ~a\n --> ~a OR ~a\n\n" DEPTH f is-not-t not-p)
                  (loop Γ (cons (-or is-not-t not-p) rst) complexs))]
               [(or (? TypeFilter?) (? NotTypeFilter?))
                (LOG "P(~a) initial loop: new type/not-type filter ~a\n pre env: ~a\n\n"
                     DEPTH f env)
                (define-values (Γ* new-ps) (update-env/atom Γ f exit))
                (LOG "P(~a) initial loop: ~a filter added! \n   post env: ~a\n\n"
                     DEPTH f env)
                (loop Γ* (append new-ps rst) complexs)]
               [(AndFilter: ps)
                (loop Γ (append ps rst) complexs)]
               [_
                (loop Γ rst (cons f complexs))])])))

      (LOG "P(~a) initial loop complete.\n\n"
           DEPTH)
      (define goal* (apply -and (logical-reduce env* goal)))
      (LOG "P(~a)  goal updated!\n new goal: ~a\n\n"
           DEPTH goal*)
      (define remaining-props (append new-compound-props compound-props))
      (cond
        [(Top? goal*) #t]
        [else
         ;; our Γ now has all the atomic facts fully updated in it and the goal has been
         ;; simplified w/ this knowledge. Start reasoning about the complex 
         ;; propositions (e.g. and/or), newly exposed propositions, etc...
         ;; to see if we can prove the goal
         (LOG "P(~a) remaining props: ~a\n goal: ~a\n\n"
              DEPTH remaining-props goal*)
         (full-proves env* remaining-props goal*)])))

  (LOG "P(~a)  END! --> ~a\n\n"
       DEPTH v)
  (LOG! (RISE!))
  v)

;;returns a list of the remaining goals to be proved
;; only proves based on type-env lookups
;; A env obj goal -> filter w/ proven facts removed
(define/cond-contract (logical-reduce Γ goal)
  (c:-> env? Filter/c
        (listof Filter/c))
  (match goal
  
    [(Bot:) (list goal)]
    
    [(Top:) null]

    ;; distribute implicit conjuction in goal 
    [(TypeFilter: (? Refine? r) o)
     (match-define (Refine/obj: o t p) r)
     (define goal* (apply -and (append (logical-reduce Γ (-is-type o t))
                                       (logical-reduce Γ p))))
     (logical-reduce Γ goal*)]
    ;; distribute negation w/ DeMorgan's law
    [(NotTypeFilter: (? Refine? r) o)
     (match-define (Refine/obj: o t p) r)
     (define goal* (-or (-is-not-type o t) (invert-filter p)))
     (logical-reduce Γ goal*)]
    
    [(or (? TypeFilter?) (? NotTypeFilter?))
     (if (witnesses Γ goal)
         null
         (list goal))]
    
    [(? SLI? s)
     (if (SLIs-imply? (env-SLIs Γ) s)
         null
         (list s))]
    
    [(AndFilter: fs)
     (let loop ([fs fs])
       (match fs
         [(list) fs]
         [(cons f rst)
          (match (logical-reduce Γ f)
            [(list) (loop rst)]
            [fs* (append fs* (loop rst))])]))]
    
    [(OrFilter: fs)
     (let* ([fs* (map (λ (f) (apply -and (logical-reduce Γ f))) fs)]
            [f* (apply -or fs*)])
       (if (Top? f*)
           null
           (list f*)))]
    [_ (int-err "invalid goal: ~a" goal)]))

(define (atomic-prop? p)
         (or (Bot? p) (Top? p) (TypeFilter? p) (NotTypeFilter? p)))

(define/cond-contract (full-proves Γ assumptions goal)
  (c:-> env? (listof Filter/c) Filter/c
        boolean?)
  (match assumptions
    ['() (null? (logical-reduce Γ goal))]
    [(cons p rst)
     (match p
       [(TypeFilter: (? Refine? r) o)
        (match-let ([(Refine/obj: o t p) r])
          (full-proves Γ (list* (-is-type o t) p rst) goal))]
       [(NotTypeFilter: (? Refine? r) o)
        (match-define (Refine/obj: o t p) r)
        (full-proves Γ (cons (-or (-is-not-type o t) (invert-filter p))
                             rst)
                     goal)]
       [(? atomic-prop?)
        (define-values (Γ* new-props) (update-env/atom Γ p (λ () #f)))
        (define goal* (and Γ* (apply -and (logical-reduce Γ* goal))))
        (or (not Γ*)
            (full-proves Γ* (append new-props rst) goal*))]
       
       [(? SLI? s)
        (define slis* (add-SLI s (env-SLIs Γ)))
        (define Γ* (if (Bot? slis*) #f (replace-props Γ (append (env-props Γ) slis*))))
        (define goal* (and Γ* (apply -and (logical-reduce Γ* goal))))
        (or (not Γ*)
            (full-proves Γ* rst goal*))]
       
       [(AndFilter: fs) (full-proves Γ (append fs rst) goal)]
       
       [(OrFilter: fs)
        (andmap (λ (f) (full-proves Γ (cons f rst) goal)) fs)]
       [_ (int-err "invalid prop in assumptions: ~a" p)])]
    [_ (int-err "invalid assumption list: ~a" assumptions)]))

;; TODO(AMK) usage of ¬Type properties is still not complete

(define/cond-contract (witnesses env goal)
  (c:-> env? (or/c TypeFilter? NotTypeFilter?)
        any/c)
  (match goal
    [(TypeFilter: ft (and o (Path: π (? identifier? x))))
     (let* ([ty (lookup-id-type x env #:fail (λ (_) #f))]
            [x-obj-ty (and ty (id-ty+path->obj-ty ty π))])
       (and x-obj-ty
            (not (Error? x-obj-ty))
            (with-lexical-env
             (env-erase-type+ env x)
             (subtype x-obj-ty ft #:obj o))))]
    
    [(NotTypeFilter: ft (and o (Path: π (? identifier? x))))
     (let* ([x-ty+ (lookup-id-type x env #:fail (λ (_) #f))]
            [x-obj-ty+ (and x-ty+ (id-ty+path->obj-ty x-ty+  π))]
            [x-ty- (lookup-id-not-type x env #:fail (λ (_) #f))]
            [x-obj-ty- (and x-ty- (id-ty+path->obj-ty x-ty- π))])
       (with-lexical-env
        (env-erase-type+ env x)
        (or (and x-obj-ty-
                 (not (Error? x-obj-ty-))
                 (subtype ft x-obj-ty- #:obj o))
            (and x-obj-ty+
                 (not (Error? x-obj-ty+))
                 (not (overlap x-obj-ty+ ft))))))]
    
    ;;TODO(amk) These should take into account the ranges
    ;; implied by the integer numeric-type when possible
    [(TypeFilter: ft (? LExp? l))
     (subtype ft (integer-type) #:env env #:obj l)]
    [(NotTypeFilter: ft (? LExp? l))
     (with-lexical-env
      env
      (not (overlap (integer-type) ft)))]
    [_ (int-err "invalid witnesses goal ~a" goal)]))



;; remove from the negative type info types that are impossible
;; based on the current positive facts in the environment
(define/cond-contract (update-negative-type ty+ ty-)
  (c:-> Type? Type? Type?)
  (match ty-
    [(Union: ts)
     (apply Un (filter (curry overlap ty+) ts))]
    [else (if (overlap ty+ ty-)
              ty-
              -Nothing)]))

(define (update-env/obj-type env o t contra-env)
  (update-env/type+ env t o contra-env))

#|
(Type/c ;; old type
   Type/c ;; new type
   boolean? ;; #t if positive fact, #f if negative
   (listof PathElem?) ;; path down which to update
   (c:-> Type/c Type/c boolean?) ;; should we notify?
   (c:-> Type/c Type/c (listof PathElem?) Type/c) ;; notification function
   . c:-> . Type/c)
|#

(define/cond-contract (make-positive-notifier x new-props-box env)
  (c:-> identifier? (box/c (listof Filter?)) env?
        (c:-> Type/c Type/c (or/c #f (listof PathElem?))
              Type/c))
  (λ (old-t new-t path-stack)
    (cond
      ;; we're in a context where we shouldn't assume things (e.g. nested in a union type)
      [(not path-stack) new-t]
      ;; we are now a more specific int type w/ bounds -- go ahead and add the bounds!
      [(bounded-int-type? new-t)
       (define-values (new-low new-high) (int-type-bounds new-t))
       (define obj (make-Path (reverse path-stack) x))
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
       (define obj (make-Path (reverse path-stack) x))
       (define-values (t* nested-props) (extract-props-from-type obj new-t))
       (when (not (null? nested-props))
         (set-box! new-props-box (append nested-props (unbox new-props-box))))
       ((make-positive-notifier x new-props-box env) new-t t* path-stack)]
      [else
       (match new-t
         ;; if we're now a refinement, assume the refining proposition and just return
         ;; the refined type (recursively, of course)
         [(Refine-unsafe: t p)
          (define obj (make-Path (reverse path-stack) x))
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
    [(Path: π (? identifier? x))
     (define notify (make-positive-notifier x new-props-box env))
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
     (define x-ty- (lookup-id-not-type x env #:fail (const #f)))
     (LOG "update-env/type+: x-ty-: ~a\n" x-ty-)
     (define-values (new-x-ty+ new-x-ty-)
       (cond
         [(not x-ty+) (values (obj-ty+path->id-ty new-o-ty π -Any) (or x-ty- -Nothing))]
         [(not x-ty-)
          (with-lexical-env
           (env-erase-type+ env x)
           (values (update-type x-ty+ new-o-ty #t π notify)
                   -Nothing))]
         [else
          (with-lexical-env
           (env-erase-type+ env x)
           (let ([new-x-ty+ (update-type (update-type x-ty+ new-o-ty #t π notify) x-ty- #f null notify)])
             (values new-x-ty+
                     (update-negative-type new-x-ty+ x-ty-))))]))
     (LOG "update-env/type+: new-x-ty+: ~a\n" new-x-ty+)
     (LOG "update-env/type+: new-x-ty-: ~a\n" new-x-ty-)
     
     (cond
       [(Nothing? new-x-ty+)
        (values (contra-env) '())]
       [(type-equal? new-x-ty- -Any)
        (values (contra-env) '())]
       [else
        (define xobj (-id-path x))
        (match new-x-ty+
          [(Refine/obj: xobj r-t r-p)
           (values (naive-extend/not-type (env-erase-type+ env x) x new-x-ty-)
                   (list* (-is-type xobj r-t) r-p (unbox new-props-box)))]
          [_ (values (naive-extend/not-type (naive-extend/type env x new-x-ty+) x new-x-ty-)
                     (unbox new-props-box))])])]
    [(? LExp? olexp)
     (cond
       [(with-lexical-env env (not (overlap (integer-type) new-o-ty)))
        (values (contra-env) '())]
       [(bounded-int-type? new-o-ty)
        (define-values (new-low new-high) (int-type-bounds new-o-ty))
        (when new-low
          (set-box! new-props-box
                    (cons (-leqSLI (-lexp new-low) olexp)
                          (unbox new-props-box))))
        (when new-high
          (set-box! new-props-box (cons (-leqSLI olexp (-lexp new-high))
                                        (unbox new-props-box))))
        (values env (unbox new-props-box))]
       [else (values env '())])]
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
           (env-erase-type+ env x)
           (let ([new-x-ty+ (update-type (update-type x-ty+ new-o-ty #f π notify) x-ty- #f null notify)])
             (values new-x-ty+
                     (update-negative-type
                      new-x-ty+
                      (Un x-ty- (obj-ty+path->id-ty new-o-ty π -Nothing))))))]
         [x-ty+
          (values (update-type x-ty+ new-o-ty #f π notify)
                  (obj-ty+path->id-ty new-o-ty π -Nothing))]
         [x-ty-
          (values -Any
                  (Un x-ty- (obj-ty+path->id-ty new-o-ty π -Nothing)))]
         ;; (or x-ty- (obj-ty+path->id-ty new-o-ty π -Nothing))
         [else
          (values -Any (obj-ty+path->id-ty new-o-ty π -Nothing))]))
     
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
           (values (naive-extend/not-type (env-erase-type+ env x) x new-x-ty-)
                   (list* (-is-type xobj r-t) r-p (unbox new-props-box)))]
          [_ (values (naive-extend/not-type (naive-extend/type env x new-x-ty+) x new-x-ty-)
                     (unbox new-props-box))])])]
    [(? LExp?)
     ;; TODO(amk) maybe do something more complex here with LExp and SLI info?
     (if (subtype (integer-type) new-o-ty #:env env #:obj o)
         (values (contra-env) '())
         (values env (unbox new-props-box)))]
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

  (LOG "proves:update-env/atom(~a)\n env: ~a\n prop: ~a\n\n"
       DEPTH env prop)
  
  (define-values (env* new-props)
    (match prop
      [(? Top?) (values env '())]
      [(? Bot?) (values (contra-env) '())]
      [(TypeFilter: t o)
       (update-env/type+ env t o contra-env)]
      [(NotTypeFilter: t o)
       (update-env/type- env t o contra-env)]
      [_ (int-err "invalid update-env prop: ~a" prop)]))

  (LOG "proves:update-env/atom(~a)\n new env: ~a\n new props: ~a\n\n"
       DEPTH env* new-props)

  (values env* new-props))
