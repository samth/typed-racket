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
 ("../types/type-ref-path.rkt" (type-ref/path type-unref/path))
 ("../types/filter-ops.rkt" (-and -or))
 ("../types/numeric-tower.rkt" (integer-type int-type-bounds bounded-int-type?)) 
 ("type-update.rkt" (update-type))
 ("../types/subtype.rkt" (subtype))
 ("../types/union.rkt" (Un)))

(provide proves witnesses update-env/atom simple-proves update-env/obj-type)

(define Bottom (Un))

(define (simple-proves axioms goal)
  (proves null empty-env axioms goal))

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

(define/cond-contract (proves A env new-props goal)
  (c:-> any/c env? (listof Filter/c) Filter/c
        any/c)
  (LOG! (DIVE!))

  #;(LOG "proves(~a) START!\n A: ~a\n env: ~a\n new-props: ~a\n goal: ~a\n\n"
       DEPTH A env new-props goal)
  
  (define v
    (let/ec exit*
      (define (exit) (exit* A))
      ;; combine the new props w/ the props already in the environment
      (define-values (compound-props atoms slis)
        (combine-props (apply append (map flatten-nested-props new-props)) 
                       (env-props+SLIs env)
                       exit))

      #;(LOG "proves(~a) combined props!\n compound-props: ~a\n atoms: ~a\n slis: ~a\n\n"
           DEPTH compound-props atoms slis)
      
      ;; update the environment based on all the known atoms
      (define-values (env* new-exposed-props)
        (for/fold ([Γ (replace-props env slis)]
                   [new-props '()]) 
                  ([f (in-list atoms)])
          (match f
            [(or (? TypeFilter?) (? NotTypeFilter?))
             (LOG "proves(~a) update-env/atom ...\n env: ~a\n f: ~a\n\n"
            DEPTH env f)
             (define-values (Γ* new-ps) (update-env/atom A Γ f exit))
             (LOG "proves(~a) update-env/atom done!\n new-env: ~a\n new-props: ~a\n\n"
                     DEPTH Γ* new-ps)
             (values Γ* (append new-ps new-props))]
            ;; [(SLI? sli) ] TODO(AMK) slis update types!
            [_ (values Γ new-props)])))

      #;(LOG "proves(~a) goal updating...\n goal: ~a\n\n"
           DEPTH goal)
      (define goal* (apply -and (logical-reduce A env* goal)))
      #;(LOG "proves(~a) goal updated!\n new goal: ~a\n\n"
           DEPTH goal*)
      (define remaining-props (append new-exposed-props compound-props))
      (cond
        [(Top? goal*) A]
        [else
         ;; our Γ now has all the atomic facts fully updated in it and the goal has been
         ;; simplified w/ this knowledge. Start reasoning about the complex 
         ;; propositions (e.g. and/or), newly exposed propositions, etc...
         ;; to see if we can prove the goal
         #;(LOG "proves(~a) working with remaining props and goal!\n remaining props: ~a\n goal: ~a\n\n"
              DEPTH remaining-props goal*)
         (and (full-proves A env* remaining-props goal*) A)])))

  #;(LOG "proves(~a) END! ~a\n\n"
       DEPTH (and v #t))
  (LOG! (RISE!))
  v)

;;returns a list of the remaining goals to be proved
;; only proves based on type-env lookups
;; A env obj goal -> filter w/ proven facts removed
(define/cond-contract (logical-reduce A env goal)
  (c:-> any/c env? Filter/c
        (listof Filter/c))
  (match goal
  
    [(Bot:) (list goal)]
    
    [(Top:) null]
    
    [(or (? TypeFilter?) (? NotTypeFilter?))
     #;(LOG "proves:logical-reduce(~a) will env witness atomic goal?\n env: ~a\n goal: ~a\n\n"
          DEPTH env goal)
     (define v
       (if (witnesses A env goal)
           null
           (list goal)))
     #;(LOG "proves:logical-reduce(~a) witness atomic goal: ~a\n\n"
          DEPTH (null? v))
     v]
    
    [(? SLI? s)
     (if (SLIs-imply? (env-SLIs env) s)
         null
         (list goal))]
    
    [(AndFilter: fs)
     (let* ([fs* (apply append (map (curry logical-reduce A env) fs))]
            [f* (apply -and fs*)])
       (if (Top? f*)
           (list)
           (list f*)))]
    
    [(OrFilter: fs)
     (let* ([fs* (map (λ (f) (apply -and (logical-reduce A env f))) fs)]
            [f* (apply -or fs*)])
       (if (Top? f*)
           null
           (list f*)))]
    [_ (int-err "invalid goal: ~a" goal)]))

(define (atomic-prop? p)
         (or (Bot? p) (Top? p) (TypeFilter? p) (NotTypeFilter? p)))

(define/cond-contract (full-proves A env assumptions goal)
  (c:-> any/c env? (listof Filter/c) Filter/c
        boolean?)
  (match assumptions
    ['() (null? (logical-reduce A env goal))]
    [(cons p ps)
     (match p
       [(? atomic-prop?)
        (define-values (env* new-props) (update-env/atom A env p (λ () #f)))
        (define goal* (and env* (apply -and (logical-reduce A env* goal))))
        (or (not env*)
            (full-proves A env* (append new-props ps) goal*))]
       
       [(? SLI? s)
        (define slis* (add-SLI s (env-SLIs env)))
        (define env* (if (Bot? slis*) #f (replace-props env (append (env-props env) slis*))))
        (define goal* (and env* (apply -and (logical-reduce A env* goal))))
        (or (not env*)
            (full-proves A env* ps goal*))]
       
       [(AndFilter: fs) (full-proves A env (append fs ps) goal)]
       
       ;; potential but unavoidable(?) performance ouch
       [(OrFilter: fs) (for/and ([f (in-list fs)]) 
                         (full-proves A env (cons f ps) goal))]
       [_ (int-err "invalid prop in assumptions: ~a" p)])]
    [_ (int-err "invalid assumption list: ~a" assumptions)]))

;; TODO(AMK) usage of ¬Type properties is still not complete

(define/cond-contract (witnesses A env goal)
  (c:-> any/c env? (or/c TypeFilter? NotTypeFilter?)
        any/c)
  (match goal
    [(TypeFilter: ft (and o (Path: π (? identifier? x))))
     (let ([ty (lookup-id-type x env #:fail (λ (_) Univ))])
       (subtype (type-ref/path ty π) ft #:A A #:env (env-erase-type+ env x) #:obj o))]
    
    [(NotTypeFilter: ft (and o (Path: π (? identifier? x))))
     (let ([x-ty+ (lookup-id-type x env #:fail (λ (_) Univ))]
           [x-ty- (lookup-id-not-type x env #:fail (λ (_) Bottom))]
           [goal-x-ty- (type-ref/path ft π)]
           [env* (env-erase-type+ env x)])
       (with-lexical-env
        env*
        (or (subtype goal-x-ty- x-ty- #:A A #:env env* #:obj o)
            (not (overlap x-ty+ goal-x-ty-)))))]
    
    ;;TODO(amk) These should take into account the ranges
    ;; implied by the integer numeric-type when possible
    [(TypeFilter: ft (? LExp? l))
     (subtype ft (integer-type) #:A A #:env env #:obj l)]
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
              Bottom)]))

(define (update-env/obj-type env o t contra-env)
  (update-env/type+ null env t o contra-env))

#|
(Type/c ;; old type
   Type/c ;; new type
   boolean? ;; #t if positive fact, #f if negative
   (listof PathElem?) ;; path down which to update
   (c:-> Type/c Type/c boolean?) ;; should we notify?
   (c:-> Type/c Type/c (listof PathElem?) Type/c) ;; notification function
   . c:-> . Type/c)
|#

(define/cond-contract (make-positive-notifier x new-props-box)
  (c:-> identifier? (box/c (listof Filter?))
        (c:-> Type/c Type/c (or/c #f (listof PathElem?))
              Type/c))
  (λ (old-t new-t path-stack)
    (cond
      ;; we're in a context where we shouldn't assume things (e.g. nested in a union type)
      [(not path-stack) new-t]
      ;; we are now a more specific int type w/ bounds -- go ahead and add the bounds!
      [(and (bounded-int-type? new-t)
            (not (type-equal? new-t old-t)))
       (define-values (old-low old-high) (int-type-bounds old-t))
       (define-values (new-low new-high) (int-type-bounds new-t))
       (define obj (make-Path (reverse path-stack) x))
       (when (and new-low (not (eqv? old-low new-low)))
         (set-box! new-props-box
                   (cons (-leqSLI (-lexp new-low) (-lexp (list 1 obj)))
                         (unbox new-props-box))))
       (when (and new-high (not (eqv? old-high new-high)))
         (set-box! new-props-box (cons (-leqSLI (-lexp (list 1 obj)) (-lexp new-high))
                                       (unbox new-props-box))))
       new-t]
      ;; we used to be a union and now we're not --- check if there are props
      ;; nested inside the union we can now assume to be true!
      [(and (Union? old-t) (not (Union? new-t)))
       (define obj (make-Path (reverse path-stack) x))
       (define-values (t* nested-props) (extract-props-from-type obj new-t))
       (when (not (null? nested-props))
         (set-box! new-props-box (append nested-props (unbox new-props-box))))
       ((make-positive-notifier x new-props-box) new-t t* path-stack)]
      [else
       (match new-t
         ;; if we're now a refinement, assume the refining proposition and just return
         ;; the refined type (recursively, of course)
         [(Refine-unsafe: t p)
          (define obj (make-Path (reverse path-stack) x))
          (define prop (subst-filter p (list 0 0) obj #t))
          (when (not (Top? p))
            (set-box! new-props-box (cons p (unbox new-props-box))))
          ((make-positive-notifier x new-props-box) old-t t path-stack)]
         [_ new-t])])))

(define ((make-negative-notifier x new-props-box) old-t new-t path-stack)
  new-t)

(define/cond-contract (update-env/type+ A env t o contra-env)
  (c:-> any/c env? Type? Object? procedure?
        (values (c:or/c env? #f) ;; updated environment
                (c:listof Filter?))) ;; new derived filters
  (LOG "update-env/type+ of ~a with ~a\n" o t)
  (define new-props-box (box '()))
  (match o
    [(Path: π (? identifier? x))
     (define notify+ (make-positive-notifier x new-props-box))
     (define notify- (make-negative-notifier x new-props-box))
     (define x-ty+ (lookup-id-type x env #:fail (λ (_) Univ)))
     (LOG "update-env/type+ x-ty+: ~a\n" x-ty+)
     (define x-ty- (lookup-id-not-type x env #:fail (λ (_) Bottom)))
     (LOG "update-env/type+ x-ty-: ~a\n" x-ty-)
     (define new-x-ty+
       (with-lexical-env env (update-type (update-type x-ty+ t #t π notify+) x-ty- #f π notify-)))
     (LOG "update-env/type+ new-x-ty+: ~a\n" new-x-ty+)
     (define new-x-ty-
       (with-lexical-env env (update-negative-type new-x-ty+ x-ty-)))
     (LOG "update-env/type+ new-x-ty-: ~a\n" new-x-ty-)
     
     (cond
       [(Bottom? new-x-ty+)
        (values (contra-env) '())]
       [(type-equal? new-x-ty- Univ)
        (values (contra-env) '())]
       [else
        (define xobj (-id-path x))
        (match new-x-ty+
          [(Refine-unsafe: r-t r-p)
           (values (naive-extend/not-type (env-erase-type+ env x) x new-x-ty-)
                   (list (-filter r-t xobj) 
                         (subst-filter r-p (list 0 0) xobj #t)))]
          [_ (values (naive-extend/not-type (naive-extend/type env x new-x-ty+) x new-x-ty-)
                     '())])])]
    [(? LExp?)
     ;; TODO(amk) maybe do something more complex here with LExp and SLI info?
     (if (with-lexical-env env (not (overlap (integer-type) t)))
         (values (contra-env) '())
         (values env '()))]
    [_ (int-err "invalid object for updating the environment! ~a" o)]))

(define/cond-contract (update-env/type- A env t o contra-env)
  (c:-> any/c env? Type? Object? (c:or/c #f procedure?)
        (values (c:or/c env? #f) (c:listof Filter?)))
  (define new-props-box (box '()))
  (match o
    [(Path: π (? identifier? x))
     (define notify+ (make-positive-notifier x new-props-box))
     (define notify- (make-negative-notifier x new-props-box))
     
     (define x-ty+ (lookup-id-type x env #:fail (λ (_) Univ))) ;; x is of type T
     (define new-x-ty+
       (with-lexical-env env (update-type x-ty+ t #f π notify+))) ;; combine new type-, x is now of type T'
     (define x-ty- (lookup-id-not-type x env #:fail (λ (_) Bottom))) ;; env says x is not of type T-
     (define new-x-ty-
       (with-lexical-env env (update-negative-type new-x-ty+
                                                   (Un x-ty- (type-unref/path t π Bottom)))))
     (cond
       [(Bottom? new-x-ty+)
        (values (contra-env) '())]
       [(type-equal? new-x-ty- Univ)
        (values (contra-env) '())]
       [else
        (define xobj (-id-path x))
        (match new-x-ty+
          [(Refine-unsafe: r-t r-p)
           (values (naive-extend/not-type (env-erase-type+ env x) x new-x-ty-)
                   (list (-filter r-t xobj) 
                         (subst-filter r-p (list 0 0) xobj #t)))]
          [_ (values (naive-extend/not-type (naive-extend/type env x new-x-ty+) x new-x-ty-)
                     '())])])]
    [(? LExp?)
     ;; TODO(amk) maybe do something more complex here with LExp and SLI info?
     (if (subtype (integer-type) t #:A A #:env env #:obj o)
         (contra-env)
         env)]
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
(define/cond-contract (update-env/atom A env prop [contra-env (λ _ #f)])
  (c:-> any/c env? atomic-prop? procedure?
        (values (c:or/c env? #f) (c:listof Filter?)))

  (LOG "proves:update-env/atom(~a)\n A: ~a\n env: ~a\n prop: ~a\n\n"
       DEPTH A env prop)
  
  (define-values (env* new-props)
    (match prop
      [(? Top?) (values env '())]
      [(? Bot?) (values (contra-env) '())]
      [(TypeFilter: t o)
       (update-env/type+ A env t o contra-env)]
      [(NotTypeFilter: t o)
       (update-env/type- A env t o contra-env)]
      [_ (int-err "invalid update-env prop: ~a" prop)]))

  (LOG "proves:update-env/atom(~a)\n new env: ~a\n new props: ~a\n\n"
       DEPTH env* new-props)

  (values env* new-props))
