#lang racket/base
(require (except-in "../utils/utils.rkt" infer)
         racket/match racket/lazy-require 
         (except-in racket/contract ->* -> )
         (prefix-in c: (contract-req))
         (utils tc-utils)
         (env lexical-env lookup type-env-structs update)
         (logic prop-ops)
         (rep type-rep object-rep filter-rep rep-utils)
         (typecheck tc-metafunctions)
         (except-in "../types/abbrev.rkt" one-of/c)
         (for-syntax racket/base))

(lazy-require
 ("../types/remove-intersect.rkt" (overlap))
 ("../types/type-ref-path.rkt" (id-ty+path->obj-ty))
 ("../types/filter-ops.rkt" (-and -or invert-filter))
 ("../types/numeric-tower.rkt" (integer-type))
 ("../types/subtype.rkt" (subtype)))

(provide proves witnesses simple-proves) 

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
      ;; TODO duplicate from tc-envops??
      #;(define env* (env+props env #:ignore-non-identifier-ids? #f))
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
             (env-erase-id-type env x)
             (subtype x-obj-ty ft #:obj o))))]
    
    [(NotTypeFilter: ft (and o (Path: π (? identifier? x))))
     (let* ([x-ty+ (lookup-id-type x env #:fail (λ (_) #f))]
            [x-obj-ty+ (and x-ty+ (id-ty+path->obj-ty x-ty+  π))]
            [x-ty- (lookup-id-not-type x env #:fail (λ (_) #f))]
            [x-obj-ty- (and x-ty- (id-ty+path->obj-ty x-ty- π))])
       (with-lexical-env
        (env-erase-id-type env x)
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
