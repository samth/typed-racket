#lang racket/base

(require "../utils/utils.rkt"
         racket/match racket/lazy-require racket/keyword-transform
         racket/list racket/function
         (except-in racket/contract ->* -> )
         (env type-env-structs global-env mvar-env)
         (utils tc-utils)
         (rep type-rep object-rep rep-utils filter-rep object-ops)
         (only-in (rep type-rep) Type/c)
         (typecheck renamer)
         (prefix-in c: (contract-req))
         (except-in (types utils abbrev filter-ops) -> ->* one-of/c))


(lazy-require 
 ("../types/kw-types.rkt" (kw-convert))
 ("../types/numeric-tower.rkt" (integer-type))
 ("../types/type-ref-path.rkt" (id-ty+path->obj-ty))
 ("../typecheck/typechecker.rkt" (tc-literal)))

(provide lookup-id-type lookup-id-not-type lookup-obj-type lookup-obj-not-type resolve-id-alias)



(define/cond-contract (lookup-id-type id env #:fail [fail #f])
  (c:->* (identifier? env?) (#:fail (c:or/c #f (c:-> any/c (c:or/c Type/c #f))))
         (c:or/c Type/c #f))
  
  ;; resolve any alias, then lookup/calculate type
  (define type
    (match (resolve-id-alias env id)
      [#f (env-struct-lookup env id #:fail (const  #f))]
      [(or (? Path? o) (? LExp? o))
         (lookup-obj-type o env #:fail (const #f))]
      [unknown (int-err "unrecognized alias obj ~a" unknown)]))
  
  (cond
    [type]
    [fail (fail id)]
    [else (lookup-fail id)]))

(define/cond-contract (lookup-id-not-type id env #:fail [fail #f])
  (c:->* (identifier? env?) (#:fail (c:or/c #f (c:-> any/c (c:or/c Type/c #f))))
         (c:or/c Type/c #f))
  ;; resolve any alias, lookup/calculate type
  (define type
    (match (resolve-id-alias env id)
      [#f (raw-lookup-id-not-type env id (const #f))]
      [o #:when (or (Path? o) (LExp? o))
         (lookup-obj-not-type o env (const #f))]
      [unknown (int-err "unrecognized alias obj ~a" unknown)]))
  
  (cond
    [type]
    [fail (fail id)]
    [else (lookup-fail id)]))

(define/cond-contract (lookup-obj-type o env #:fail [fail #f])
  (c:->* (non-empty-obj? env?) (#:fail (c:or/c #f procedure?))
         (c:or/c Type/c #f))
  (match o
    [(Path: π (? identifier? x)) 
     (let* ([ty (lookup-id-type x env #:fail (const #f))]
            [o-ty (and ty (id-ty+path->obj-ty ty π))])
       (cond 
         [(not (Error? o-ty)) o-ty]
         [fail (fail o)]
         [else (lookup-fail o)]))]
    ;; TODO(amk) maybe something else here more specific
    ;; for what LExp it is? I dunno
    [(? LExp? l)
       (cond
         [(lookup-lexp-type env l (const #f)) 
          => (λ (t) (-unsafe-refine t (-eqSLI l (-lexp (-id-path (-arg-path 0 0))))))]
         [(constant-LExp? l)
          => (λ (c) (-unsafe-refine (tc-literal (datum->syntax #f c))
                                    (-eqSLI l (-lexp (-id-path (-arg-path 0 0))))))]
         [else
          (-refine x (integer-type)
                   (apply -and (leqs->SLIs (list (leq l (-lexp (-id-path x)))
                                                 (leq (-lexp (-id-path x)) l)))))])]
    [_ #:when fail (fail o)]
    [_ (lookup-fail o)]))

(define/cond-contract (lookup-obj-not-type o env #:fail [fail #f])
  (c:->* (Object? env?) (#:fail (c:or/c #f (c:-> any/c (c:or/c Type/c #f))))
         (c:or/c Type/c #f))
  
  (define type
    (match o
      [(Path: π (? identifier? x))
       (let ([ty (lookup-id-not-type x env #:fail (const #f))])
         (and ty (id-ty+path->obj-ty ty π)))]
      ;; currently don't store LExp negative type info...
      [(? LExp?) #f]))
  (cond 
    [(and (not (Error? type))
          type)
     type]
    [fail (fail o)]
    [else #f]))

(define/cond-contract (resolve-id-alias env id [fail (const #f)])
  (c:->* (env? identifier?)
         ((c:-> identifier? (or/c non-empty-obj? #f)))
        (or/c non-empty-obj? #f))
  (raw-lookup-alias env id fail))


(define/cond-contract (env-struct-lookup env i #:fail [fail #f])
  (c:->* (env? identifier?) (#:fail (c:or/c #f (c:-> any/c (c:or/c Type/c #f))))
       (c:or/c Type/c #f))
  (raw-lookup-id-type env i (λ (i)
                              (lookup-type
                               i
                               (λ ()
                                 (cond 
                                   [(syntax-property i 'constructor-for)
                                    => (λ (prop)
                                         (define orig (un-rename prop))
                                         (define t (env-struct-lookup env orig))
                                         (register-type i t)
                                         t)]
                                   [(syntax-procedure-alias-property i) 
                                    => (λ (prop)
                                         (define orig (car (flatten prop)))
                                         (define t (env-struct-lookup env orig))
                                         (register-type i t)
                                         t)]
                                   [(syntax-procedure-converted-arguments-property i)
                                    => (λ (prop)
                                         (define orig (car (flatten prop)))
                                         (define pre-t
                                           (env-struct-lookup 
                                            env orig #:fail (lambda (i) (lookup-fail i) #f)))
                                         (define t (if pre-t
                                                       (kw-convert pre-t #f)
                                                       Err))
                                         (register-type i t)
                                         t)]
                                   [else ((or fail lookup-fail) i)]))))))


;(trace lookup-id-type)
;(trace lookup-id-not-type)
;(trace lookup-obj-type)
;(trace lookup-obj-not-type)
;(trace resolve-id-alias)
