#lang racket/base

(require "../utils/utils.rkt" syntax/parse racket/match
         (contract-req)
         (env lexical-env)
         (private type-annotation)
         (rep type-rep rep-utils)
         (types numeric-tower)
         (for-label racket/base racket/unsafe/ops typed/safe/ops))

(provide/cond-contract [find-annotation ((syntax? identifier? #:try-vec-nat? boolean?)
                                         . ->* . (or/c #f Type/c 'vec))])

(define-syntax-class lv-clause
  #:transparent
  (pattern [(v:id ...) e:expr]))

(define-syntax-class lv-clauses
  #:transparent
  (pattern (cl:lv-clause ...)
           #:with (e ...) #'(cl.e ...)
           #:with (vs ...) #'((cl.v ...) ...)))

(define-syntax-class core-expr
  #:literal-sets (kernel-literals)
  #:transparent
  (pattern (let-values cls:lv-clauses body)
           #:with (expr ...) #'(cls.e ... body))
  (pattern (letrec-values cls:lv-clauses body)
           #:with (expr ...) #'(cls.e ... body))
  (pattern (letrec-syntaxes+values _ cls:lv-clauses body)
           #:with (expr ...) #'(cls.e ... body))
  (pattern (#%plain-app expr ...))
  (pattern (if expr ...))
  (pattern (with-continuation-mark expr ...))
  (pattern (begin expr ...))
  (pattern (begin0 expr ...))
  (pattern (#%plain-lambda _ e)
           #:with (expr ...) #'(e))
  (pattern (case-lambda [_ expr] ...))
  (pattern (set! _ e)
           #:with (expr ...) #'(e))
  (pattern _
           #:with (expr ...) #'()))

(define-literal-set find-annotation-literals #:for-label
    (reverse vector-ref unsafe-vector-ref safe-vector-ref vector-set! unsafe-vector-set! safe-vector-set!))

(define (unrefine t)
  (and t
       (let loop ([t t])
         (match t
           [(Refine-type: t) (loop t)]
           [_ t]))))

;; expr id -> type or #f
;; if there is a binding in stx of the form:
;; (let ([x (reverse name)]) e) or
;; (let ([x name]) e)
;; where x has a type annotation, return that annotation, otherwise #f
(define (find-annotation stx name #:try-vec-nat? try-vec-nat?)
  (define t (find-annotation* stx name try-vec-nat?))
  (cond
    [try-vec-nat? t]
    [else (and (Type? t) t)]))
(define (find-annotation* stx name try-vec-nat?)
  (define (find s) (find-annotation* s name try-vec-nat?))
  (define ((match? body) b)
    (syntax-parse b
      #:literal-sets (kernel-literals find-annotation-literals)
      [c:lv-clause
       #:with n:id #'c.e
       #:with (v) #'(c.v ...)
       #:fail-unless (free-identifier=? name #'n) #f
       (unrefine (or (type-annotation #'v)
                     (lookup-type/lexical #'v #:fail (lambda _ #f))
                     (and try-vec-nat?
                          (let ([t (find-annotation* body #'v try-vec-nat?)])
                            (and t (eq? 'vec t) 'vec)))))]
      [c:lv-clause
       #:with (#%plain-app reverse n:id) #'c.e
       #:with (v) #'(c.v ...)
       #:fail-unless (free-identifier=? name #'n) #f
       (unrefine (or (type-annotation #'v) (lookup-type/lexical #'v #:fail (lambda _ #f))))]
      [c:lv-clause
       #:with rhs:expr #'c.e
       #:with (v) #'(c.v ...)
       #:fail-unless try-vec-nat? #f
       (let ([t (unrefine (find #'rhs))])
         (and t (eq? 'vec t) 'vec))]
      [_ #f]))
  (syntax-parse stx
    #:literal-sets (kernel-literals find-annotation-literals)
    [(let-values cls:lv-clauses body)
     (or (ormap (match? #'body) (syntax->list #'cls))
         (find #'body))]
    [(#%plain-app (~or vector-ref unsafe-vector-ref safe-vector-ref) _ n:id)
     #:when (and try-vec-nat? (free-identifier=? name #'n))
     'vec]
    [(#%plain-app (~or vector-set! unsafe-vector-set! safe-vector-set!) _ n:id _)
     #:when (and try-vec-nat? (free-identifier=? name #'n))
     'vec]
    [e:core-expr
     (ormap find (syntax->list #'(e.expr ...)))]))
