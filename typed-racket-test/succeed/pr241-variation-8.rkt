#lang racket/base

;; Compiled expressions are dangerous!

(module u racket/base
  (define (foo? x)
    (define-values (ctr incr) (eval x))
    (error 'pr241 "Danger: compiled expression allowed as 'Any'")
    (set-box! ctr 'haha)
    (displayln (incr))
    #t)
  (provide foo?))

(module t typed/racket/base
  (require/typed (submod ".." u)
    [#:opaque T foo?])
  (define compiled-counter
    (compile-syntax
      #'(let*: ([b : (Boxof Integer) (box 0)]
                [incr : (-> Void) (lambda () (set-box! b (add1 (unbox b))))])
          (values b incr))))
  (with-handlers ([exn:fail:contract? (lambda (e) (void))])
    (foo? compiled-counter)))

(require 't)
