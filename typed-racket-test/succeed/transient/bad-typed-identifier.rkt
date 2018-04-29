#lang typed/racket/shallow/base

(module bad racket/base
  (provide bad)
  (define (bad x) 'xxx))

(require/typed 'bad
  (bad (-> Any String)))

(define f (vector bad))
(define g (vector-ref f 0)) ;; g is typed id, but cannot trust type

(require typed/rackunit)
(check-exn #rx"transient-assert"
  (lambda () (string-append (g 0) "xxx")))
