#;
(exn-pred exn:fail:contract? #rx"transient-assert")

#lang typed/racket/base/shallow

(module u racket/base
  (define x* (list "OOPS"))
  (provide x*))

(require/typed 'u
  (x* (Listof Integer)))

(+ (car x*) 1)
