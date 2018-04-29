#;
(exn-pred exn:fail:contract? #rx"transient-assert")

#lang typed/racket/shallow/base

(module u racket/base
  (define x* "OOPS")
  (provide x*))

(require/typed 'u
  (x* (Listof Integer)))

