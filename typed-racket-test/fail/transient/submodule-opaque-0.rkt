#;
(exn-pred exn:fail:contract? #rx"transient-assert")

#lang typed/racket/shallow/base

(module u racket/base
  (define x* "not function")
  (provide x*))

(require/typed 'u
  (#:opaque X? x*))

