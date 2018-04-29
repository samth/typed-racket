#;
(exn-pred exn:fail:contract? #rx"transient-assert")

#lang typed/racket/shallow

;; Bad cast, expect transient-assert error

(cast 42 String)
