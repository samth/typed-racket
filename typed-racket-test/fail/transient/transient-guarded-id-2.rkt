#;
(exn-pred exn:fail:syntax? #rx"required a flat contract")

#lang typed/racket/deep/base

;; cannot send syntax transient -> guarded,
;; (see succeed/transient/pass for tests 0 and 1)

(module transient typed/racket/shallow/base
  (provide xxx)
  (: xxx (Syntaxof Any))
  (define xxx
    #`#,(vector 0)))

(require 'transient)
xxx

