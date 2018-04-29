#;
(exn-pred exn:fail:syntax? #rx"required a flat contract")

#lang typed/racket/deep/base

;; cannot send syntax to guarded

(module optional typed/racket/optional/base
  (provide xxx)
  (: xxx (Syntaxof Any))
  (define xxx
    #`#,(vector 0)))

(require 'optional)
xxx

