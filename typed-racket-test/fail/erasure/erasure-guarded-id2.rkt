#;
(exn-pred exn:fail:syntax? #rx"required a flat contract")

#lang typed/base/racket/deep

;; cannot send syntax to guarded

(module optional typed/base/racket/optional
  (provide xxx)
  (: xxx (Syntaxof Any))
  (define xxx
    #`#,(vector 0)))

(require 'optional)
xxx

