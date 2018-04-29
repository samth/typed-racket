#lang racket/base

;; #:opaque predicates may change the type of their arguments in transient

(module untyped racket/base
 (define (bad x)
   (set-box! x 5)
   #t)
 (provide bad))

(module typed typed/racket/shallow/base
 (require typed/rackunit)
 (require/typed (submod ".." untyped)
   [#:opaque T bad])
 (: b (Boxof String))
 (define b (box "hi"))
 (bad b)
 (check-exn exn:fail:contract? (lambda () (unbox b))))

(require 'typed)
