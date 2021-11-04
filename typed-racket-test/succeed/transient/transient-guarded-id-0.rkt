#lang typed/racket/base

;; basic transient -> guarded, is ok

(module transient typed/racket/base/shallow
  (provide xxx)
  (define xxx '$$$)
  xxx)

(require 'transient)
xxx

(define (f y)
  xxx)

