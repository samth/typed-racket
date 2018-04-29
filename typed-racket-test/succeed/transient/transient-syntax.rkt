#lang racket/base

(module a typed/racket/shallow/base
  (provide f)
  (define-syntax-rule (f x)
    (car (car x))))

(require 'a)
(f '((a) b c))
