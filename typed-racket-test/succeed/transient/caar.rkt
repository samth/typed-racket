#lang typed/racket/shallow/base

;; Test that nested elimination forms get checked

(define (f)
  (car (car '((1)))))
