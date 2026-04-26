#lang racket/base
;; Tiny `raise-continuable`-style helper for the unsoundness demo of issue #1505.
;; This is the same trick R6RS rnrs/exceptions-6 uses internally: capture the
;; continuation of the raise-continuable call in a struct so the exception
;; handler can tail-call it with a value of its choosing.

(provide make-raise-continuable k-box? k-box-k)

(struct k-box (k) #:transparent)

(define (make-raise-continuable v)
  (let/cc cont
    (raise (k-box cont) #f)))   ; #f = no continuation barrier
