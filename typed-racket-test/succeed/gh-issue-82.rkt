#lang typed/racket

;; Issue #82: Previously caused internal error "Tried to move vars to
;; dbound that already exists" when using plambda with dotted type
;; variables. Now type checks correctly.

(: f (-> One (List One String Char) : #:object (0 0)))
(define (f [x : One])
  (let ([f (plambda: (a ...) [w : a ... a] w)])
    (f x "hello" #\c)))
