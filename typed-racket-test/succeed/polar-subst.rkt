#lang typed/racket

;; Companion to fail/subst-empty-obj-negative-prop.rkt and
;; fail/erase-id-negative-prop.rkt: polarity-aware erasure of the empty
;; object must not reject these sound uses of latent props.

;; a latent prop about a variable that stays in scope: nothing is
;; erased, and the argument genuinely establishes (Number @ x)
(define (f0 [x : Any]) : Number
  ((lambda ([f : (Any -> Boolean : #:+ (Number @ x))])
     (if (f x) (add1 x) 1))
   (lambda ([w : Any]) (number? x))))

;; positive erasure: props about an erased argument in result position
;; weaken to Top and the application still typechecks
(define (f1) : Boolean
  ((lambda ([y : Any]) (number? y)) "hello"))

;; the same, through let
(define f2
  (let ([x (ann 5 Any)])
    (lambda () (number? x))))

(f0 1)
(f1)
(f2)
