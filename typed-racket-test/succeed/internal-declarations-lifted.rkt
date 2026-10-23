#lang typed/racket/base

;; Declarations in an internal-definition body are lifted to the start of
;; the body's expressions, so they must still be found when checking the
;; definitions that come before them in the expanded `let-values` chain.

(define (f [n : Fixnum]) : Integer
  (for/fold ([acc : Integer 0]) ([i (in-range n)])
    (define c (+ i 1))
    (: iters Nonnegative-Fixnum)
    (define iters (let loop ([k : Nonnegative-Fixnum 0])
                    (if (< k 3) (loop (+ k 1)) k)))
    (+ acc iters c)))

(define (g) : String
  (define x "hi")
  (: x T)
  (define-type T String)
  (define y : T x)
  y)

(define (h) : (Listof Integer)
  (define-type (Pair-Of A) (List A A))
  (: p (Pair-Of Integer))
  (define p (list 1 2))
  (let ()
    (: q (Pair-Of Integer))
    (define q p)
    q))

(unless (equal? (list (f 10) (g) (h)) (list 85 "hi" '(1 2)))
  (error 'internal-declarations-lifted "wrong result"))
