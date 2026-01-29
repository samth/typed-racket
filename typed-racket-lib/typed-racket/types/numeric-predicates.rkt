#lang racket/base

(require racket/unsafe/ops
         (submod racket/performance-hint begin-encourage-inline))

(provide index? exact-rational?)

;; this is required for template in numeric-tower.rkt

(begin-encourage-inline

;; Indexes are in the range [0, 2^28), which is portable across all
;; platforms Racket supports (32-bit and 64-bit).
;; NOTE: We cannot use (fixnum? (* x 4)) to check this because on Racket BC,
;; generic multiplication may not return a fixnum even when the result fits.
(define (index? x) (and (fixnum? x) (unsafe-fx>= x 0) (unsafe-fx< x 268435456)))

(define (exact-rational? x) (and (rational? x) (exact? x)))

) ; begin-encourage-inline
