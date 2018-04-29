#lang typed/racket/optional

;; 2021-09-22: what should define-predicate do?

(require typed/rackunit)

(define-predicate p? (All (A) (Listof A)))

(check-not-exn
  (lambda ()
    (: x (U (Listof Integer) Integer)) (define x '(1 2 3))
    (if (p? x) (car x) 0)))

