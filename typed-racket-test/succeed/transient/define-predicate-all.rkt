#lang typed/racket/shallow

(require typed/rackunit)

(define-predicate p? (All (A) (Listof A)))

(check-exn #rx"transient-assert" ;; car
  (lambda ()
    (: x (U (Listof Integer) Integer)) (define x '(1 2 3))
    (if (p? x) (car x) 0)))

