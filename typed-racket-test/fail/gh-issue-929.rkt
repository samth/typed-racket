#;
(exn-pred #rx"Type Checker")
#lang typed/racket

;; Issue #929: Internal Typechecker Error: function->method: Error
;; The error occurs when using ->m (a contract form, not a type) in a method annotation
;; This should give a user-friendly error, not an internal error

(define state%
  (class object% (init-field (C : Number))
    (super-new)

    (: final? (->m Boolean))  ;; ->m is not a valid type, should error gracefully
    (define/public (final?)
      (number? C))))
