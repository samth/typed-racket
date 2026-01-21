#;
(exn-pred #rx"unit export must be an identifier")
#lang typed/racket

;; Issue #1305: invoke-unit and unit-from-context can trigger an internal
;; typechecker error when a macro expands to a non-identifier export.
;; Fixed by converting internal error to proper type error.

(define-signature a^ ([x : (Pairof Integer Integer)]))

(define-unit get-x@
  (import a^)
  (export)
  x)

(define v : (Pairof Integer Integer)
  (let ()
    (define-syntax (x stx)
      #'(quote not-an-integer))
    (invoke-unit get-x@ (import a^))))

(+ (car v) (cdr v))
