#;
(exn-pred #px"not a type constructor")
#lang typed/racket

;; Test that nullary type constructors require application
;; Using Nat2 without () should fail

(define-type (Nat2) Natural)
(ann 123 Nat2)  ; Should fail - Nat2 is a type constructor, not a type
