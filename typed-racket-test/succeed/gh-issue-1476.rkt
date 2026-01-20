#lang typed/racket

;; Test for GitHub Issue #1476: Make nullary type constructors require application

;; Test 1: Simple alias (no parens) - Nat can be used directly
(define-type Nat1 Natural)
(ann 123 Nat1)  ; Should work - Nat1 is a simple alias

;; Test 2: Nullary type constructor - must be applied
(define-type (Nat2) Natural)
(ann 123 (Nat2))  ; Should work - (Nat2) applies the type constructor

;; Test 3: Type constructor with parameters
(define-type (MyPair A B) (Pairof A B))
(ann (cons 1 "hello") (MyPair Integer String))
