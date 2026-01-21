#;#lang racket/base

;; Test that shows failure when s-immutable field is NOT in the type
;; This test should FAIL with a contract error

(module typed-color typed/racket
  (provide make-test-color)
  (require racket/class)

  ;; Color% type WITHOUT s-immutable field (this is the bug!)
  (define-type TestColor%
    (Class [is-immutable? (-> Boolean)]))

  (: test-color% TestColor%)
  (define test-color%
    (class object%
      (super-new)
      (field [s-immutable #f])  ;; Field exists but NOT in type!
      (define/public (is-immutable?) s-immutable)))

  (: make-test-color (-> (Instance TestColor%)))
  (define (make-test-color)
    (new test-color%)))

(module untyped-code racket
  (require racket/class)
  (provide access-s-immutable-field)

  ;; Tries to access s-immutable field from untyped code
  (define (access-s-immutable-field color-obj)
    (get-field s-immutable color-obj)))

(require 'typed-color 'untyped-code)

;; This should FAIL because s-immutable is not in the contract
(define c (make-test-color))
(access-s-immutable-field c)  ;; Should raise: "cannot read or write field hidden by Typed Racket"
