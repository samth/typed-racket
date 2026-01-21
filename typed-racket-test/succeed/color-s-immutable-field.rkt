#lang racket/base

;; Test that Color% type includes s-immutable field so that
;; untyped code (like color->immutable-color) can access it

(module typed-color typed/racket
  (provide make-test-color)
  (require racket/class)

  ;; Minimal Color% type WITH s-immutable field
  (define-type TestColor%
    (Class (field [s-immutable Boolean])
           [is-immutable? (-> Boolean)]))

  (: test-color% TestColor%)
  (define test-color%
    (class object%
      (super-new)
      (field [s-immutable #f])
      (define/public (is-immutable?) s-immutable)))

  (: make-test-color (-> (Instance TestColor%)))
  (define (make-test-color)
    (new test-color%)))

(module untyped-code racket
  (require racket/class)
  (provide access-s-immutable-field)

  ;; This simulates what color-is-immutable? does in racket/draw/private/color.rkt
  ;; It accesses the s-immutable field directly from untyped code
  (define (access-s-immutable-field color-obj)
    (get-field s-immutable color-obj)))

(require 'typed-color 'untyped-code)

;; This should succeed because s-immutable is in the TestColor% type
(define c (make-test-color))
(define result (access-s-immutable-field c))

(unless (boolean? result)
  (error 'test "Expected boolean from s-immutable field, got: ~a" result))

(printf "Test passed: s-immutable field accessible from untyped code\n")
