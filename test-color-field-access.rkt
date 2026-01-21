#lang racket/base

;; Test case 1: Demonstrate that object/c-opaque blocks field access
;; when the field is not in the contract

(module typed-color typed/racket
  (provide my-color%)
  (require racket/class)

  ;; Define a type WITHOUT the s-immutable field
  (define-type MyColor%
    (Class (init-rest (U (List) (List Byte Byte Byte)))
           [red (-> Byte)]
           [is-immutable? (-> Boolean)]))

  ;; Create a class that HAS the s-immutable field
  (: my-color% MyColor%)
  (define my-color%
    (class object%
      (super-new)
      (init-rest args)
      (field [r 255])
      (field [s-immutable #f])  ;; This field is NOT in the type!
      (define/public (red) r)
      (define/public (is-immutable?) s-immutable))))

(module untyped-accessor racket
  (require racket/class)
  (provide try-access-s-immutable-simple)

  ;; This simulates what color-is-immutable? does in untyped code:
  ;; Tries to access the s-immutable field
  (define (try-access-s-immutable-simple obj)
    (get-field s-immutable obj)))

(require 'typed-color 'untyped-accessor)

(define c (new my-color%))

(printf "Testing field access from untyped code...\n")

;; This should fail because s-immutable is not in the contract
(with-handlers ([exn:fail? (lambda (e)
                              (printf "ERROR (as expected): ~a\n" (exn-message e)))])
  (try-access-s-immutable-simple c)
  (printf "SUCCESS: Field access worked (unexpected!)\n"))

(printf "\n")


;; Test case 2: Show that adding the field to the type fixes the issue
(module typed-color-with-field typed/racket
  (provide my-color-fixed%)
  (require racket/class)

  ;; Define a type WITH the s-immutable field
  (define-type MyColorFixed%
    (Class (init-rest (U (List) (List Byte Byte Byte)))
           (field [s-immutable Boolean])  ;; Field is now in the type!
           [red (-> Byte)]
           [is-immutable? (-> Boolean)]))

  (: my-color-fixed% MyColorFixed%)
  (define my-color-fixed%
    (class object%
      (super-new)
      (init-rest args)
      (field [r 255])
      (field [s-immutable #f])
      (define/public (red) r)
      (define/public (is-immutable?) s-immutable))))

(require 'typed-color-with-field)

(define c2 (new my-color-fixed%))

(printf "Testing field access with field in type...\n")

(with-handlers ([exn:fail? (lambda (e)
                              (printf "ERROR (unexpected): ~a\n" (exn-message e)))])
  (define result (get-field s-immutable c2))
  (printf "SUCCESS: Field access worked! Value = ~a\n" result))
