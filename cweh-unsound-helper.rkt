#lang typed/racket/base
;; Typed-racket helper for the soundness demo of issue #1505.
;; Provides a tiny `raise-continuable` whose captured continuation is
;; embedded in the raised value, mirroring the trick R6RS
;; rnrs/exceptions-6 uses internally. The carrier is an exn:fail subtype
;; so plain `raise` accepts it.

(provide make-raise-continuable
         KBox k-box k-box? k-box-k)

(struct k-box exn:fail ([k : (-> Any Nothing)])
  #:transparent #:type-name KBox)

(: make-raise-continuable (-> Any Any))
(define (make-raise-continuable v)
  (let/cc cont : Any
    (raise (k-box "raise-continuable"
                  (current-continuation-marks)
                  (lambda ([x : Any]) (cont x))))))
