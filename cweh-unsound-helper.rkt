#lang typed/racket/base
;; Helper for the call-with-exception-handler discussion in issue #1505.
;;
;; This is a tiny `raise-continuable`: it captures the continuation of
;; the call and stores it (type-erased to `(-> Any Nothing)`) inside the
;; raised value, so an exception handler can tail-call the continuation
;; and supply any value as the result of `make-raise-continuable`. It's
;; the same trick rnrs/exceptions-6 uses internally, simplified.
;;
;; The carrier subclasses `exn:fail` only because TR's `raise` requires
;; values from a restricted union; the subclassing has no semantic role.

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
