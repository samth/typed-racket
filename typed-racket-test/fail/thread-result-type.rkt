#;
(exn-pred #rx"thread-wait")
#lang typed/racket

;; `thread-wait` on a thread with unknown results can produce any number
;; of values, so it cannot appear where one value is expected.
(define (f [t : ThreadTop]) : Void
  (thread-wait t))
