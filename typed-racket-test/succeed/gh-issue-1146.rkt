#lang typed/racket

;; Issue #1146: Regression test - previously caused "unexpected input for check-below"
;; internal error with row polymorphic types.
;; Fixed by adding Row type handling in check-below.rkt.

(: hi (All (r #:row)
           (-> r r)))
(define (hi a)
  a)

(define cls1
  (class object%
    (init-field [x : Real 0] [y : Real 0])
    (super-new)))

(hi cls1)
