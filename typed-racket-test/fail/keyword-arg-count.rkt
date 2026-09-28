#lang typed/racket
(define (called-fun [prefix : String]
                    [get-num : (-> Real)]
                    #:scrub s) : Real
  (get-num))
(called-fun "abcd" #t #:scrub #t)
