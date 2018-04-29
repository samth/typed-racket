#;
(exn-pred exn:fail:contract? #rx"transient-assert")
#lang typed/racket/shallow

(define: b : (Boxof Any) (box 4))

(define-predicate boxof-integer? (Boxof Integer))

(define (set-b-box! v) (set-box! b v))

(: a-very-listy-integer (-> Integer))
(define (a-very-listy-integer)
  (cond [(boxof-integer? b)  (set-b-box! '(1 2 3))
                             (unbox b)]
        [else  (error 'a-very-listy-integer "can't happen")]))

(a-very-listy-integer)
