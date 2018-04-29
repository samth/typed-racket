#;
(exn-pred exn:fail:contract? #rx"transient-assert")

#lang typed/racket/shallow/base

;; Expected: transient-assert error
;;
;; With a similar program, we can end up passing a bad input to `cdr`,
;;  so transient functions need to be careful to protect themselves
;;  (untyped & typed need to take care too, of course).
;; But, I don't think we can end up with a bad op in transient code.

(require/typed racket/base
  (cdr (All (A) (U (Boxof A) (Pairof A A) (-> (Pairof String String) Symbol)))))

(let ((v : (U (Boxof String) (Pairof String String) (-> (Pairof String String) Symbol))
       (inst cdr String)))
  (if (box? v)
    #f
    (if (pair? v)
      #f
      (v (cons "a" "aaa")))))

