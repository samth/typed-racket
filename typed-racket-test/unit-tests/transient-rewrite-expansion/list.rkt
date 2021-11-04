#lang typed/racket/base/shallow

;; Expand and look for transient-assert / lack of.
;; See comments below.

(let ((x0 : (List) '()))
  (cdr x0) ;; yes transient-assert
  (cddr x0)) ;; yes transient-assert

(let ((x1 : (List Symbol) '(a)))
  (cdr x1) ;; no transient-assert
  (cddr x1)) ;; yes transient-assert

(let ((x2 : (List Symbol Symbol) '(a b)))
  (cdr x2) ;; no transient-assert
  (cddr x2) ;; no transient-assert
  (cdddr x2)) ;; yes transient-assert after (cdr (unsafe-cdr (unsafe-cdr _)))

(let ((x3 : (List Symbol Symbol Symbol) '(a b c)))
  (cdr x3) ;; no transient-assert
  (cddr x3) ;; no transient-assert
  (cdddr x3) ;; no transient-assert
  (cddddr x3)) ;; yes transient-assert after (cdr (unsafe-cdr (unsafe-cdr _)))

(let ((x4 : (List Symbol Symbol Symbol Symbol) '(a b c d)))
  (cdr x4) ;; no transient-assert
  (cddr x4) ;; no transient-assert
  (cdddr x4) ;; no transient-assert
  (cddddr x4)) ;; no transient-assert

(let ((x5 : (Pairof Symbol Null) '(a . ())))
  (cdr x5)) ;; no transient-assert
