#;
(exn-pred exn:fail:contract? #rx"transient-assert")

#lang typed/racket/base/shallow

;; Expected: transient-assert error
;;
;; To remove the error, we need to treat `inst` as an elimination form
;; when the poly type does not guarantee some kind of shape.

(require/typed racket/base
  (cdr (All (A) (U (Boxof A) A))))

(let ((v : (U (Boxof (Pairof String String)) (Pairof String String))
       (inst cdr (Pairof String String))))
  (if (box? v)
    #f
    (car v)))

