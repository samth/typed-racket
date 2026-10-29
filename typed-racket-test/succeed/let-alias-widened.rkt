#lang typed/racket
;; A binding whose right-hand side widens a variable's type, as with
;; `ann` to `Any`, must not alias that variable; otherwise the variable
;; would get the wider type.
(struct (X) s ([i : X]) #:mutable #:transparent)
(struct (X) t ([i : X]))
(struct u ([i : Integer]) #:mutable)

(let () (define s1 (s 42)) (define s3 (ann s1 Any)) (s-i s1))
(let () (define s1 (t 42)) (define s3 (ann s1 Any)) (t-i s1))
(let () (define s1 (u 42)) (define s3 (ann s1 Any)) (u-i s1))
(let () (define s1 (s 42)) (define s3 : Any s1) (s-i s1))
(let () (define s1 (vector 1)) (define s3 (ann s1 Any)) (vector-ref s1 0))
(let ([s1 (s 42)]) (let ([s3 (ann s1 Any)]) (s-i s1)))
