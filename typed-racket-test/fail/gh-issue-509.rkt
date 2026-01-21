#;
(exn-pred #rx"Type Checker")
#lang typed/racket

;; Issue #509: Internal Typechecker Error: Got non-dcons
;; Bug in dmap.rkt where loop variables shadow struct field bindings

(define-type Filter
  (All (a b ...) (-> (-> a b ... b Any) (Listof a) (Listof b) ... (Listof a))))

(: filter* Filter)
(define (filter* p? l)
  (cond
    [(andmap empty? l) '[]]
    [else (define fst ({inst map a b ...} first l))
          (define rst (apply filter* p? ({inst map a b ...} rest l)))
          (if (apply p? fst) (cons fst rst) rst)]))

(filter* (lambda ({x : Integer}) (> x 1)) '(0 1 2))
