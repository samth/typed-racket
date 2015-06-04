#lang racket/base

(require racket/pretty racket/dict syntax/parse syntax/id-table unstable/sequence
         (for-template racket/base))

(define-syntax-class simple
  #:literal-sets (kernel-literals)
  #:literals (values call-with-continuation-barrier)
  [pattern (begin e:simple ...)]
  [pattern (begin0 e:simple ...)]
  [pattern _:id]
  [pattern (quote _)]
  [pattern (quote-syntax . _)]
  [pattern (#%plain-lambda . _)]
  [pattern (case-lambda . _)]
  [pattern (#%plain-app values e:simple ...)]
  [pattern (#%plain-app call-with-continuation-barrier (#%plain-lambda () _ ...))
           #:when (printf "c-w-c-b: ~a\n" (syntax->datum this-syntax))])

(define-syntax-class letrec-clause
  #:attributes ([mutated-vars 1])
  #:literal-sets (kernel-literals)
  #:literals (values call-with-continuation-barrier)
  [pattern [(v ...) (#%plain-app call-with-continuation-barrier (#%plain-lambda () _ ...))]
           #:with (mutated-vars ...) #'()]
  [pattern [(v ...) e]
           #:with (mutated-vars ...) #'(v ...)])


;; find and add to mapping all the set!'ed variables in form
;; if the supplied mapping is mutable, mutates it
;; default is immutability
;; syntax [table] [pred] -> table
(define (find-mutated-vars form
                           [tbl (make-immutable-free-id-table)]
                           [pred #f])
  ;(pretty-print (syntax->datum form))
  (define add (if (dict-mutable? tbl)
                  (lambda (t i) (dict-set! t i #t) t)
                  (lambda (t i) (dict-set t i #t))))
  (define (add-list t l)
    (for/fold ([t t]) ([i (in-list l)])
      (add t i)))
  (let loop ([stx form] [tbl tbl])
    ;; syntax-list -> table
    (define (fmv/list lstx)
      (for/fold ([tbl tbl]) ([stx (in-syntax lstx)])
        (loop stx tbl)))
    (syntax-parse stx
      #:literal-sets (kernel-literals)
      ;; let us care about custom syntax classes
      [form
       #:when pred
       #:attr result (pred #'form)
       #:when (attribute result)
       (define-values (sub name)
         (values (car (attribute result))
                 (cadr (attribute result))))
       (add (loop sub tbl) name)]
      ;; what we care about: set!
      [(set! v e)
       #:when (not pred)
       (add (loop #'e tbl) #'v)]
      ;; forms with expression subforms
      [(define-values (var ...) expr)
       (loop #'expr tbl)]
      [(#%expression e) (loop #'e tbl)]
      [(#%plain-app . rest) (fmv/list #'rest)]
      [(begin . rest) (fmv/list #'rest)]
      [(begin0 . rest) (fmv/list #'rest)]
      [(#%plain-lambda _ . rest) (fmv/list #'rest)]
      [(case-lambda (_  rest ...) ...)
       (fmv/list #'(rest ... ...))]
      [(if . es) (fmv/list #'es)]
      [(with-continuation-mark . es) (fmv/list #'es)]
      [(let-values ([_ e] ...) b ...) (fmv/list #'(b ... e ...))]
      [(letrec-values ([(v ...) e:simple] ... (~and lc:letrec-clause [(v2 ...) e2]) ...) b ...)
       (add-list (fmv/list #'(b ... e ... e2 ...)) (syntax->list #'(lc.mutated-vars ... ...)))]
      [(#%plain-module-begin . forms) (fmv/list #'forms)]
      ;; all the other forms don't have any expression subforms (like #%top)
      [_ tbl])))

(provide find-mutated-vars)
