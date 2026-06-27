#lang racket/base

;; A helper for predefining the contract for a type in the module where
;; that type is defined, so that other modules can reference the
;; (potentially huge, recursive) contract instead of regenerating it.
;; See typed-racket/static-contracts/instantiate's `predefined-contracts`
;; submodule and the lookup in type->static-contract.
;;
;; `generate-predefined-contracts` takes, for each entry, a compile-time
;; *expression that produces a Type* (so it works for any named type, not
;; just `(Instance C)`), a contract kind, and the sides to register.

(require (for-syntax racket/base
                     racket/match
                     racket/syntax
                     (only-in typed-racket/private/type-contract
                              extra-requires type->static-contract)
                     (only-in typed-racket/static-contracts/instantiate
                              instantiate/optimize)
                     typed-racket/private/parse-type
                     (only-in typed-racket/rep/type-rep make-Instance Instance? Instance-cls Name? Name-id)
                     typed-racket/env/env-req))

;; derive a readable name for the contract identifier from a type expr
(define-for-syntax (->name type-expr)
  (syntax-case type-expr (make-Instance parse-type quote-syntax)
    [(make-Instance (parse-type (quote-syntax c)))
     (identifier? #'c) (format-symbol "~a-instance/c" (syntax-e #'c))]
    [(make-Instance (parse-type c))
     (identifier? #'c) (format-symbol "~a-instance/c" (syntax-e #'c))]
    [_ 'predefined/c]))

;; (generate-predefined-contracts [type-expr kind (side ...)] ...)
;;   type-expr : a phase-1 expression evaluating to a Type?
;;   kind      : impersonator | chaperone | flat
;;   side      : typed | untyped   ('both lookups fall back to inline)
(define-syntax (generate-predefined-contracts stx)
  (define defs-stx null)
  (define sets-stx null)
  (define (gen type-expr kind side)
    (define typ (syntax-local-eval type-expr))
    (define ts (case side [(typed) #t] [(untyped) #f]
                          [else (raise-syntax-error 'generate-predefined-contracts
                                                    "side must be `typed` or `untyped`" stx side)]))
    (define (fail #:reason [r #f])
      (raise-syntax-error 'generate-predefined-contracts
                          (format "could not generate contract: ~a" r) type-expr))
    ;; Generate the full (untrusted) contract for this side -- a sound,
    ;; reusable definition (trust-based optimization is position-specific
    ;; and cannot be baked into a shared contract).
    (define sc (type->static-contract typ fail #:typed-side ts))
    (match-define (list defs ctc)
      (instantiate/optimize sc fail kind #:cache (make-hash)))
    (define n (generate-temporary (->name type-expr)))
    (set! defs-stx (append defs-stx defs
                           (list #`(provide #,n)
                                 #`(define #,n #,ctc))))
    ;; register (module-path . symbol); the type key is recomputed at load
    ;; time by re-evaluating the same type expression
    (set! sets-stx (cons #`(hash-set! predef-contracts
                                      (cons #,type-expr '#,side)
                                      (cons contract-defs-mod-path '#,(syntax-e n)))
                         sets-stx)))
  (syntax-case stx ()
    [(_ [type-expr kind (mode ...)] ...)
     (for ([te (in-list (syntax->list #'(type-expr ...)))]
           [kind (in-list (syntax->list #'(kind ...)))]
           [modes (in-list (syntax->list #'((mode ...) ...)))])
       (for ([m (in-list (syntax->list modes))])
         (gen te (syntax-e kind) (syntax-e m))))])
  #`(begin
      ;; the actual contract definitions
      (module* #%contract-defs #f
        (#%plain-module-begin
         (#%declare #:empty-namespace)
         #,extra-requires
         #,@defs-stx))
      ;; register the (module-path . symbol) of each contract, at phase 1,
      ;; so do-contract-requires can populate the predef table downstream
      (begin-for-syntax
        (module* #%contract-defs-names #f
          (require (submod typed-racket/static-contracts/instantiate predefined-contracts)
                   typed-racket/private/parse-type
                   (only-in typed-racket/rep/type-rep make-Instance)
                   racket/base
                   syntax/modcollapse)
          ;; the module path of our sibling #%contract-defs submodule
          (define contract-defs-mod-path
            (collapse-module-path-index
             (module-path-index-join
              '(submod ".." #%contract-defs)
              (variable-reference->module-path-index (#%variable-reference)))))
          #,@sets-stx))
      ;; make sure downstream modules know to load our #%contract-defs-names
      (begin-for-syntax
        (add-mod! (variable-reference->module-path-index (#%variable-reference))))))

(provide generate-predefined-contracts)
