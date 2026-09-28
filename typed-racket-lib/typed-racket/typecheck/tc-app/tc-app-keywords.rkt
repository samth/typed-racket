
#lang racket/unit

(require "signatures.rkt"
         "utils.rkt"
         syntax/parse syntax/stx racket/match racket/set
         "../signatures.rkt"
         "../tc-app-helper.rkt"
         "../integer-refinements.rkt"
         "../check-below.rkt"
         "../tc-funapp.rkt"
         "../tc-metafunctions.rkt"
         "../../types/abbrev.rkt"
         "../../types/utils.rkt"
         "../../types/substitute.rkt"
         "../../types/subtype.rkt"
         "../../types/type-table.rkt"
         "../../rep/type-rep.rkt"
         (except-in "../../utils/utils.rkt" infer)
         "../../utils/tc-utils.rkt"
         "../../infer/infer.rkt"
         (for-label racket/base)
         ;; adjusted -1 since it's provided for-syntax
         (only-in (for-template racket/contract/private/provide)
                  contract-neg-party-property))


(import tc-expr^)
(export tc-app-keywords^)

(define-literal-set keyword-literals #:for-label (list))

(define-tc/app-syntax-class (tc/app-keywords expected)
  #:literal-sets (kernel-literals keyword-literals)
  (pattern (~and form
                 ((#%plain-app cpce s-kp fn kpe kws num)
                  kw-list
                  (#%plain-app list . kw-arg-list)
                  . *pos-args))
    #:declare cpce (id-from 'checked-procedure-check-and-extract 'racket/private/kw)
    #:declare s-kp (id-from 'struct:keyword-procedure 'racket/private/kw)
    #:declare kpe  (id-from 'keyword-procedure-extract 'racket/private/kw)
    ;; If this application is of a module boundary contract function or not
    ;; If #t, then the contract system has inserted an extra argument which we
    ;; need to ignore
    #:attr boundary-ctc? (contract-neg-party-property #'fn)
    #:do [(for-each register-ignored! (syntax->list #'form))] ; no type info, so can't optimize
    #:with pos-args (if (attribute boundary-ctc?)
                        (stx-cdr #'*pos-args)
                        #'*pos-args)

    (let ()
      (define (tc/app-mono-fun arrows)
        (tc-keywords #'(#%plain-app . form) arrows (type->list (tc-expr/t #'kws))
                     #'kw-arg-list #'pos-args expected))

      (define (tc/app-poly-fun vars arrow fail)
        (match-define (and ar (Arrow: dom rst kw-formals rng)) arrow)
        ;; if the types of the keyword arguments have type variables or rst is
        ;; set, stop.
        (unless (or (set-empty? (fv/list kw-formals)) (not rst))
          (fail))
        (match (stx-map single-value #'pos-args)
           [(list (tc-result1: argtys-t) ...)
            (let* ([subst (infer vars null argtys-t dom rng
                                 (and expected (tc-results->values expected)))])
              (unless subst
                (fail))
              (tc-keywords #'form (list (subst-all subst ar))
                           (type->list (tc-expr/t #'kws)) #'kw-arg-list #'pos-args expected))]))

      (match (tc-expr/t #'fn)
        [(Poly: vars
                (Fun: (list arrow)))
         (=> fail)
         (tc/app-poly-fun vars arrow fail)]
        [(Fun: arrows)
         (tc/app-mono-fun arrows)]
        [(Poly: _ (Fun: _))
         (tc-error/expr "Inference for polymorphic keyword functions not supported")]
        [(Intersection: (HasArrows: arrows) _)
         (tc/app-mono-fun arrows)]
        [(Intersection: (Poly: vars
                               (Fun: (list arrow))) _)
         (=> fail)
         (tc/app-poly-fun vars arrow fail)]
        [t
         (tc-error/expr "Cannot apply expression of type ~a, since it is not a function type" t)]))))

(define (tc-keywords/internal arity kws kw-args error?)
  (match arity
    [(Arrow: dom (not (? RestDots?)) ktys rng)
     ;; assumes that everything is in sorted order
     (let loop ([actual-kws kws]
                [actual-args (syntax->list kw-args)]
                [actual-res (if error? '() (stx-map single-value kw-args))]
                [formals ktys])
       (match* (actual-kws formals)
         [('() '())
          (void)]
         [(_ '())
          (if error?
              (tc-error/delayed "Unexpected keyword argument ~a" (car actual-kws))
              #f)]
         [('() (cons fst rst))
           (match fst
             [(Keyword: k _ #t)
              (if error?
                  (tc-error/delayed "Missing keyword argument ~a" k)
                  #f)]
            [_ (loop actual-kws actual-args actual-res rst)])]
         [((cons k kws-rest) (cons (Keyword: k* t req?) form-rest))
          (cond [(eq? k k*) ;; we have a match
                 (if error?
                     (begin
                       ;; Check kw-arg with expected keyword type. On failure, emit classic message.
                       (unless (tc-expr/check? (car actual-args) (ret t))
                         (define ty (tc-expr/t (car actual-args)))
                         (tc-error/delayed
                          "Wrong function argument type, expected ~a, got ~a for keyword argument ~a"
                          t ty k))
                       (loop kws-rest (cdr actual-args) actual-res form-rest))
                     (let ([ty (match (car actual-res)
                                  [(tc-result1: ty) ty]
                                  [(tc-results: (list (tc-result: ty _ _)) _) ty]
                                  [_ Univ])])
                       (and (subtype ty t)
                            (loop kws-rest (cdr actual-args) (cdr actual-res) form-rest))))]
                 [req? ;; this keyword argument was required
                  (if error?
                      (begin (tc-error/delayed "Missing keyword argument ~a" k*)
                             (loop kws-rest (cdr actual-args) (cdr actual-res) form-rest))
                      #f)]
                 [else ;; otherwise, ignore this formal param, and continue
                  (loop actual-kws actual-args actual-res form-rest)])]))]))

(define (tc-keywords form arrows kws kw-args pos-args expected)
  (define no-keywords? (null? (syntax->list kw-args)))
  (define (dom-ref dom rst idx)
    (define dl (length dom))
    (cond
      [(< idx dl) (list-ref dom idx)]
      [else
       (match rst
         [(Rest: rst-ts)
          (define k (length rst-ts))
          (list-ref rst-ts (remainder (- idx dl) (max 1 k)))]
         [_ #f])]))
  (define (compute-arg-results f-id dom rst)
    (define args* (syntax->list pos-args))
    (define check-arg (if (and (identifier? f-id)
                               (with-refinements?)
                               (has-linear-integer-refinements? f-id))
                          tc-dep-fun-arg
                          single-value))
    (for/list ([arg-stx (in-list args*)]
               [idx (in-naturals)])
      (define maybe-dom (dom-ref dom rst idx))
      (if maybe-dom
          (check-arg arg-stx (ret maybe-dom))
          (check-arg arg-stx))))
  (match arrows
    [(list (and a (Arrow: dom (and rst (not (? RestDots?))) ktys rng rng-T+)))
     (if no-keywords?
         (begin
           ;; still signal missing required keywords
           (tc-keywords/internal a kws kw-args #t)
           (tc/funapp (car (syntax-e form)) pos-args
                      (->* dom rst rng :T+ rng-T+)
                      (compute-arg-results #'fn dom rst)
                      expected))
         (begin
           (tc-keywords/internal a kws kw-args #t)
           (tc/funapp (car (syntax-e form)) pos-args
                      (->* dom rst rng :T+ rng-T+)
                      (stx-map tc-expr pos-args) expected)))]
    [(list (and a (Arrow: doms (and rsts (not (? RestDots?))) _ rngs rngs-T+)) ...)
     (let ([new-arrows
            (for/list ([a (in-list arrows)]
                       #:when (tc-keywords/internal a kws kw-args #f))
              (match a
                [(Arrow: dom (and rst (not (? RestDots?))) _ rng rng-T+)
                 (make-Arrow dom rst '() rng rng-T+)]))])
       (if (null? new-arrows)
           (domain-mismatches
            (car (syntax-e form)) (cdr (syntax-e form))
            (make-Fun arrows) doms rsts rngs
            (stx-map tc-expr pos-args)
            #f #f #:expected expected
            #:msg-thunk
            (lambda (dom)
              (string-append "No function domains matched in function application:\n"
                             dom)))
           (let ([arg-ress
                  (if no-keywords?
                      (let* ([args* (syntax->list pos-args)]
                             [check-arg (if (and (identifier? #'fn)
                                                 (with-refinements?)
                                                 (has-linear-integer-refinements? #'fn))
                                            tc-dep-fun-arg
                                            single-value)])
                        (for/list ([arg-stx (in-list args*)]
                                   [idx (in-naturals)])
                          (define maybe-tys
                            (for/list ([ar (in-list new-arrows)])
                              (match ar
                                [(Arrow: dom rst '() _ _)
                                 (dom-ref dom rst idx)])))
                          (cond
                            [(and (pair? maybe-tys)
                                  (andmap (lambda (t) (equal? t (car maybe-tys))) (cdr maybe-tys))
                                  (car maybe-tys))
                             (check-arg arg-stx (ret (car maybe-tys)))]
                            [else (check-arg arg-stx)])))
                      (stx-map tc-expr pos-args))])
             (tc/funapp (car (syntax-e form)) pos-args
                        (make-Fun new-arrows)
                        arg-ress
                        expected))))]))

(define (type->list t)
  (match t
    [(Pair: (Value: (? keyword? k)) b)
     (cons k (type->list b))]
    [(? Base:Null?) null]
    [_ (int-err "bad value in type->list: ~a" t)]))
