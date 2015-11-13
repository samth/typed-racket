#lang racket/unit

(require "../../utils/utils.rkt"
         "signatures.rkt"
         "utils.rkt"
         syntax/parse racket/match racket/function
         syntax/parse/experimental/reflect racket/list
         racket/stream
         (typecheck signatures tc-funapp tc-subst)
         (types abbrev utils)
         (env lexical-env)
         (logic type-update)
         (rep type-rep filter-rep object-rep))

(import tc-expr^ tc-app-keywords^
        tc-app-hetero^ tc-app-list^ tc-app-apply^ tc-app-values^
        tc-app-objects^ tc-app-eq^ tc-app-lambda^ tc-app-special^
        tc-app-contracts^)
(export tc-app^)

(define-tc/app-syntax-class (tc/app-regular* expected)
  (pattern form (tc/app-regular #'form expected)))

(define-syntax-rule (combine-tc/app-syntax-classes class-name case ...)
  (define-syntax-class (class-name expected)
    #:attributes (check)
    (pattern (~reflect v (case expected) #:attributes (check))
             #:attr check (attribute v.check)) ...))

(combine-tc/app-syntax-classes tc/app-special-cases
  tc/app-list
  tc/app-apply
  tc/app-eq
  tc/app-hetero
  tc/app-values
  tc/app-keywords
  tc/app-objects
  tc/app-lambda
  tc/app-special
  tc/app-contracts
  tc/app-regular*)

;; the main dispatching function
;; syntax (or/c tc-results/c #f) -> tc-results/c
(define (tc/app form expected)
  (syntax-parse form
    [(#%plain-app . (~var v (tc/app-special-cases expected)))
     ((attribute v.check))]))



;; TODO: handle drest, and filters/objects
(define (arr-matches? arr args)
  (match arr
    [(arr: domain
           (Values: (list (Result: v (FilterSet: (Top:) (Top:)) (Empty:)) ...))
           rest #f (list (Keyword: _ _ #f) ...) dep?)
     (cond
       [(< (length domain) (length args)) rest]
       [(= (length domain) (length args)) #t]
       [else #f])]
    [_ #f]))

(define (has-filter? arr)
  (match arr
    [(arr: _ (Values: (list (Result: v (FilterSet: (Top:) (Top:)) (Empty:)) ...))
           _ _ (list (Keyword: _ _ #f) ...) dep?) #f]
    [else #t]))


(define (maybe-res-obj res)
  (match res
    [(tc-result1: t fs o)
     #:when (non-empty-obj? o)
     o]
    [else #f]))

(define (tc/app-regular form expected)
  (syntax-case form ()
    [(f . args)
     (let* ([f-ty (tc-expr/t #'f)]
            [args* (syntax->list #'args)])
       (define (matching-arities arrs)
         (for/list ([arr (in-list arrs)] #:when (arr-matches? arr args*)) arr))
       (define (has-drest/filter? arrs)
         (for/or ([arr (in-list arrs)])
           (or (has-filter? arr) (arr-drest arr))))
       ;; check arg types w/o expected (in case more precise type is available)       
       (define initial-arg-res-list
         (match f-ty
           [(Function: (list (arr: doms rng rest drest kws #t)))
            ;; typecheck each arg against the respective domain
            ;; while substituting objects for DB indexes of later domain types
            (let loop ([remaining-args-stx args*]
                       [remaining-doms doms]
                       [args-res null]
                       [idx 0])
              (cond
                [(or (null? remaining-args-stx)
                     (null? remaining-doms))
                 (reverse args-res)]
                [else
                 (match-define (cons a-stx rst-as-stx) remaining-args-stx)
                 (match-define (cons dom-t rst-doms) remaining-doms)
                 (define arg-t (tc-expr/check a-stx (ret dom-t) #:more-specific #t))
                 (define obj (maybe-res-obj arg-t))
                 (loop rst-as-stx
                       (if obj
                           (map (λ (d) (subst-type d (list 0 idx) obj #t)) rst-doms)
                           rst-doms)
                       (cons arg-t args-res)
                       (add1 idx))]))]
           [(Function: (? has-drest/filter?))
            (map single-value args*)]
           [(Function:
             (app matching-arities
                  (list (arr: doms ranges rests drests _ _) ..1)))
            (define matching-domains
              (sequence->stream
               (in-values-sequence
                (apply in-parallel
                       (for/list ((dom-ts (in-list doms)) (rest (in-list rests)))
                         (in-sequences (in-list dom-ts) (in-cycle (in-value rest))))))))
            (let loop ([remaining-args-stx args*]
                       [remaining-domss matching-domains]
                       [args-res null]
                       [idx 0]
                       [subst values])
              (cond
                [(or (null? remaining-args-stx)
                     (stream-empty? remaining-domss))
                 (reverse args-res)]
                [else
                 (match-define (cons a-stx rst-as-stx) remaining-args-stx)
                 (match-define (cons (app subst t) (app (λ (pre-ts) (map subst pre-ts)) ts))
                   (stream-first remaining-domss))
                 (define res-typess (stream-rest remaining-domss))
                 (define arg-t (if (for/and ((t2 (in-list ts))) (equal? t t2))
                                   (tc-expr/check a-stx (ret t) #:more-specific #t)
                                   (single-value a-stx)))
                 (define obj (maybe-res-obj arg-t))
                 (loop rst-as-stx
                       res-typess
                       (cons arg-t args-res)
                       (add1 idx)
                       (if (not obj) subst (λ (t) (subst-type (subst t) (list 0 idx) obj #t))))]))]
           [_ (map single-value args*)]))

       (tc/funapp #'f #'args f-ty initial-arg-res-list expected))]))
