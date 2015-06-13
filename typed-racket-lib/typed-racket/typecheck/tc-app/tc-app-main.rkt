#lang racket/unit

(require "../../utils/utils.rkt"
         "signatures.rkt"
         "utils.rkt"
         syntax/parse racket/match racket/function
         syntax/parse/experimental/reflect racket/list
         (typecheck signatures tc-funapp tc-subst tc-envops)
         (types abbrev utils)
         (env lexical-env)
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

       (define initial-arg-res-list
         (match f-ty
           ;; TODO(AMK) support multi-arr functions w/ dependent types
           [(Function: (list (arr: doms rng rest drest kws #t)))
            ;; here we check argument types before bounding them w/ expected
            ;; results if possible, so more precise types in the domain
            ;; can refine dependent types
            (define arg-ts (map (curryr tc-expr/check? #f) args*))
            (define arg-ts* (for/list ([t (in-list arg-ts)]
                                       [a (in-list args*)]
                                       [dom-t (in-list doms)])
                              (or t (tc-expr/check a (ret dom-t)))))
            arg-ts*]
           [(Function: (? has-drest/filter?))
            (map single-value args*)]
           [(Function:
             (app matching-arities
                  (list (arr: doms ranges rests drests _ _) ..1)))
            (define matching-domains
              (in-values-sequence
               (apply in-parallel
                      (for/list ((dom (in-list doms)) (rest (in-list rests)))
                        (in-sequences (in-list dom) (in-cycle (in-value rest)))))))
            (for/list ([a (in-list args*)] [types matching-domains])
              (match-define (cons t ts) types)
              (if (for/and ((t2 (in-list ts))) (equal? t t2))
                  (tc-expr/check a (ret t))
                  (single-value a)))]
           [_ (map single-value args*)]))

       ;; generate temporary identifiers for arguments w/o objects
       ;; and any associated props discussing their types
       (define-values
         (args-res arg-objs arg-tys props temp-ids)
         (for/fold ([res-l null]
                    [obj-l null]
                    [ty-l null]
                    [prop-l null]
                    [temp-id-l null])
                   ([r (in-list (reverse initial-arg-res-list))])
           (match-define (tc-result1: t fs o) r)
           (cond
             [(non-empty-obj? o)
              (values (cons r res-l)
                      (cons o obj-l)
                      (cons t ty-l)
                      prop-l
                      temp-id-l)]
             [else
              (define temp-id (genid))
              (define o* (-id-path temp-id))
              (values (cons (ret t fs o*) res-l)
                      (cons o* obj-l)
                      (cons t ty-l)
                      (cons (-filter t o*) prop-l)
                      (cons temp-id temp-id-l))])))

       ;; extend the env w/ any new types
       (define-values (env* _) (env+props (lexical-env) props))

       ;; tc the application TODO (ret -bot) on no env*?
       (define tc-res (with-lexical-env
                       (or env* (lexical-env))
                       (tc/funapp #'f
                                  #'args
                                  (instantiate-fun-args f-ty arg-objs)
                                  args-res
                                  (and expected (unabstract-expected/arg-objs expected arg-objs)))))

       ;; erase any temps remaining in the result from typechecking
       (for/fold ([tc-res tc-res])
                 ([temp-id (in-list temp-ids)])
         (subst-tc-results tc-res temp-id -empty-obj #t)))]))
