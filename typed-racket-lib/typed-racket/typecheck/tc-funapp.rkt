#lang racket/base

(require (rename-in "../utils/utils.rkt" [infer r:infer])
         racket/match racket/list racket/function
         (prefix-in c: (contract-req))
         (env tvar-env lexical-env)
         (for-syntax syntax/parse racket/base)
         (types utils subtype resolve abbrev
                substitute classes)
         (logic type-update)
         (typecheck tc-metafunctions tc-app-helper tc-subst tc-envops)
         (rep type-rep object-rep)
         (r:infer infer))

(require-for-cond-contract syntax/stx)

(provide/cond-contract
  [tc/funapp
   (syntax? stx-list? Type/c (c:listof tc-results1/c)
    (c:or/c #f tc-results/c)
    . c:-> . full-tc-results/c)])

(define-syntax (handle-clauses stx)
  (syntax-parse stx
    [(_  (lsts ... arrs) f-stx args-stx pred infer t args-res expected)
     (with-syntax ([(vars ... a) (generate-temporaries #'(lsts ... arrs))])
       (syntax/loc stx
         (or (for/or ([vars (in-list lsts)] ... [a (in-list arrs)]
                      #:when (pred vars ... a))
               (let ([substitution (infer vars ... a)])
                 (and substitution
                      (tc/funapp1 f-stx args-stx (subst-all substitution a)
                                  args-res expected #:check #f))))
             (poly-fail f-stx args-stx t args-res
                        #:name (and (identifier? f-stx) f-stx)
                        #:expected expected))))]))
;(define counter 0)
(define (tc/funapp f-stx args-stx f-ty initial-args-res expected)

  #;(printf "<~a><<TC/FUNAPP 1>>\n (apply ~a ~a)\n-F-TY-\n ~a\n --INIT-ARGS--\n ~a\n --EXPTD--\n ~a\n\n"
          counter f-stx args-stx f-ty initial-args-res expected)
  
  ;; generate temporary identifiers for arguments w/o objects
  ;; and any associated props discussing their types
  
  (define-values
    (args-res arg-objs arg-tys props temp-ids)
    (for/fold ([res-l null]
               [obj-l null]
               [ty-l null]
               [prop-l null]
               [temp-id-l null])
              ([r (in-list (reverse initial-args-res))])
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
                 (cons (-is-type o* t) prop-l)
                 (cons temp-id temp-id-l))])))

  #;(printf "<~a><<TC/FUNAPP 2>>\n --NEW-ARGS--\n ~a\n\n"
          counter args-res)
  
  (define env* (env+props (lexical-env) props))

  #;(printf "<~a><<TC/FUNAPP 3>>\n --OLD-ENV--\n ~a\n --NEW-ENV--\n ~a\n\n"
          counter (lexical-env) env*)
  
  ;; NOTE: this next line IS COSTLY it seems (probably because we're rebuilding
  ;; every function here twice?)
  ;; TODO - only restrict-type/env if fun-type contains dependent references?
  ;; not as simple as checking for free vars (since fun is a binder)
  (define f-ty*
    (and env* (restrict-type/env (instantiate-fun-args f-ty arg-objs) env*)))
  (define expected* (and expected (unabstract-expected/arg-objs expected arg-objs)))

  #;(printf "<~a><<TC/FUNAPP 4>>\n --NEW-F-TY--\n ~a\n\n"
          counter f-ty*)

  #;(printf "<~a><<TC/FUNAPP 5>>\n --OLD-EXPTD--\n ~a\n --NEW-EXPTD--\n ~a\n\n"
          counter expected expected*)
  
  ;; tc the application TODO (ret -bot) on no env*?
  (define tc-res
    (cond
      [env*
       (with-lexical-env
        env*
        (tc/funapp* f-stx args-stx f-ty* args-res expected*))]
      [expected*
       expected*]
      [else
       (define trivial-args
         (map (const (ret -Nothing (-PS -bot -bot) -empty-obj)) args-res))
       (tc/funapp* f-stx args-stx f-ty* trivial-args expected*)]))

  #;(printf "<~a><<TC/FUNAPP 6>>\n --RESULTS--\n ~a\n\n"
          counter tc-res)
  
  ;; erase any temps remaining in the result from typechecking
  (define v (for/fold ([tc-res tc-res])
                      ([temp-id (in-list temp-ids)])
              (subst-tc-results tc-res temp-id -empty-obj #t)))

  #;(printf "<~a><<TC/FUNAPP 7>>\n --RESULTS after temps removed--\n ~a\n\n"
          counter v)
  ;(set! counter (add1 counter))
  v)


(define/cond-contract (tc/funapp* f-stx args-stx f-type args-res expected)
  (syntax? stx-list? Type/c (c:listof tc-results1/c)
           (c:or/c #f tc-results/c)
           . c:-> . full-tc-results/c)
  ;; TODO(AMK) this call to restrict-fun/arg-types should probably be removed
  ;; if we simply extend the environment w/ the arg/type filters
  ;; for the subtyping and/or tc/funapp1 calls that should be equivalent/better
  (match-define (list (tc-result1: argtys _ argobjs) ...) args-res)
  (match f-type
    ;; we special-case this (no case-lambda) for improved error messages
    ;; tc/funapp1 currently cannot handle drest arities
    [(Function: (list (and a (arr: _ _ _ #f _ dep?))))
     ;; non-dependent case
     (tc/funapp1 f-stx args-stx a args-res expected)]
    [(Function/arrs: doms rngs rests (and drests #f) kws deps? #:arrs arrs)
     (or
      ;; find the first function where the argument types match
      (for/or ([dom (in-list doms)]
               [rng (in-list rngs)]
               [rest (in-list rests)]
               [kw (in-list kws)]
               [a (in-list arrs)]
               [dep? (in-list deps?)])
        (cond
          [(subtypes/varargs argtys argobjs dom rest)
           ;; then typecheck here
           ;; we call the separate function so that we get the appropriate
           ;; filters/objects
           (tc/funapp1 f-stx args-stx a args-res expected #:check #f)]
          [else #f]))
      ;; if nothing matched, error
      (domain-mismatches
       f-stx args-stx f-type doms rests drests rngs args-res #f #f
       #:expected expected
       #:msg-thunk (lambda (dom)
                     (string-append
                      "No function domains matched in function application:\n"
                      dom))))]
    ;; any kind of dotted polymorphic function without mandatory keyword args
    [(PolyDots: (list fixed-vars ... dotted-var)
       (Function/arrs: doms rngs rests drests (list (Keyword: _ _ #f) ...) deps? #:arrs arrs))
     (handle-clauses
      (doms rngs rests drests arrs) f-stx args-stx
      ;; predicate fun - only try inference if the argument lengths are appropriate
      (λ (dom _ rest drest a)
        (cond [rest (<= (length dom) (length argtys))]
              [drest (and (<= (length dom) (length argtys))
                          (eq? dotted-var (cdr drest)))]
              [else (= (length dom) (length argtys))]))
      ;; Only try to infer the free vars of the rng (which includes the vars
      ;; in filters/objects).
      (λ (dom rng rest drest a)
        (extend-tvars fixed-vars
          (cond
           [drest
            (infer/dots
             fixed-vars dotted-var argtys dom (car drest) rng (fv rng)
             #:expected (and expected (tc-results->values expected)))]
           [rest
            (infer/vararg fixed-vars
                          (list dotted-var)
                          argtys
                          argobjs
                          dom
                          rest
                          rng
                          (and expected (tc-results->values expected)))]
           ;; no rest or drest
           [else
            (infer fixed-vars (list dotted-var) argtys dom rng
                   (and expected (tc-results->values expected)))])))
      f-type args-res expected)]
    ;; regular polymorphic functions without dotted rest, 
    ;; we do not choose any instantiations with mandatory keyword arguments
    [(Poly: vars (Function/arrs: doms rngs rests #f (list (Keyword: _ _ kw?) ...) deps? #:arrs arrs))
     (handle-clauses
      (doms rngs rests kw? arrs) f-stx args-stx
      ;; only try inference if the argument lengths are appropriate
      ;; and there's no mandatory kw
      (λ (dom _ rest kw? a) 
        (and (andmap not kw?) ((if rest <= =) (length dom) (length argtys))))
      ;; Only try to infer the free vars of the rng (which includes the vars
      ;; in filters/objects).
      (λ (dom rng rest kw? a)
        (extend-tvars
         vars
         (infer/vararg vars
                       null
                       argtys
                       argobjs
                       dom
                       rest
                       rng
                       (and expected (tc-results->values expected)))))
      f-type args-res expected)]
    ;; Row polymorphism. For now we do really dumb inference that only works
    ;; in very restricted cases, but is probably enough for most cases in
    ;; the Racket codebase. Eventually this should be extended.
    [(PolyRow: vars constraints (and f-ty (Function/arrs: doms _ _ #f _ _)))
     (define (fail)
       (poly-fail f-stx args-stx f-type args-res
                  #:name (and (identifier? f-stx) f-stx)
                  #:expected expected))
     ;; there's only one row variable in a PolyRow (for now)
     (define row-var (car vars))
     ;; only infer if there is only one argument type that has the relevant
     ;; row type variable in its free variables in all cases
     (define row-var-idxs
       (for/list ([dom doms])
         (define num-occurs
           (for/list ([dom-type dom] [idx (in-naturals)]
                      #:when (member row-var (fv dom-type)))
             idx))
         (unless (<= (length num-occurs) 1)
           (fail))
         (if (null? num-occurs) 0 (car num-occurs))))
     (unless (or (< (length row-var-idxs) 2)
                 (apply = row-var-idxs))
       ;; row var wasn't in the same position in some cases
       (fail))
     (define idx (car row-var-idxs))
     (define resolved-argty (resolve (list-ref argtys idx)))
     (cond [(Class? resolved-argty)
            (define substitution
              (hash row-var
                    (t-subst (infer-row constraints resolved-argty))))
            (tc/funapp* f-stx args-stx (subst-all substitution f-ty)
                       args-res expected)]
           [else (fail)])]
    ;; procedural structs
    [(Struct: _ _ _ (? Function? proc-ty) _ _)
     (tc/funapp* f-stx #`(#,(syntax/loc f-stx dummy) . #,args-stx) proc-ty
                (cons (ret f-type) args-res) expected)]
    ;; parameters are functions too
    [(Param: in out)
     (match argtys
      [(list) (ret out)]
      [(list t)
       (if (subtype t in)
           (ret -Void -true-filter)
           (tc-error/expr
            #:return (ret -Void -true-filter)
            "Wrong argument to parameter - expected ~a and got ~a"
            in t))]
      [_ (tc-error/expr
           "Wrong number of arguments to parameter - expected 0 or 1, got ~a"
           (length argtys))])]
    ;; resolve names, polymorphic apps, mu, etc
    [(? needs-resolving?)
     (tc/funapp* f-stx args-stx (resolve-once f-type) args-res expected)]
    ;; a union of functions can be applied if we can apply all of the elements
    [(Union: (and ts (list (? Function?) ...)))
     (merge-tc-results
      (for/list ([fty ts])
        (tc/funapp* f-stx args-stx fty args-res expected)))]
    ;; error type is a perfectly good fcn type
    [(Error:) (ret f-type)]
    ;; otherwise fail
    [(Poly: ns (Function: arrs))
     (tc-error/expr
      (string-append "Cannot infer type instantiation for type ~a. Please add "
                     "more type annotations")
      f-type)]
    [_
     (tc-error/expr
      "Cannot apply expression of type ~a, since it is not a function type"
      f-type)]))
