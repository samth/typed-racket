#lang racket/base

;; Provides functionality to take a static contract and turn it into a regular contract.

(require (for-template racket/base
                       racket/contract)
         racket/contract
         racket/list
         racket/match
         racket/syntax
         syntax/private/id-table
         "../utils/utils.rkt"
         "combinators.rkt"
         "combinators/case-lambda.rkt"
         "combinators/name.rkt"
         "combinators/parametric.rkt"
         "constraints.rkt"
         "equations.rkt"
         "kinds.rkt"
         "optimize.rkt"
         "parametric-check.rkt"
         "structures.rkt")

(provide static-contract-may-contain-free-ids?)

(provide/cond-contract
 [instantiate/optimize
     (parametric->/c (a) ((static-contract? (-> #:reason (or/c #f string?) a))
                          (contract-kind? #:cache (or/c #f hash?) #:trusted-positive boolean? #:trusted-negative boolean?)
                          . ->* . (or/c a (list/c (listof syntax?) syntax?))))]
 [instantiate
     (parametric->/c (a) ((static-contract? (-> #:reason (or/c #f string?) a))
                          (contract-kind? #:cache (or/c #f hash?) #:recursive-kinds (or/c hash? #f))
                          . ->* . (or/c a (list/c (listof syntax?) syntax?))))]
 [should-inline-contract? (-> syntax? boolean?)])

;; Providing these so that tests can work directly with them.
(module* internals #f
  (provide compute-constraints
           compute-recursive-kinds
           instantiate/inner))

;; A shared, expansion-time table of contracts that are defined once in
;; some module and can be referenced by an identifier instead of being
;; regenerated (and duplicated) in every module that needs them.
;;
;; The table maps (cons Type? typed-side?) -> identifier?, where the
;; identifier is bound (in that defining module's #%contract-defs
;; submodule) to the contract for that type.  This is its own module, so
;; every requirer shares a single mutable table.
(module predefined-contracts racket/base
  (define predef-contracts (make-hash))
  ;; (define/contract-decl id ctc key) binds `id` to the contract `ctc`
  ;; and registers `key` -> #'id in the shared table.
  (define-syntax-rule (define/contract-decl i ctc key)
    (begin (hash-set! predef-contracts key #'i)
           (define i ctc)))
  (provide predef-contracts define/contract-decl))

(define no-optimize-sc? (and (getenv "PLT_TR_NO_CONTRACT_OPTIMIZE") #t))

(define (instantiate/optimize sc fail [kind 'impersonator] #:cache [cache #f] #:trusted-positive [trusted-positive #f] #:trusted-negative [trusted-negative #f])
  (define recursive-kinds
    (with-handlers [(exn:fail:constraint-failure?
                    (lambda (exn)
                      ;; Even if the constraints for `sc` are unsolvable,
                      ;;  the optimizer might be able to reduce parts of
                      ;;  `sc` to give a contract with solvable constraints.
                      ;; This currently happens for the `Any-Syntax` type;
                      ;;  eventually that won't happen for `Any-Syntax`,
                      ;;  and at that point maybe we can fail here. -- Ben G.
                      #f))]
      (compute-recursive-kinds
        (contract-restrict-recursive-values (compute-constraints sc kind)))))
  (define sc/opt (if no-optimize-sc? sc (optimize sc #:trusted-positive trusted-positive #:trusted-negative trusted-negative #:recursive-kinds recursive-kinds)))
  (instantiate sc/opt fail kind #:cache cache #:recursive-kinds recursive-kinds))

;; kind is the greatest kind of contract that is supported, if a greater kind would be produced the
;; fail procedure is called.
;;
;; The cache is used to share contract definitions across multiple calls to
;; type->contract in a given contract fixup pass. If it's #f then that means don't
;; do any sharing (useful for testing).
(define (instantiate sc fail [kind 'impersonator] #:cache [cache #f] #:recursive-kinds [recursive-kinds #f])
  (if (parametric-check sc)
      (fail #:reason "multiple parametric contracts are not supported")
      (with-handlers [(exn:fail:constraint-failure?
                        (lambda (exn) (fail #:reason (exn:fail:constraint-failure-reason exn))))]
        (instantiate/inner sc
          (or recursive-kinds
              (compute-recursive-kinds
                (contract-restrict-recursive-values (compute-constraints sc kind))))
          cache))))

;; computes the definitions that are in / used by `sc`
;; `(get-all-name-defs)` is not what we want directly, since it also includes
;; definitions that were optimized away
;; we restrict it to only variables bound in `sc`
(define (compute-defs sc)
  (define all-name-defs (get-all-name-defs))
  ;; all-name-defs maps lists of ids to defs
  ;; we want to match if any id in the list matches
  (define (ref b) (for/first ([k/v (in-list all-name-defs)]
                              #:when (for/or ([k* (in-list (car k/v))])
                                       (free-identifier=? b k*)))
                    k/v))
  (define bound '())
  ;; ignores its second argument (variance, passed by sc-traverse)
  (let loop ([sc sc] [_ #f])
    (match sc
      [(name/sc: name*)
       (unless (member name* bound free-identifier=?)
         (set! bound (cons name* bound))
         ;; traverse what `name` refers to
         (define r (ref name*))
         ;; ref returns a rib, get the one definition we want
         (define target (for/first ([k (in-list (car r))]
                                    [v (in-list (cdr r))]
                                    #:when (free-identifier=? name* k))
                          v))
         (loop target #f))]
      [else (sc-traverse sc loop)]))
  (for*/hash ([b (in-list bound)]
              [v (in-value (ref b))]
              #:when v)
    (values (car v) (cdr v))))

(define (compute-constraints sc max-kind)
  (define memo-table (make-hash))
  (define name-defs (compute-defs sc))
  (define (recur sc)
    (cond [(hash-ref memo-table sc #f)]
          [else
           (define result
             (match sc
               [(recursive-sc names values body)
                (close-loop names (map recur values) (recur body))]
               [(? sc?)
                (sc->constraints sc recur)]))
           (hash-set! memo-table sc result)
           result]))
  (define constraints
    (cond
      [(hash-empty? name-defs)
       (recur sc)]
      [else
       (define keys+values (hash->list name-defs))
       (close-loop (apply append (map car keys+values))
                   (map recur (apply append (map cdr keys+values)))
                   (recur sc))]))
  (validate-constraints (add-constraint constraints max-kind))
  constraints)


(define (compute-recursive-kinds recursives)
  (define eqs (make-equation-set))
  (define vars
    (for/hash ([(name _) (in-free-id-table recursives)])
      (values name (add-variable! eqs 'flat))))

  (define (lookup id)
    (variable-ref (hash-ref vars id)))

  (for ([(name v) (in-free-id-table recursives)])
    (match-define (kind-max others max) v)
    (add-equation! eqs
                   (hash-ref vars name)
                   (λ ()
                     (apply combine-kinds
                            max
                            (for/list ([(id _) (in-free-id-table others)])
                              (lookup id))))))
  (define var-values (resolve-equations eqs))
  (for/hash ([(name var) (in-hash vars)])
    (values name (hash-ref var-values var))))


(define (instantiate/inner sc recursive-kinds cache)
  (define bound-names (make-parameter null))
  ;; sc-queue : records the order in which to return syntax objects
  (define sc-queue null)
  ;; top-level? is #t only for the first call and not for recursive
  ;; calls, which helps for inlining
  (define (recur sc [top-level? #f])
    (cond [(and cache (hash-ref cache sc #f)) => car]
          [(arr/sc? sc) (make-contract sc)]
          [(or (parametric->/sc? sc) (sealing->/sc? sc))
           (match-define (or (parametric->/sc: vars _)
                             (sealing->/sc: vars _ _))
                         sc)
           (parameterize ([bound-names (append vars (bound-names))])
             (make-contract sc))]
          ;; If any names are bound, the contract can't be shared
          ;; becuase it depends on the scope it's in
          [(ormap (λ (n) (name-free-in? n sc)) (bound-names))
           (make-contract sc)]
          [(static-contract-may-contain-free-ids?) (make-contract sc)]
          [else
           (define ctc (make-contract sc))
           (cond 
            ;; when a contract benefits from inlining
            ;; (e.g., ->) and this contract appears
            ;; directly in a define-module-boundary-contract
            ;; position (i.e, top-level? is #t) then
            ;; don't generate a new identifier for it
            [(or (should-inline-contract? ctc #:top-level? top-level?)
                 (not cache))
             ctc]
            [else
             (define fresh-id (generate-temporary))
             (hash-set! cache sc (cons fresh-id ctc))
             (set! sc-queue (cons sc sc-queue))
             fresh-id])]))
  (define (make-contract sc)
    (match sc
      [(recursive-sc names values body)
       (define raw-names (generate-temporaries names))
       (define raw-bindings
         (parameterize ([bound-names (append names (bound-names))])
           (for/list ([raw-name (in-list raw-names)]
                      [value (in-list values)])
             #`[#,raw-name #,(recur value)])))
       (define bindings
         (for/list ([name (in-list names)]
                    [raw-name (in-list raw-names)])
            #`[#,name (recursive-contract #,raw-name
                                            #,(kind->keyword
                                                (hash-ref recursive-kinds name)))]))
       #`(letrec (#,@bindings #,@raw-bindings)
           #,(parameterize ([bound-names (append names (bound-names))])
               (recur body)))]
      [(? sc? sc)
       (sc->contract sc recur)]))
  (define ctc (recur sc #t))
  (define name-defs (compute-defs sc))
  ;; These are extra contract definitions for the name static contracts
  ;; that are used for this type. Since these are shared across multiple
  ;; contracts from a single contract fixup pass, we use the name-defined
  ;; table to see if we've already defined it. If so, we avoid duplicating
  ;; the definition later.
  (define extra-defs
    (cond [(hash-empty? name-defs) null]
          [else
           (define names+values (hash->list name-defs))
           (define names (apply append (map car names+values)))
           (for/list ([name (in-list names)]
                      [sc   (in-list (apply append (map cdr names+values)))]
                      #:unless (lookup-name-defined name))
             (set-name-defined name)
             #`(define #,name
                 (recursive-contract #,(recur sc)
                                     #,(kind->keyword (hash-ref recursive-kinds name)))))]))
  (define all-defs
    (append ;; These contracts are sub-contract definitions used to
            ;; increase sharing among contracts in a given fixup pass
            extra-defs
            (for/list ([sc (in-list (reverse sc-queue))])
              (match-define (cons id ctc) (hash-ref cache sc))
              #`(define #,id #,ctc))))
  (if (canon-ids?)
      (let-values ([(defs* ctc*) (hashcons-defs all-defs ctc)]) (list defs* ctc*))
      (list all-defs ctc)))

;; M4: the per-sc cache misses structurally-identical recursive/object
;; contracts because recursive-sc/name temporaries are fresh per occurrence.
;; This post-pass merges definitions whose right-hand sides are equal modulo
;; renaming of the (generate-temporary) definition identifiers, rewriting all
;; references to the surviving representative.  Sound (the merge key is
;; binding-aware) and a consistent ~10-14% smaller, so it is on by default;
;; PLT_TR_NO_CANON_IDS disables it.
(define (canon-ids?) (not (getenv "PLT_TR_NO_CANON_IDS")))

(define (hashcons-defs defs ctc)
  ;; def-id symbols are unique generate-temporary outputs
  (define entries
    (for/list ([d (in-list defs)])
      (define parts (syntax->list d))   ; (define <id> <rhs>)
      (define i (cadr parts))
      (cons (syntax-e i) (cons i (caddr parts)))))
  (define def-syms (for/hasheq ([e (in-list entries)]) (values (car e) #t)))
  (define rhs-of   (for/hasheq ([e (in-list entries)]) (values (car e) (cddr e))))
  (define id-of    (for/hasheq ([e (in-list entries)]) (values (car e) (cadr e))))
  (define order    (map car entries))
  (define canon (make-hasheq))
  (for ([s (in-list order)]) (hash-set! canon s s))
  ;; binding-aware key for a non-def identifier, so two same-symbol but
  ;; different-binding identifiers (e.g. like-named predicates from different
  ;; modules) are NOT treated as equal — keeping the merge sound.
  (define (id->key x)
    (define b (identifier-binding x))
    (cond [(list? b)
           (vector 'id (resolved-module-path-name
                        (module-path-index-resolve (car b)))
                   (cadr b))]
          [else (vector 'lex (syntax-e x))]))
  ;; structural key of a def's rhs, with def-refs replaced by their current rep
  (define (key-of s)
    (let recur ([x (hash-ref rhs-of s)])
      (cond [(identifier? x)
             (define sym (syntax-e x))
             (if (hash-ref def-syms sym #f) (vector 'ref (hash-ref canon sym)) (id->key x))]
            [(syntax? x) (recur (syntax-e x))]
            [(pair? x) (cons (recur (car x)) (recur (cdr x)))]
            [(vector? x) (vector 'v (map recur (vector->list x)))]
            [(null? x) '()]
            [else x])))
  ;; fixpoint: collapse defs with equal keys to a single representative
  (let loop ()
    (define seen (make-hash))
    (define changed #f)
    (for ([s (in-list order)])
      (define k (key-of s))
      (define rep (hash-ref seen k (lambda () (hash-set! seen k s) s)))
      (unless (eq? (hash-ref canon s) rep)
        (hash-set! canon s rep) (set! changed #t)))
    (when changed (loop)))
  ;; rewrite references (in surviving defs and the top contract) to reps,
  ;; preserving the original syntax (and thus bindings) elsewhere
  (define (rewrite stx)
    (cond
      [(identifier? stx)
       (define sym (syntax-e stx))
       (if (and (hash-ref def-syms sym #f) (not (eq? (hash-ref canon sym) sym)))
           (hash-ref id-of (hash-ref canon sym))
           stx)]
      [(syntax? stx)
       (define e (syntax-e stx))
       (if (pair? e) (datum->syntax stx (rewrite-seq e) stx stx) stx)]
      [else stx]))
  (define (rewrite-seq e)
    (cond [(pair? e) (cons (rewrite (car e)) (rewrite-seq (cdr e)))]
          [(syntax? e) (rewrite e)]
          [(null? e) '()]
          [else e]))
  (define kept-defs
    (for/list ([s (in-list order)] #:when (eq? (hash-ref canon s) s))
      #`(define #,(hash-ref id-of s) #,(rewrite (hash-ref rhs-of s)))))
  (values kept-defs (rewrite ctc)))

;; Determine whether the given contract syntax should be inlined or
;; not.  if top-level? is true, we inline functions because the
;; contract system treats them specially. Otherwise, always inline
;; simple things.
(define (should-inline-contract? stx #:top-level? [top-level? #f])
  (or
   (syntax-case stx (quote) [(quote _) #t] [_ #f])
   ;; no need to generate an extra def for things that are already identifiers
   (identifier? stx)
   ;; ->* are handled specially by the contract system
   (let ([sexp (syntax-e stx)])
     (and top-level?
          (pair? sexp)
          (or (free-identifier=? (car sexp) #'->)
              (free-identifier=? (car sexp) #'->*))))))

;; determine if a given name is free in the sc
(define (name-free-in? name sc)
  (let/ec escape
    (define/match (free? sc _)
      [((or (recursive-sc-use name*)
            (parametric-var/sc: name*)
            (sealing-var/sc: name*)
            (name/sc: name*))
        _)
       (when (free-identifier=? name name*)
         (escape #t))]
      [(_ _) (sc-traverse sc free?)])
    (free? sc 'dummy)
    #f))
