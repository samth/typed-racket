#lang racket/base

(require (rename-in "../utils/utils.rkt" [infer infer-in]))
(require racket/match racket/list
         (only-in unstable/list list-update)
         (for-syntax racket/base syntax/parse)
         (contract-req)
         (rep type-rep filter-rep object-rep rep-utils)
         (utils tc-utils)
         (types tc-result resolve subtype filter-ops
                numeric-tower)
         (env type-env-structs lexical-env mvar-env update)
         (logic prop-ops)
         (rename-in (types abbrev)
                    [-> -->]
                    [->* -->*]
                    [one-of/c -one-of/c])
         (typecheck tc-metafunctions))

(provide with-lexical-env/extend-props 
         with-lexical-env/extend-types
         with-lexical-env/extend-types+aliases+props
         with-lexical-env/naive-extend-types
         env-extend-types
         env+props)


;; (define/cond-contract (update ...
;;    if you came here looking for update, it's now
;;    in proves/type-update and is called update-type,
;;    sorry =)



(define (env-extend-types env ids types)
  (define-values (ids/ts* pss) 
    (for/lists (ids/ts ps) 
      ([id (in-list ids)] [t (in-list types)])
      (let-values ([(t* ps) (extract-props-from-type id t #:int-bounds? #t)])
        (values (cons id t*) (cons (-filter t* (-id-path id)) ps)))))
  (cond
    [(for/or ([id/t (in-list ids/ts*)]) (type-equal? (cdr id/t) -Bottom))
     #f]
    [else 
     (define ps (apply append pss))
     (define new-env
       (env+props (naive-extend/id-types (lexical-env) ids/ts*)
                  ps))
     new-env]))


;; extend the environment with a list of propositions
;; Returns #f if anything becomes (U)
;; AMK: We also return the atoms? I'm sure there's a reason
;; but from the body of this function it's difficult to
;; understand why
(define (env+props env fs
                   #:return-atoms? [return-atoms? #f]
                   #:ignore-non-identifier-ids? [ingore-non-identifier-ids? #t])
  (let/ec exit*
    (define (exit)
      (if return-atoms?
          (exit* #f empty)
          (exit* #f)))

    (define (update-env/props env fs)
      ;; logically combine all propositions
      (define-values (props atoms slis) 
        (combine-props (apply append (map flatten-nested-props fs)) 
                       (env-props+SLIs env)
                       exit))
      
      ;; update the environment w/ known atomic facts
      (define-values (Γ* new-exposed-props)
        (for/fold ([Γ (replace-props env (append slis props))]
                   [new-ps '()])
                  ([f (in-list atoms)])
          (match f
            [(or (TypeFilter: ft (Path: _ x)) 
                 (NotTypeFilter: ft (Path: _ x)))
             (cond
               ;; don't update certain vars
               [(or (is-var-mutated? x)
                    (and ingore-non-identifier-ids?
                         (not (identifier-binding x))))
                (values Γ new-ps)]
               ;; otherwise, refine the type
               [else
                (define-values (Γ* newly-exposed-props)
                  (parameterize
                      ([current-orig-stx x])
                    (update-env/atom Γ f exit)))
                (values Γ* (append newly-exposed-props new-ps))])]
            [(or (TypeFilter: _ (? LExp? l))
                 (NotTypeFilter: _ (? LExp? l)))
             (define-values (Γ* newly-exposed-props)
               (update-env/atom Γ f exit))
             (values Γ* (append newly-exposed-props new-ps))]
            [_ (values Γ new-ps)])))
      
      (cond
        [(null? new-exposed-props)
         ;; simple/common case -- no new nested propositions were discovered
         ;; when refining types
         (if return-atoms?
             (values Γ* atoms)
             Γ*)]
        [else
         ;; we found some new propositions when we updated a type and it became
         ;; a refinement! we have to start over making sure to incorporate
         ;; the new facts
         (define-values (Γ** new-atoms)
           (update-env/props Γ* new-exposed-props))
         (if return-atoms?
             (values Γ** (append atoms new-atoms))
             Γ**)]))

    (update-env/props env fs)))

;; run code in an extended env and with replaced props. Requires the body to return a tc-results.
;; TODO make this only add the new prop instead of the entire environment once tc-id is fixed to
;; include the interesting props in its filter.
;; WARNING: this may bail out when code is unreachable
(define-syntax (with-lexical-env/extend-props stx)
  (define-splicing-syntax-class unreachable?
    (pattern (~seq #:unreachable form:expr))
    (pattern (~seq) #:with form #'(begin)))
  (syntax-parse stx
    [(_ ps:expr u:unreachable? . bodies)
     #'(let*-values ([(new-env atoms) (env+props (lexical-env) ps #:return-atoms? #t)])
         (if new-env
             (with-lexical-env new-env
               (add-unconditional-prop 
                (let () . bodies) 
                (apply -and (append atoms (env-SLIs new-env) (env-props new-env)))))
             ;; unreachable, bail out
             (let ()
               u.form
               (ret -Bottom))))]))



;; run code in an extended env and with replaced props. Requires the body to return a tc-results.
;; TODO make this only add the new prop instead of the entire environment once tc-id is fixed to
;; include the interesting props in its filter.
;; WARNING: this may bail out when code is unreachable
(define-syntax (with-lexical-env/extend-types stx)
  (define-splicing-syntax-class unreachable?
    (pattern (~seq #:unreachable form:expr)))
  (syntax-parse stx
    [(_ ids:expr types:expr u:unreachable? . bodies)
     #'(let ()
         (define-values (ids/ts* pss) 
           (for/lists (ids/ts ps) 
             ([id (in-list ids)] [t (in-list types)])
             (let-values ([(t* ps) (extract-props-from-type id t #:int-bounds? #t)])
               (values (cons id t*) (cons (-filter t* id) ps)))))
         (cond
           [(for/or ([id/t (in-list ids/ts*)]) 
              (type-equal? (cdr id/t) -Bottom))
            ;; unreachable, bail out
            u.form]
           [else
            (let*-values 
                ([(ps) (apply append pss)]
                 [(new-env atoms) (env+props (naive-extend/id-types (lexical-env) ids/ts*)
                                             ps
                                             #:return-atoms? #t)]
                 [(new-env) (and new-env
                                 (replace-props
                                  new-env
                                  (append atoms (env-props+SLIs new-env))))])
              (if new-env
                  (with-lexical-env 
                   new-env
                   (let () . bodies))
                  ;; unreachable, bail out
                  u.form))]))]))


;; run code in an extended env and with replaced props. Requires the body to return a tc-results.
;; TODO make this only add the new prop instead of the entire environment once tc-id is fixed to
;; include the interesting props in its filter.
;; WARNING: this may bail out when code is unreachable
(define-syntax (with-lexical-env/extend-types+aliases+props stx)
  (define-splicing-syntax-class unreachable?
    (pattern (~seq #:unreachable form:expr)))
  (syntax-parse stx
    [(_ ids:expr types:expr aliases:expr ps:expr u:unreachable? . bodies)
     #'(let*-values 
           ([(ids/ts* ids/als pss)
             (for/fold ([ids/ts null] [ids/als null] [pss null]) 
                       ([id (in-list ids)] [t (in-list types)] [o (in-list aliases)])
               (match o
                 [(not (? non-empty-obj?))
                  ;; no alias, so just record the type and props as usual
                  (define-values (t* ps*) (extract-props-from-type id t #:int-bounds? #t))
                  (values `((,id . ,t*) . ,ids/ts) 
                          ids/als
                          (cons ps* pss))]
                 [(Path: '() id*)
                  ;; id is aliased to an identifier
                  ;; record the alias relation *and* type of that alias id along w/ props
                  (define-values (t* ps*) (extract-props-from-type id* t #:int-bounds? #t))
                  (values `((,id* . ,t*) . ,ids/ts) 
                          `((,id . ,o) . ,ids/als)
                          (cons ps* pss))]
                 ;; standard aliasing, just record the type and the alias
                 [(? Path?)
                  (define-values (t* ps*) (extract-props-from-type o t #:int-bounds? #t))
                  (values ids/ts
                          `((,id . ,o) . ,ids/als)
                          (cons ps* pss))]
                 ;; aliasing a linear expression, we should record the lexp's type
                 [(? LExp? l)
                  (define-values (t* ps*) (extract-props-from-type l t #:int-bounds? #t))
                  (values ids/ts
                          `((,id . ,o) . ,ids/als)
                          (cons (cons (-is-type l t*) ps*) pss))]
                 [_ (int-err "unrecognized object! ~a" o)]))])
         (cond
           [(for/or ([id/t (in-list ids/ts*)]) (type-equal? (cdr id/t) -Bottom))
            ;; unreachable, bail out
            u.form]
           [else 
            (let*-values
                ([(all-ps) (apply append (cons ps pss))]
                 [(env) (naive-extend/id-types (lexical-env) ids/ts*)] 
                 [(env) (and env (extend/aliases env ids/als))]
                 [(new-env atoms) (if env (env+props env all-ps #:return-atoms? #t) (values #f '()))]
                 [(new-env) (and new-env 
                                 (replace-props new-env 
                                                (append atoms (env-props+SLIs new-env))))])
              (if new-env
                  (with-lexical-env new-env (let () . bodies))
                  ;; unreachable, bail out
                  (let () u.form)))]))]))



;; run code in an extended env
;; WARNING! does not reason about nested props in refinements
(define-syntax-rule (with-lexical-env/naive-extend-types ids types . b)
  (with-lexical-env (naive-extend/id-types (lexical-env) (map cons ids types)) . b))

