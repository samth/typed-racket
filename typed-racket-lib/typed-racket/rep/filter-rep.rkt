#lang racket/base

;;TODO use contract-req
(require "../utils/utils.rkt"
         "rep-utils.rkt" "object-rep.rkt"
         "free-variance.rkt" "fme.rkt"
         racket/contract/base
         racket/match racket/dict
         racket/list racket/fixnum
         racket/lazy-require racket/set
         racket/function racket/stream
         (for-syntax racket/base)
         (utils tc-utils))

;; TODO use something other than lazy-require.
(lazy-require ["type-rep.rkt" (Type/c Univ? Bottom?)]
              ["../types/filter-ops.rkt" (-or)])


(provide Filter/c FilterSet/c name-ref/c hash-name filter-equal?
         SLI?
         SLI-try-join
         SLI-satisfiable?
         SLI-implies?
         SLIs-imply?
         conservative-complementary-SLIs?
         SLI-paths
         add-SLI
         add-SLIs
         SLI-path-map
         SLI->sexp
         SLI-negate
;         SLI-leq-pairs: TODO used for serialization
         *Top
         equals-constant-SLI?
         SLIs-contain?
         conservative-contradictory-SLIs?
         ;; the rest of the world doesn't know about 'Leq' vs 'leq'...
         ;; so they can just keep talking about leqs
         -leq
         (rename-out [Leq? leq?]
                     [Leqs->SLIs leqs->SLIs]
                     [SLI:* SLI:]
                     [Leq-negate leq-negate])
         SLI->lexp-pairs)

(define (Filter/c-predicate? e)
  (and (Filter? e) (not (NoFilter? e)) (not (FilterSet? e))))
(define Filter/c (flat-named-contract 'Filter Filter/c-predicate?))

(define FilterSet/c
  (flat-named-contract
   'FilterSet
   (λ (e) (or (FilterSet? e) (NoFilter? e)))))

;; A Name-Ref is any value that represents an object.
;; As an identifier, it represents a free variable in the environment
;; As a list, it represents a De Bruijn indexed bound variable
(define name-ref/c (or/c identifier? (list/c integer? integer?)))
(define (hash-name v) (if (identifier? v) (hash-id v) (list v)))

(define ((length>=/c len) l)
  (and (list? l)
       (>= (length l) len)))

(def-filter Bot () [#:fold-rhs #:base])
(def-filter Top () [#:fold-rhs #:base])

(define -bot (*Bot))
(define -top (*Top))

(def-filter TypeFilter ([t (and/c Type/c (not/c Univ?) (not/c Bottom?))] [p (or/c LExp? Path?)])
  [#:intern (list (Rep-seq t) (Rep-seq p))]
  [#:frees (λ (f) (combine-frees (map f (list t p))))]
  [#:fold-rhs (*TypeFilter (type-rec-id t) (object-rec-id p))])

(def-filter NotTypeFilter ([t (and/c Type/c (not/c Univ?) (not/c Bottom?))] [p (or/c LExp? Path?)])
  [#:intern (list (Rep-seq t) (Rep-seq p))]
  [#:frees (λ (f) (combine-frees (map f (list t p))))]
  [#:fold-rhs (*NotTypeFilter (type-rec-id t) (object-rec-id p))])

;; implication
(def-filter ImpFilter ([a Filter/c] [c Filter/c]))

(define-struct/cond-contract Leq ([ps immutable-path-set?]
                                  [exp leq?])
  #:transparent)

;; internal smart builder -- it normalizes the constant
;; so one side has a const of 0
;; NOTE: leq-negate does this as well, no need to double stack
(define (leq* lhs rhs)
  (match* (lhs rhs)
    [((lexp: const-l terms-l) (lexp: const-r terms-r))
     (cond
       [(= const-l const-r)
        (leq (lexp 0 terms-l) (lexp 0 terms-r))]
       [(< const-l const-r)
        (leq (lexp 0 terms-l) (lexp (- const-r const-l) terms-r))]
       [else
        (leq (lexp (- const-l const-r) terms-l) (lexp 0 terms-r))])]
    [(_ _) (int-err "leq* given invalid arg(s) ~a ~a" lhs rhs)]))

;; constructor for the outside world
;; (since they'll be constructing LExps
;;  but leqs use the lighter weight lexp representation
;; defined in fme.rkt and used internally by LExps)
(define/cond-contract (-leq lhs rhs)
  (-> LExp? LExp? Leq?)
  (match* (lhs rhs)
    [((LExp-raw: ps-l exp-l)
      (LExp-raw: ps-r exp-r))
     (Leq (set-union ps-l ps-r)
          (leq* exp-l exp-r))]
    [(_ _) (int-err "-leq: invalid lexp(s) ~a ~a" lhs rhs)]))

(define/cond-contract (Leq-negate ineq)
  (-> Leq? Leq?)
  (match ineq
    [(Leq ps ineq)
     (Leq ps (leq-negate ineq))]
    [_ (int-err "invalid Leq for Leq-negate ~a" ineq)]))

(define/cond-contract (try-simplify-Leq inequality)
  (-> Leq? (or/c Leq? Top? Bot?))
  (match inequality
    [(Leq ps ineq)
     (cond
       [(leq-trivially-valid? ineq) -top]
       [(leq-trivially-invalid? ineq) -bot]
       [else inequality])]))

;; check that every path in an sli (sys)
;; is actually in the path set (ps)
(define (well-formed-paths+sys ps sys)
  (define p-set (for/seteq ([p (in-set ps)])
                           (Obj-seq p)))
  (define (valid-lexp? l)
    (match l
      [(lexp: _ terms)
       (for/and ([key (in-hash-keys terms)])
         (set-member? p-set key))]))
  
  (for/and ([ineq (in-set sys)])
        (match ineq
          [(leq: lhs rhs)
           (and (valid-lexp? lhs)
                (valid-lexp? rhs))])))

;;******************************************************************************
;; System of Linear Inequalities (and related ops)
(def-filter SLI ([paths (and/c immutable-path-set?
                               (not/c set-empty?))]
                 [sys (and/c sli? (not/c set-empty?))])
  #:no-provide
  [#:intern sys]
  [#:frees (λ (f) (combine-frees (set-map paths f)))]
  [#:fold-rhs (internal-sli-path-map object-rec-id paths sys)])


(define-match-expander SLI:*
  (lambda (stx)
    (syntax-case stx ()
      [(_ sli)
       #'(? SLI? sli)])))

(define/cond-contract (SLI-path-map f sli)
  (-> (-> Path? Object?) SLI? Filter?)
  (match sli
    [(SLI: paths sys)
     (internal-sli-path-map f paths sys)]
    [_ (int-err "invalid SLI? to SLI-path-map: ~a" sli)]))

(define/cond-contract (internal-sli-path-map f paths orig-system)
  (-> (-> Path? Object?) immutable-path-set? sli?
      Filter?)
  ;; calculate changes
  (define-values (path->path-map
                  path->lexp-map
                  elim-keys
                  new-path-set)
    (for/fold ([path->path (hasheq)]
               [path->lexp (hasheq)]
               [elim-keys null]
               [new-path-set empty-path-set])
              ([p (in-set paths)])
      (define p-key (Obj-seq p))
      (match (f p)
        [(? Empty?)
         (values path->path
                 path->lexp
                 (cons p-key elim-keys)
                 new-path-set)]
        [(? Path? p*)
         (values (if (= p-key (Obj-seq p*))
                     path->path
                     (hash-set path->path p-key (Obj-seq p*)))
                 path->lexp
                 elim-keys
                 (set-add new-path-set p*))]
        [(LExp-raw: l-ps exp)
         (values path->path
                 (hash-set path->lexp p-key exp)
                 elim-keys
                 (set-union new-path-set l-ps))]
        [o (int-err "unknown object from function in SLI-map ~a" o)])))
  ;; perform FM-elimination for all paths that were mapped to Empty
  (define system-w/o-empties
    (reduce-sli (for/fold ([sys orig-system])
                          ([p (in-list elim-keys)])
                  (fme-elim sys p))))
  ;; define a function which tests if the lexp needs updated
  ;; logic similar to LExp-path-map related functions on rep/object-rep.rkt
  (define (update-lexp linear-expression)
    (match linear-expression
     [(lexp: const terms)
      (define-values (const* terms*)
        (for/fold ([const const]
                   [terms terms])
                  ([orig-key (in-hash-keys terms)])
          (cond
            ;; orig-key is now a new path -- remove the old,
            ;; put in the new w/ the same coeff
            [(hash-ref path->path-map orig-key #f)
             => (λ (new-key)
                  (values const
                          (terms-set (terms-remove terms orig-key)
                                     new-key
                                     (terms-ref terms orig-key 0))))]
            ;; orig-key is now a linear expression -- scale it by
            ;; the old coeff and add it to the const and terms
            [(hash-ref path->lexp-map orig-key #f)
             => (λ (new-lexp)
                  (define old-key-coeff (terms-ref terms orig-key 0))
                  (match new-lexp
                    [(lexp: p*-const p*-terms)
                     (values (+ const (* old-key-coeff p*-const))
                             (terms-plus (terms-remove terms orig-key)
                                         (terms-scale p*-terms old-key-coeff)))]
                    [_ (int-err "invalid new-lexp in path->lexp-map. lexp: ~a, map: ~a"
                                new-lexp path->lexp-map)]))]
            ;; this term was unchanged
            [else (values const terms)])))
      ;; if we didn't change the linear-expression return the original
      ;; else build the new one
      (if (and (eq? const const*)
               (eq? terms terms*))
          linear-expression
          (lexp const* terms*))]
      [_ (int-err "update-lexp: invalid lexp ~a" linear-expression)]))

  (cond
    ;; no changes effected this system 
    [(and (null? elim-keys)
          (hash-empty? path->path-map)
          (hash-empty? path->lexp-map))
     (*SLI paths orig-system)]
    ;; there were changes, we must update the system
    [else
     (define system*
       (reduce-sli
        (for/fold ([sys system-w/o-empties])
                  ([inequality (in-set system-w/o-empties)])
          ;; update each inequality individually
          (match inequality
            [(leq: lhs rhs)
             (define lhs* (update-lexp lhs))
             (define rhs* (update-lexp rhs))
             ;; if it wasn't changed, leave the system be
             ;; for this iteration
             (if (and (eq? lhs lhs*) (eq? rhs rhs*))
                 sys
                 ;; otherwise remove the old inequality
                 ;; and put the new one in
                 (set-add (set-remove sys inequality)
                          (leq* lhs* rhs*)))]
            [_ (int-err "system*-def: invalid inequality ~a" inequality)]))))
     (cond
       [(not system*) -bot]
       [(sli-trivially-valid? system*)
        -top]
       [(not (fme-sat? system*))
        -bot]
       [else
        (*SLI new-path-set
              system*)])]))

(define (set-overlap? s1 s2)
  (for/or ([a (in-set s1)])
    (set-member? s2 a)))

;; SLI-try-join
;; combine two SLIs if they share any paths
;; if they don't, return #f
(define/cond-contract (SLI-try-join s1 s2)
  (-> SLI? SLI? (or/c #f  SLI? Top? Bot?))
  (match* (s1 s2)
    [((SLI: ps1 sli1) (SLI: ps2 sli2))
     (cond 
       [(set-overlap? ps1 ps2)
        (define system* (sli-union/sat? sli1 sli2))
        (cond
          [(not system*) -bot]
          [(sli-trivially-valid? system*)
           -top]
          [else
           (define ps* (filter-path-set/sys (set-union ps1 ps2) system*))
           (*SLI ps* system*)])]
       [else #f])]
    [(_ _) (int-err "invalid SLI(s) to SLI-try-join: ~a ~a" s1 s2)]))

(define (SLI-empty? s)
  (set-empty? (SLI-sys s)))

(define (terms-contains-path-key? terms p-key)
  (and (terms-ref terms p-key #f) #t))

;; does an leq's paths overlap with an SLI's paths?
  ;; !curried! takes an leq, returns a function to call on SLIs
(define (leq/SLI-overlap? l)
  (match l
    [(leq: (lexp: _ lhs-terms) (lexp: _ rhs-terms))
     (λ (sys)
       (for/or ([p (in-set (SLI-paths sys))])
         (or (terms-contains-path-key? lhs-terms (Obj-seq p))
             (terms-contains-path-key? rhs-terms (Obj-seq p)))))]
    [_ (int-err "leq/SLI-overlap?: invalid leq ~a" l)]))

(define (system-contains-path? sys path)
  (define p-key (Obj-seq path))
  (for/or ([ineq (in-set sys)])
    (match ineq
      [(leq: (lexp: _ lhs-terms) (lexp: _ rhs-terms))
       (or (terms-contains-path-key? lhs-terms p-key)
           (terms-contains-path-key? rhs-terms p-key))]
      [_ (int-err "leq/SLI-overlap?: invalid leq ~a" ineq)])))

;;; takes a list of leqs and builds
;;; the proper disjoint SLIs
;;; takes a list of leqs and builds
;;; the proper disjoint SLIs
(define/cond-contract (Leqs->SLIs initial-inequalities)
  (-> (listof Leq?) (listof (or/c SLI? Top? Bot?)))
  
  (define initial-Leqs
    (let loop ([to-do initial-inequalities]
               [ineqs null])
      (cond
        [(null? to-do)
         (if (empty? ineqs)
             -top
             ineqs)]
        [else
         (match (try-simplify-Leq (car to-do))
           [(? Top?) (loop (cdr to-do) ineqs)]
           [(? Bot?) -bot]
           [l (loop (cdr to-do) (cons l ineqs))])])))
  
  (cond
    [(not (list? initial-Leqs))
     (list initial-Leqs)]
    [else
     ;; create an SLI by joining the list of SLIs and adding the leq
     ;; don't consider any details/satisfiability etc, just merge
     (define (naive-merge-SLIs+Leq SLIs ineq)
       (match-define (Leq l-ps l-exp) ineq)
       (cond
         [(pair? SLIs)
          (define-values (ps sys)
            (for/fold ([paths (SLI-paths (car SLIs))]
                       [system (SLI-sys (car SLIs))])
                      ([S (in-list (cdr SLIs))])
              (match S
                [(SLI: ps sys)
                 (values (set-union paths ps)
                         (set-union system sys))]
                [_ (int-err "invalid SLI in naive-merge-SLIs: ~a" S)])))
          (*SLI (set-union ps l-ps)
                (set-add sys l-exp))]
         [else
          (*SLI l-ps (set l-exp))]))
     
     ;; build the various SLIs based on overlap
     (define SLI-list
       (for/fold ([SLI-list null])
                 ([ineq (in-list initial-Leqs)])
         (define-values (related-SLIs unrelated-SLIs)
           (partition (leq/SLI-overlap? (Leq-exp ineq)) SLI-list))
         (define joined-SLI (naive-merge-SLIs+Leq related-SLIs ineq))
         (cons joined-SLI unrelated-SLIs)))
     
     ;; now just simplify (if needed) the list of SLIs
     (for/list ([sli (in-list SLI-list)])
       (match-define (SLI: ps sys) sli)
       (let ([sys (reduce-sli/sat? sys)])
         (cond
           [(not sys) -bot]
           [(sli-trivially-valid? sys) -top]
           ;; okay, we're keeping it. filter out paths that
           ;; aren't there anymore
           [else (*SLI (filter-path-set/sys ps sys)
                       sys)])))]))

(define (filter-path-set/sys ps sys)
  (for/fold ([ps ps])
            ([p (in-set ps)])
    (if (system-contains-path? sys p)
        ps
        (set-remove ps p))))

(define/cond-contract (SLI-satisfiable? sli)
  (-> SLI? boolean?)
  (fme-sat? (SLI-sys sli)))

;; complementary-SLIs?
;; two SLIs s1 and s2 are complimentary iff
;; ~s1 --> s2  and  ~s2 --> s1
;; (i.e. just prove the Or of the two is a tautology)
(define/cond-contract (conservative-complementary-SLIs? s1 s2)
  (-> SLI? SLI? boolean?)
  (match-define (SLI: ps1 sys1) s1)
  (match-define (SLI: ps2 sys2) s2)
  
  (and
   (equal? ps1 ps2)
   (= 1 (set-count sys1) (set-count sys2))
   ;; s2 --> ~s1?
   (fme-imp-leq? (set (leq-negate (set-first sys1))) (set-first sys2))
   ;; s1 --> ~s2?
   (fme-imp-leq? (set (leq-negate (set-first sys2))) (set-first sys1))))

;; tests if the SLI is stating some Path is
;; equal to some exact integer, returning #f
;; if not or the exact integer if it is
(define/cond-contract (equals-constant-SLI? s)
  (-> SLI? (or/c #f exact-integer?))
  (match-define (SLI: paths sys) s)
  (cond
    [(not (= 2 (set-count sys)))
     #f]
    [(not (= 1 (set-count paths)))
     #f]
    [else
     (match-define (list ineq1 ineq2) (set->list sys))
     (define p (set-first paths))
     (match* (ineq1 ineq2)
      [((leq: lhs1 rhs1) (leq: lhs2 rhs2))
       (cond
         [(let ([c-l1 (constant-lexp? lhs1)]
                [simp1? (simple-lexp? rhs1)]
                [simp2? (simple-lexp? lhs2)]
                [c-r2 (constant-lexp? rhs2)])
            (and c-l1 simp1? simp2? c-r2
                 (= c-l1 c-r2)
                 c-r2))]
         [(let ([c-r1 (constant-lexp? rhs1)]
                [simp1? (simple-lexp? lhs1)]
                [simp2? (simple-lexp? rhs2)]
                [c-r2 (constant-lexp? lhs2)])
            (and c-r1 simp1? simp2? c-r2
                 (= c-r1 c-r2)
                 c-r2))]
         [else #f])]
       [(_ _) (int-err "equals-constant-SLI?:invalid ineq(s) ~a ~a" ineq1 ineq2)])]))


;; ======== SLI cache -- DO NOT TOUCH PLZ ========
(define SLI-cache (make-hasheq))
(define (cache-answer->bool ans)
  (match ans
    ['yes #t]
    ['no #f]))
(define (SLI-cached? P Q)
  (cond
    [(hash-ref SLI-cache (Rep-seq P) #f)
     => (λ (P-cache)
          (hash-ref P-cache (Rep-seq Q) #f))]
    [else #f]))
(define (SLI-cache-set! P Q ans)
  (when (> 25 (hash-count SLI-cache))
    (set! SLI-cache (make-hasheq)))
  (define Pkey (Rep-seq P))
  (cond
    [(hash-ref SLI-cache Pkey #f)
     => (λ (P-cache)
          (hash-set! P-cache (Rep-seq Q) (if ans 'yes 'no)))]
    [else
     (define P-cache (make-hasheq))
     (hash-set! P-cache (Rep-seq Q) (if ans 'yes 'no))
     (hash-set! SLI-cache Pkey P-cache)]))
;; ========= END OF SLI cache ========

(define/cond-contract (SLI-implies? sli1 sli2)
  (-> SLI? SLI? boolean?)
  (cond
    [(SLI-cached? sli1 sli2)
     => cache-answer->bool]
    [else
     (let ([imp? (fme-imp? (SLI-sys sli1) 
                           (SLI-sys sli2))])
       (SLI-cache-set! sli1 sli2 imp?)
       imp?)]))

(define/cond-contract (SLIs-imply? slis goal)
  (-> (listof SLI?) SLI? boolean?)
  (match-define (SLI: goal-ps goal-sys) goal)
  
  (define axiom-sys
    (for/fold ([system #f])
              ([sli (in-list slis)])
      (match-define (SLI: ps sys) sli)
      (cond
        [(set-overlap? goal-ps ps)
         (if system
             (set-union system sys)
             sys)]
        [else system])))

  (and axiom-sys
       (not (set-empty? axiom-sys))
       (fme-imp? axiom-sys goal-sys)))

(define/cond-contract (SLIs-contain? slis s)
  (-> (listof SLI?) SLI? boolean?)
  (set-empty?
   (for/fold ([s-sys (SLI-sys s)])
             ([sli (in-list slis)])
     (set-subtract s-sys (SLI-sys sli)))))


(define/cond-contract (add-SLI new-sli slis)
  (-> SLI? (listof SLI?) (or/c Bot? (listof SLI?)))
  (match slis
    [(list) (list new-sli)]
    [(cons sli slis*)
     (match (SLI-try-join new-sli sli)
       [#f (match (add-SLI new-sli slis*)
             [(? list? l) (cons sli l)]
             [(? Bot? b) b])]
       [(? SLI? new-s) (cons new-s slis*)]
       [(? Top?) slis*]
       [(? Bot? b) b])]))

(define/cond-contract (add-SLIs new-slis slis)
  (-> (listof SLI?) (listof SLI?) (or/c Bot? (listof SLI?)))
  (for/fold ([accumulation slis])
            ([new-sli (in-list new-slis)])
    #:break (Bot? accumulation)
    (add-SLI new-sli accumulation)))


(define (conservative-contradictory-SLIs? s1 s2)
  (match-let ([(SLI: _ sys1) s1]
              [(SLI: _ sys2) s2])
    (not (sli-union sys1 sys2))))

(define (SLI->sexp s Path->sexp)
  (match s
    [(SLI: ps sys)
     ;; build a function which converts Path-seq's to sexp
     (define path-key->sexp
       (let ([h (for/hasheq ([p (in-set ps)])
                  (values (Obj-seq p) (Path->sexp p)))])
         (λ (p) (hash-ref h p (λ _ (error 'SLI->sexp "path not in hash! ~a" p))))))
     ;; build a function that turns lexp's into sexps
     (define (lexp->sexp l)
       (match l
        [(lexp: c terms)
         (define terms-sexp
           (let ([terms-sexp
                  (for/list ([(p-key p-coeff) (in-hash terms)])
                    (if (= 1 p-coeff)
                        (path-key->sexp p-key)
                        `(* ,p-coeff ,(path-key->sexp p-key))))])
             (if (zero? c) terms-sexp (cons c terms-sexp))))
         (cond
           [(null? terms-sexp) 0] ;; not possible?
           [(null? (cdr terms-sexp)) (car terms-sexp)] ;; just one term, no '+'
           [else (cons '+ terms-sexp)])]
         [_ (int-err "lexp->sexp: invalid lexp ~a" l)]))
     ;; separate out equalities (pairs of inverted leqs) and regular leqs
     ;; TODO?? -- add const normalization to leqs (ONLY if printing and other operations
     ;; turn out to be a pain without it)
     (define-values (eqs leqs)
       (for/fold ([eqs (set)]
                  [leqs (set)])
                 ([ineq (in-set sys)])
         (define inv-ineq (leq-negate ineq))
         (cond
           [(set-member? leqs inv-ineq)
            (values (set-add eqs ineq)
                    (set-remove leqs inv-ineq))]
           [(set-member? eqs inv-ineq)
            (values eqs leqs)]
           [else (values eqs (set-add leqs ineq))])))
     
     (append
      (for/list ([ineq (in-set eqs)])
        (match ineq
          [(leq: lhs rhs) `(= ,(lexp->sexp lhs) ,(lexp->sexp rhs))]
          [_ (int-err "equality-ineqs->sexp: invalid ineq ~a" ineq)]))
      (for/list ([ineq (in-set leqs)])
        (match ineq
         [(leq: lhs rhs) `(≤ ,(lexp->sexp lhs) ,(lexp->sexp rhs))]
         [_ (int-err "ineqs->sexp: invalid ineq ~a" ineq)])))]
    [_ (int-err "invalid SLI given to SLI->sexp: ~a" s)]))

;; used for serialization (I think...)
(define (SLI->lexp-pairs sli)
  (unless (SLI? sli)
    (int-err "SLI->Leqs: invalid SLI for serialization ~a" sli))
  
  (match-define (SLI: ps sys) sli)

  (define (lookup p-key)
    (for/or ([p (in-set ps)])
      (and (= p-key (Obj-seq p))
           p)))

  (define (lexp->LExp exp)
    (match exp
      [(lexp: const terms)
       (apply -lexp (cons const (for/list ([(key coeff) (in-hash terms)])
                                  (list coeff (lookup key)))))]
      [_ (int-err "invalid exp to convert ~a" exp)]))
  (define (leq->lexp-pairs ineq)
    (match ineq
      [(leq: lhs rhs) (cons (lexp->LExp lhs) (lexp->LExp rhs))]
      [_ (int-err "invalid exp to convert ~a" exp)]))

  (set-map sys leq->lexp-pairs))


(define/cond-contract (SLI-negate sli)
  (-> SLI? Filter?)
  (match sli
    [(SLI: ps sys)
     (apply -or
            (for/list ([ineq (in-set sys)])
              (define sys* (set (leq-negate ineq)))
              (cond
                [(sli-trivially-valid? sys*)
                 -top]
                [(not (fme-sat? sys*))
                 -bot]
                [else
                 (match (set-first sys*)
                   [(leq: (lexp: _ termsl) (lexp: _ termsr))
                    (define ps* (for/fold ([new-ps empty-path-set])
                                          ([p (in-set ps)])
                                  (if (or (terms-ref termsl (Obj-seq p) #f)
                                          (terms-ref termsr (Obj-seq p) #f))
                                      (set-add new-ps p)
                                      new-ps)))
                    (*SLI ps* sys*)]
                   [_ (int-err "SLI-negate: oops, set had bad elem? ~a" sys*)])])))]
    [_ (int-err "SLI-negate given invalid SLI?: ~a" sli)]))


;;***************************************************************************
;; Or, And, FilterSet, NoFilter

(def-filter OrFilter ([fs (and/c (length>=/c 2)
                                 (listof (or/c TypeFilter? NotTypeFilter? SLI?)))])
  [#:intern (map Rep-seq fs)]
  [#:fold-rhs (*OrFilter (map filter-rec-id fs))]
  [#:frees (λ (f) (combine-frees (map f fs)))])


(def-filter AndFilter ([fs (and/c (length>=/c 2)
                                  (listof (or/c OrFilter? TypeFilter? NotTypeFilter? ImpFilter? SLI?)))])
  [#:intern (map Rep-seq fs)]
  [#:fold-rhs (*AndFilter (map filter-rec-id fs))]
  [#:frees (λ (f) (combine-frees (map f fs)))])

(def-filter FilterSet ([thn Filter/c] [els Filter/c])
  [#:fold-rhs (*FilterSet (filter-rec-id thn) (filter-rec-id els))])

;; represents no info about the filters of this expression
;; should only be used for parsing type annotations and expected types
(def-filter NoFilter () [#:fold-rhs #:base])

(define (filter-equal? a b) (= (Rep-seq a) (Rep-seq b)))
