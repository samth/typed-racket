#lang racket/base

(require "../utils/utils.rkt"
         racket/list racket/match
         racket/lazy-require ;racket/trace
         (prefix-in c: (contract-req))
         (rep type-rep filter-rep object-rep rep-utils)
         (env type-env-structs)
         (types union subtype remove-intersect abbrev tc-result restrict))
(provide/cond-contract
  [-and (c:->* () #:rest (c:listof Filter/c) Filter/c)]
  [-or (c:->* () #:rest (c:listof Filter/c) Filter/c)]
  [-imp (c:-> Filter/c Filter/c Filter/c)]
  [implied-atomic? (c:-> Filter/c Filter/c boolean?)]
  [complementary? (c:-> Filter/c Filter/c boolean?)]
  [contradictory? (c:-> Filter/c Filter/c boolean?)]
  [add-unconditional-filter-all-args (c:-> Function? Type/c Function?)]
  [add-unconditional-prop (c:-> tc-results/c Filter/c tc-results/c)]
  [erase-filter (c:-> tc-results/c tc-results/c)]
  [name-ref=? (c:-> name-ref/c name-ref/c boolean?)]
  [invert-filter (c:-> Filter/c Filter/c)])

(define (atomic-filter? p)
  (or (TypeFilter? p) 
      (NotTypeFilter? p)
      (Top? p) (Bot? p)))

;; contradictory: Filter/c Filter/c -> boolean?
;; Returns true if the AND of the two filters is equivalent to Bot
(define (contradictory? f1 f2)
  (match* (f1 f2)
    [((TypeFilter: t1 p) (NotTypeFilter: t2 p))
     (subtype t1 t2 #:env empty-env)]
    [((NotTypeFilter: t2 p) (TypeFilter: t1 p))
     (subtype t1 t2 #:env empty-env)]
    [((TypeFilter: t1 p) (TypeFilter: t2 p))
     (not (overlap t1 t2))]
    [((Bot:) _) #t]
    [(_ (Bot:)) #t]
    [((? SLI? s1) (? SLI? s2))
     (Bot? (SLI-try-join s1 s2))]
    [(_ _) #f]))

;; complementary: Filter/c Filter/c -> boolean?
;; Returns true if the OR of the two filters is equivalent to Top
(define (complementary? f1 f2)
  (match* (f1 f2)
    [((TypeFilter: t1 p) (NotTypeFilter: t2 p))
     (subtype t2 t1 #:env empty-env)]
    [((NotTypeFilter: t2 p) (TypeFilter: t1 p))
     (subtype t2 t1 #:env empty-env)]
    [((Top:) (Top:)) #t]
    [((? SLI? s1) (? SLI? s2)) (complementary-SLIs? s1 s2)]
    [(_ _) #f]))
(define (name-ref=? a b)
  (or (equal? a b)
      (and (identifier? a)
           (identifier? b)
           (free-identifier=? a b))))

;; is f1 implied by f2?
(define (implied-atomic? f1 f2)
  (match* (f1 f2)
    [(_ _) #:when (= (Rep-seq f1) (Rep-seq f2)) #t]
    [((Top:) _) #t]
    [(_ (Bot:)) #t]
    [((? SLI? Q) (? SLI? P))
     (SLI-implies? P Q)]
    [((OrFilter: ps) (OrFilter: qs))
     (for/and ([q (in-list qs)])
       (for/or ([p (in-list ps)])
         (implied-atomic? p q)))]
    [((OrFilter: fs) f2)
     (for/or ([f (in-list fs)])
       (implied-atomic? f f2))]
    [(f1 (AndFilter: fs))
     (for/or ([f (in-list fs)])
       (implied-atomic? f1 f))]
    [((TypeFilter: t1 p) (TypeFilter: t2 p))
     (subtype t2 t1 #:env empty-env)]
    [((NotTypeFilter: t2 p) (NotTypeFilter: t1 p))
     (subtype t2 t1 #:env empty-env)]
    [((NotTypeFilter: t1 p) (TypeFilter: t2 p))
     (not (overlap t1 t2))]
    [(_ _) #f]))

(define (hash-name-ref i)
  (if (identifier? i) (hash-id i) i))

;; compact : (Listof prop) bool -> (Listof prop)
;; props : propositions to compress
;; or? : is this an OrFilter (alternative is AndFilter)
;;
;; This combines all the TypeFilters at the same path into one TypeFilter. If it is an OrFilter the
;; combination is done using Un, otherwise, restrict. The reverse is done for NotTypeFilters. If it is
;; an OrFilter this simplifies to -top if any of the atomic filters simplified to -top, and removes
;; any -bot values. The reverse is done if this is an AndFilter.
;;
(define/cond-contract (compact props or?)
     ((c:listof Filter/c) boolean? . c:-> . (c:listof Filter/c))
  (define tf-map (make-hash))
  (define ntf-map (make-hash))
  (define (restrict-update dict t1 p)
    (hash-update! dict p (λ (t2) (restrict t1 t2)) Univ))
  (define (union-update dict t1 p)
    (hash-update! dict p (λ (t2) (Un t1 t2)) -Bottom))

  (define-values (atomics others) (partition atomic-filter? props))
  (for ([prop (in-list atomics)])
    (match prop
      [(TypeFilter: t1 p)
       ((if or? union-update restrict-update) tf-map t1 p)]
      [(NotTypeFilter: t1 p)
       ((if or? restrict-update union-update) ntf-map t1 p)]))
  (define raw-results
    (append others
            (for/list ([(k v) (in-hash tf-map)]) (-filter v k))
            (for/list ([(k v) (in-hash ntf-map)]) (-not-filter v k))))
  (if or?
      (if (member -top raw-results)
          (list -top)
          (filter-not Bot? raw-results))
      (if (member -bot raw-results)
          (list -bot)
          (filter-not Top? raw-results))))

;; invert-filter: Filter/c -> Filter/c
;; Logically inverts a filter.
(define (invert-filter p)
  (match p
    [(Bot:) -top]
    [(Top:) -bot]
    [(TypeFilter: t p) (-not-filter t p)]
    [(NotTypeFilter: t p) (-filter t p)]
    [(AndFilter: fs) (apply -or (map invert-filter fs))]
    [(OrFilter: fs) (apply -and (map invert-filter fs))]
    [(ImpFilter: f1 f2) (-and f1 (invert-filter f2))]
    [(? SLI? s) (SLI-negate s)]))



;; -imp: Filter/c Filter/c -> Filter/c
;; Smart constructor for make-ImpFilter
(define (-imp p1 p2)
  (match* (p1 p2)
    [(t t) -top]
    [((Bot:) _) -top]
    [(_ (Top:)) -top]
    [((Top:) _) p2]
    [(_ (Bot:)) #:when (not (SLI? p1))
                (invert-filter p1)]
    [(_ _) (-or (invert-filter p1) p2)])) ; (make-ImpFilter p1 p2)

(define (-or . args)
  (define mk
    (case-lambda [() -bot]
                 [(f) f]
                 [fs (make-OrFilter (sort fs filter<?))]))
  (define (distribute args)
    (define-values (ands others) (partition AndFilter? args))
    (match ands
      ['() (apply mk others)]
      [(cons (AndFilter: elems) ands-rest)
       (apply -and (for/list ([a (in-list elems)])
                     (apply -or a (append ands-rest others))))]))
  (let loop ([fs args]
             [result null])
    (match fs
      [(list) (distribute (compact result #t))]
      [(cons f rst)
       (cond
         [(Top? f) f]
         [(OrFilter? f) (loop (append (OrFilter-fs f) rst) result)]
         [(Bot? f) (loop rst result)]
         ;; check for complements of 'f' in the other props
         [(let ([complement? (λ (f*) (complementary? f f*))])
            (or (ormap complement? rst)
                (ormap complement? result)))
          -top]
         [else
          ;; get rid of duplicate info
          (define-values (keeping-f? result*)
            (let loop ([to-check result]
                       [checked null])
              (match to-check
                [(list) (values #t checked)]
                [(cons p ps)
                 (cond
                   ;; the new prop is more specific than a prop we already know
                   ;; so we're done (we don't want the more specific in our disjunct)
                   [(implied-atomic? p f)
                    (values #f result)]
                   ;; we found an already processed prop more specific than this new prop
                   ;; so we'll keep the new prop instead of this more specific old one
                   [(implied-atomic? f p)
                    (loop ps checked)]
                   ;; the props are unrelated, keep em both
                   [else (loop ps (cons p checked))])])))
          (cond
            ;; f should be in our disjunct (as far as we care to check), add it to our sifted results
            [keeping-f? (loop rst (cons f result*))]
            ;; f is more specific than something already in our disjunct
            [else (loop rst result*)])])])))

(define (-and . args)
  (define mk
    (case-lambda [() -top]
                 [(f) f]
                 [fs (make-AndFilter (sort fs filter<?))]))
  (define (flatten-ands fs)
    (let loop ([fs fs] [results null])
      (match fs
        [(list) results]
        [(cons (AndFilter: fs*) fs) (loop fs (append fs* results))]
        [(cons f fs) (loop fs (cons f results))])))
  ;; Move all the type filters up front as they are the stronger props
  ;; this reverse really shouldn't be necc, but is at the moment...
  ;; (else let related typecheck unit test fails) TODO: investigate!
  (define-values (type-filters not-type-filters other-args)
    (for/fold ([tfs null] [ntfs null] [ofs null])
              ([f (in-list (reverse (flatten-ands (remove-duplicates args eq? #:key Rep-seq))))])
      (cond
        [(TypeFilter? f) (values (cons f tfs) ntfs ofs)]
        [(NotTypeFilter? f) (values tfs (cons f ntfs) ofs)]
        [else (values tfs ntfs (cons f ofs))])))
  (let loop ([fs (append type-filters not-type-filters other-args)]
             [slis null]
             [result null])
    (match fs
      [(list)
       (define ps (compact result #f))
       (if (memf Bot? ps)
           -bot
           (apply mk (append slis ps)))]
      [(cons f rst)
       (cond
         [(Bot? f) f] ;; bottom, bail
         [(Top? f) (loop rst slis result)] ;; top, continue
         [(SLI? f) ;; SLI, add it to the other SLis
          (define slis* (add-SLI f slis))
          (if (Bot? slis*) -bot (loop rst slis* result))]
         ;; check for 'contradictory?' props in the results thus far
         [(let ([contradiction? (λ (f*) (contradictory? f f*))])
            (or (ormap contradiction? rst)
                (ormap contradiction? result)))
          -bot]
         [else
          ;; get rid of any props in result weaker than this one,
          ;; or if this is weaker than one we already have in results
          ;; omit it
          (define-values (keeping-f? result*)
            (let loop ([to-check result]
                       [checked null])
              (match to-check
                [(list) (values #t checked)]
                [(cons p ps)
                 (cond
                   ;; this new prop is actually weaker than one we already know!
                   ;; just forget about it and continue along our way
                   [(implied-atomic? f p)
                    (values #f result)]
                   ;; this prop we already knew is weaker than the new one, so
                   ;; ditch the old weaker prop
                   [(implied-atomic? p f)
                    (loop ps checked)]
                   [else (loop ps (cons p checked))])])))
          (cond
            ;; f is new (as far as we care to check), add it to our sifted results
            [keeping-f? (loop rst slis (cons f result*))]
            ;; f is already known
            [else (loop rst slis result*)])])])))

;; add-unconditional-prop: tc-results? Filter/c? -> tc-results?
;; Ands the given proposition to the filters in the tc-results.
;; Useful to express properties of the form: if this expressions returns at all, we learn this
(define (add-unconditional-prop results prop)
  (match results
    [(tc-any-results: f) (tc-any-results (-and prop f))]
    [(tc-results: ts (list (FilterSet: fs+ fs-) ...) os)
     (ret ts
          (for/list ([f+ fs+] [f- fs-])
            (-FS (-and prop f+) (-and prop f-)))
          os)]
    [(tc-results: ts (list (FilterSet: fs+ fs-) ...) os dty dbound)
     (ret ts
          (for/list ([f+ fs+] [f- fs-])
            (-FS (-and prop f+) (-and prop f-)))
          os)]))


;; ands the given type filter to both sides of the given arr for each argument
;; useful to express properties of the form: if this function returns at all,
;; we learn this about its arguments (like fx primitives, or car/cdr, etc.)
(define (add-unconditional-filter-all-args arr type)
  (match arr
    [(Function: (list (arr: dom rng rest drest kws dep?)))
     (match rng
       [(Values: (list (Result: tp (FilterSet: -true-filter -false-filter) op)))
        (let ([new-filters (apply -and (build-list (length dom)
                                                   (lambda (i)
                                                     (-filter type i))))])
          (make-Function
           (list (make-arr
                  dom
                  (make-Values
                   (list (-result tp
                                  (-FS (-and -true-filter new-filters)
                                       (-and -false-filter new-filters))
                                  op)))
                  rest drest kws dep?))))])]))

;; tc-results/c -> tc-results/c
(define (erase-filter tc)
  (match tc
    [(tc-any-results: _) (tc-any-results -no-filter)]
    [(tc-results: ts _ _)
     (ret ts
          (for/list ([f (in-list ts)]) -no-filter)
          (for/list ([f (in-list ts)]) -no-obj))]
    [(tc-results: ts _ _ dty dbound)
     (ret ts
          (for/list ([f (in-list ts)]) -no-filter)
          (for/list ([f (in-list ts)]) -no-obj)
          dty dbound)]))


;(trace contradictory?)
;(trace complementary?)
;(trace implied-atomic?)
;(trace compact)
;(trace invert-filter)
;(trace -or)
;(trace -and)