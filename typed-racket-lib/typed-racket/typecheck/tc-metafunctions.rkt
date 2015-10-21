#lang racket/base

(require "../utils/utils.rkt"
         racket/match racket/list
         (except-in (types abbrev union utils filter-ops tc-result)
                    -> ->* one-of/c)
         (rep type-rep filter-rep object-rep rep-utils)
         (typecheck tc-subst check-below)
         (types remove-intersect) ; for overlap
         (contract-req))

(provide abstract-results
         combine-props
         merge-tc-results
         tc-results->values)

;; Objects representing the rest argument are currently not supported
(define/cond-contract (abstract-results results arg-names #:rest-id [rest-id #f])
  ((tc-results/c (listof identifier?)) (#:rest-id (or/c #f identifier?))
   . ->* . SomeValues/c)
  (define positional-arg-objects
    (for/list ([(nm k) (in-indexed (in-list arg-names))])
      (list nm (make-Path null (list 0 k)))))
  (define arg-objects
    (if rest-id
        (cons (list rest-id -empty-obj) positional-arg-objects)
        positional-arg-objects))
  (tc-results->values (replace-names arg-objects results)))

(define (tc-results->values tc)
  (match (fix-results tc)
    [(tc-any-results: f)
     (-AnyValues f)]
    [(tc-results: ts fs os)
     (make-Values (map -result ts fs os))]
    [(tc-results: ts fs os dty dbound)
     (make-ValuesDots (map -result ts fs os) dty dbound)]))

(define/cond-contract (resolve derived prop)
  ((listof Filter/c)
   Filter/c
   . -> .
   Filter/c)
  (for/fold ([prop prop])
    ([a (in-list derived)])
    (match prop
      [(AndFilter: ps)
       (let loop ([ps ps] [result null])
         (match ps
           [(list) (apply -and result)]
           [(cons p ps*)
            (cond [(contradictory? a p) -bot]
                  [(implied-atomic? p a) (loop ps* result)]
                  [else (loop ps* (cons p result))])]))]
      [(OrFilter: ps)
       (let loop ([ps ps] [result null])
         (match ps
           [(list) (apply -or result)]
           [(cons p ps)
            (cond [(contradictory? a p) (loop ps result)]
                  [(implied-atomic? p a) -top]
                  [else (loop ps (cons p result))])]))]
      [_ prop])))

(define (flatten-props ps)
  (let loop ([ps ps])
    (match ps
      [(list) null]
      [(cons (AndFilter: ps*) ps) (loop (append ps* ps))]
      [(cons p ps) (cons p (loop ps))])))

(define/cond-contract (combine-props new-props old-props exit)
  ((listof Filter/c) (listof Filter/c) (-> none/c)
   . -> .
   (values (listof (or/c ImpFilter? OrFilter?)) 
           (listof (or/c TypeFilter? NotTypeFilter?))
           (listof SLI?)))

  (when (ormap Object? new-props) (error 'combine-props "object in new-props!"))
  (when (ormap Object? old-props) (error 'combine-props "object in old-props!"))
  
  (define-values (new-atoms new-formulas) 
    (partition (λ (p) (or (TypeFilter? p) 
                          (NotTypeFilter? p))) 
               (flatten-props new-props)))
  
  (let loop ([derived-formulas null]
             [derived-atoms new-atoms]
             [worklist (append old-props new-formulas)]
             [slis null])
    (match worklist
      [(list) (values derived-formulas derived-atoms slis)]
      [(cons next-prop ps)
       (match (resolve (append derived-atoms derived-formulas) next-prop)
         [(or (? TypeFilter? a) (? NotTypeFilter? a)) 
          (loop derived-formulas (cons a derived-atoms) ps slis)]
         [(? SLI? s) (let ([slis* (add-SLI s slis)])
                       (if (Bot? slis*)
                           (exit)
                           (loop derived-formulas
                                 derived-atoms
                                 ps
                                 slis*)))]
         [(? OrFilter? p)
          (loop (cons p derived-formulas) derived-atoms ps slis)]
         [(AndFilter: and-ps) (loop derived-formulas derived-atoms (append and-ps ps) slis)]
         [(Top:) (loop derived-formulas derived-atoms ps slis)]
         [(Bot:) (exit)]
         [else (error 'combine-props "invalid worklist! ~a, what is it? ~a"
                      else
                      (struct->vector else))])])))


(define (unconditional-prop res)
  (match res
    [(tc-any-results: f) f]
    [(tc-results (list (tc-result: _ (FilterSet: f+ f-) _) ...) _)
     (apply -and (map -or f+ f-))]))


(define (extract-SLIs prop)
  (match prop
    [(? SLI?) (values -top (list prop))]
    [(AndFilter: fs)
     (define-values (slis non-slis) (partition SLI? fs))
     (cond
       [(null? slis) (values prop (list))]
       [(null? non-slis) (values -top slis)]
       [(null? (cdr non-slis)) (values (car non-slis) slis)]
       [else (values (make-AndFilter non-slis) slis)])]
    [_ (values prop (list))]))

(define (merge-tc-results results)
  (define (merge-tc-result r1 r2)
    (match* (r1 r2)
      [((tc-result: t1 (FilterSet: f1+ f1-) o1)
        (tc-result: t2 (FilterSet: f2+ f2-) o2))
       (define merged-ty (Un t1 t2))
       (let-values ([(f1+ slis1+) (extract-SLIs f1+)]
                    [(f2+ slis2+) (extract-SLIs f2+)]
                    [(f1- slis1-) (extract-SLIs f1-)]
                    [(f2- slis2-) (extract-SLIs f2-)])
         ;; Do not put SLIs in disjuctions. Check that they must be true,
         ;; or do not include them (this is to avoid blow up in files
         ;; with lots of numeric reasoning -- there may be a more principled
         ;; approach to handling this...)
         (define slis+
           (cond
             [(or (Bot? f1+) (type-equal? t1 (-val #f))) slis2+]
             [(or (Bot? f2+) (type-equal? t2 (-val #f))) slis1+]
             [else (filter (λ (s) (memf (λ (s*) (filter-equal? s* s)) slis1+)) slis2+)]))
         (define slis-
           (cond
             [(or (Bot? f1-) (not (overlap t1 (-val #f)))) slis2-]
             [(or (Bot? f2-) (not (overlap t2 (-val #f)))) slis1-]
             [else (filter (λ (s) (memf (λ (s*) (filter-equal? s* s)) slis1-)) slis2-)]))
         (define f+ (apply -and (-or f1+ f2+) slis+))
         (define f- (apply -and (-or f1- f2-) slis-))
         (tc-result
          merged-ty
          (-FS f+ f-)
          (if (equal? o1 o2) o1 -empty-obj)))]))

  (define/match (same-dty? r1 r2)
    [(#f #f) #t]
    [((cons t1 dbound) (cons t2 dbound)) #t]
    [(_ _) #f])
  (define/match (merge-dty r1 r2)
    [(#f #f) #f]
    [((cons t1 dbound) (cons t2 dbound))
     (cons (Un t1 t2) dbound)])

  (define/match (number-of-values res)
    [((tc-results rs #f))
     (length rs)]
    [((tc-results rs (cons _ dbound)))
     (format "~a and ... ~a" (length rs) dbound)])


  (define/match (merge-two-results res1 res2)
    [((tc-result1: (== -Bottom)) res2) res2]
    [(res1 (tc-result1: (== -Bottom))) res1]
    [((tc-any-results: f1) res2)
     (tc-any-results (-or f1 (unconditional-prop res2)))]
    [(res1 (tc-any-results: f2))
     (tc-any-results (-or (unconditional-prop res1) f2))]
    [((tc-results results1 dty1) (tc-results results2 dty2))
     ;; if we have the same number of values in both cases
     (cond
       [(and (= (length results1) (length results2))
             (same-dty? dty1 dty2))
        (tc-results (map merge-tc-result results1 results2)
                    (merge-dty dty1 dty2))]
       ;; otherwise, error
       [else
        (tc-error/expr "Expected the same number of values, but got ~a and ~a"
                         (length results1) (length results2))])])

  (for/fold ([res (ret -Bottom)]) ([res2 (in-list results)])
    (merge-two-results res res2)))
