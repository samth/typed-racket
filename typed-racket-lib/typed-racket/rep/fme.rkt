#lang racket/base

;; *****************************************************************************
;; fme.rkt
;; Fourier-Motzkin elimination implementation
;; http://en.wikipedia.org/wiki/Fourier-Motzkin_elimination
;;
;; Uses non-matrix representations of data (racket sets, so as to avoid
;; duplicate inequalities)
;;
;; decides satisfiability, implication, etc... of/between sets of linear inequalities
;; of the form ([(a_1x_1 + a_2x_2 + ... + a_c) <= (b_1x_1 + b_2x_2 + ... + b_c)] ...)
;; *****************************************************************************

(require racket/contract
         racket/set
         racket/function
         racket/format
         (for-syntax racket/base syntax/parse)
         racket/unsafe/ops
         racket/contract
         racket/match)

(provide lexp?
         lexp
         lexp-coeff
         terms-ref
         terms-remove
         terms-scale
         terms-set
         terms-plus
         lexp-const
         lexp-terms
         lexp-add1
         fme-elim
         constant-lexp?
         simple-lexp?
         leq-lhs
         leq-rhs
         leq
         leq?
         leq-negate
         sli-trivially-valid?
         sli?
         fme-sat?
         fme-imp?
         eqhash?
         lexp:
         leq:
         leq-trivially-valid?
         leq-trivially-invalid?
         sli-union
         sli-union/sat?
         reduce-sli
         sli-add-leq
         reduce-sli/sat?)

(define-for-syntax enable-fme-contracts? #f)

(define-match-expander lexp:
  (lambda (stx)
    (syntax-case stx ()
      [(_ const exp)
       #'(cons const exp)])))

(define-match-expander leq:
  (lambda (stx)
    (syntax-case stx ()
      [(_ lhs rhs)
       #'(cons lhs rhs)])))

(define-syntax define/cond-fme-contract
  (if enable-fme-contracts?
      (make-rename-transformer #'define/contract)
      (lambda (stx)
        (syntax-parse stx
          [(_ head cnt . body)
           (syntax/loc stx (define head . body))]))))

(define eqhash? (flat-contract (and/c hash? hash-eq?)))

(define lexp? (flat-contract (cons/c exact-integer? eqhash?)))

(define/cond-fme-contract lexp
  (-> exact-integer? eqhash? lexp?)
  cons)

(define lexp-const car)
(define lexp-terms cdr)

;(define terms-set hash-set) use terms-set-var instead
(define terms-ref hash-ref)
(define terms-remove hash-remove)

(define-syntax-rule (lexp* t ...)
  (list->lexp (list t ...)))

(define/cond-fme-contract (list->lexp terms)
  (-> (listof (or/c exact-integer? (list/c exact-integer? any/c))) lexp?)
  (let loop ([c 0]
             [h (hasheq)]
             [zxs terms])
    (match zxs
      [(list) (lexp c h)]
      [(cons (list coeff var) zxs-rst)
       (loop c (terms-set h var (+ coeff (hash-ref h var 0))) zxs-rst)]
      [(cons constant zxs-rst)
       (loop (+ constant c) h zxs-rst)])))


(define/cond-fme-contract (terms-set h x i)
  (-> (hash/c any/c exact-integer? #:immutable #t) 
      any/c 
      exact-integer?
      (hash/c any/c exact-integer? #:immutable #t))
  (if (= 0 i)
      (hash-remove h x)
      (hash-set h x i)))

; lexp-coeff
(define/cond-fme-contract (lexp-coeff l x)
  (-> lexp? any/c exact-integer?)
  (hash-ref (lexp-terms l) x 0))

(module+ test
  (require rackunit)
  
  (check-equal? (lexp* 1 '(1 x) '(42 y) 1) (lexp* '(42 y) 2 '(1 x)))
  (check-equal? (lexp* 0) (lexp* 0 '(0 x) '(0 y) '(0 z)))
  (check-equal? (lexp-coeff (lexp* 1 '(1 x) '(42 y)) 'y) 42)
  (check-equal? (lexp-const (lexp* 1 '(1 x) '(42 y))) 1)
  (check-equal? (lexp-coeff (lexp* '(1 x) '(42 y)) 'q) 0))

(define/cond-fme-contract (lexp-vars exp)
  (-> lexp? set?)
  (for/seteq ([x (in-hash-keys (lexp-terms exp))])
    x))

(define/cond-fme-contract (lexp-scalars exp)
  (-> lexp? (listof exact-integer?))
  (match exp
    [(lexp: c h)
     (define coeffs (hash-values h))
     (if (zero? c) coeffs (cons c coeffs))]
    [_ (error 'lexp-scalars "given invalid lexp ~a" exp)]))

(module+ test
  (check-true (and (equal? (list->set (lexp-vars (lexp* 17 '(42 x) '(2 z))))
                           (list->set '(x z)))
                   (= 2 (set-count (lexp-vars (lexp* 17 '(42 x) '(2 z)))))))
  (check-true (and (equal? (list->set (lexp-scalars (lexp* 17 '(42 x) '(2 z))))
                           (list->set '(17 42 2)))
                   (= 3 (set-count (lexp-scalars (lexp* 17 '(42 x) '(2 z))))))))


(define/cond-fme-contract (terms-scale ts a)
  (-> eqhash? rational? eqhash?)
  (cond
    [(zero? a) (hasheq)]
    [(= a 1) ts]
    [else
     (for/hasheq ([(x coeff) (in-hash ts)])
       (values x (* coeff a)))]))

; lexp-scale
;; if multiplying any scalar by a results
;; in a non integer, error is thrown if
;; contracts are active
(define/cond-fme-contract (lexp-scale exp a)
  (-> lexp? rational? lexp?)
  (cond
    [(zero? a)
     (lexp 0 (hasheq))]
    [(= a 1) exp]
    [else
     (match exp
       [(lexp: c h)
        (lexp (* c a)
              (terms-scale h a))]
       [_ (error 'lexp-scale "given invalid lexp ~a" exp)])]))

(module+ test
  (check-equal? (lexp-set (lexp* 17 '(42 x)) 'x 0)
                (lexp* 17)))
; lexp-set
; excludes items set to 0
(define/cond-fme-contract (lexp-set exp x i)
  (-> lexp? any/c exact-integer? lexp?)
  (match exp
    [(lexp: c h)
     (lexp c
           (terms-set h x i))]
    [_ (error 'lexp-set "given invalid lexp ~a" exp)]))

; lexp-set-const
(define/cond-fme-contract (lexp-set-const exp i)
  (-> lexp? exact-integer? lexp?)
  (lexp i
        (lexp-terms exp)))

(module+ test 
  (check-equal? (lexp-set (lexp* 17) 'x 42)
                (lexp* 17 '(42 x)))
  (check-equal? (lexp-set (lexp* 17 '(2 x)) 'x 42)
                (lexp* 17 '(42 x)))
  (check-equal? (lexp-set-const (lexp* 17 '(2 x)) 42)
                (lexp* 42 '(2 x))))

; lexp-zero?
(define/cond-fme-contract (lexp-zero? exp)
  (-> lexp? boolean?)
  (match exp
    [(lexp: c h)
     (and (= 0 c)
          (hash-empty? h))]
    [_ (error 'lexp-zero? "given invalid lexp ~a" exp)]))

(module+ test
  (check-false (lexp-zero? (lexp* 17 '(42 x))))
  (check-false (lexp-zero? (lexp* 17)))
  (check-not-false (lexp-zero? (lexp* 0))))

(define/cond-fme-contract (terms-minus l1-terms l2-terms)
  (-> eqhash? eqhash? eqhash?)
  (for/fold ([h l1-terms])
            ([(x coeff) (in-hash l2-terms)])
    (terms-set h x (- (hash-ref l1-terms x 0) coeff))))

; l1 - l2
(define/cond-fme-contract (lexp-minus l1 l2)
  (-> lexp? lexp? lexp?)
  (match* (l1 l2)
    [((lexp: c1 h1) (lexp: c2 h2))
     (lexp (- c1 c2)
           (terms-minus h1 h2))]
    [(_ _) (error 'lexp-minus "given invalid lexp(s) ~a ~a" l1 l2)]))

(define/cond-fme-contract (terms-plus l1-terms l2-terms)
  (-> eqhash? eqhash? eqhash?)
  (for/fold ([h l1-terms])
            ([(x coeff) (in-hash l2-terms)])
    (terms-set h x (+ (hash-ref l1-terms x 0) coeff))))

;; l1 + l2
(define/cond-fme-contract (lexp-plus l1 l2)
  (-> lexp? lexp? lexp?)
  (match* (l1 l2)
    [((lexp: c1 h1) (lexp: c2 h2))
     (lexp (+ c1 c2)
           (terms-plus h1 h2))]
    [(_ _) (error 'lexp-plus "given invalid lexp(s) ~a ~a" l1 l2)]))

(module+ test
  (check-equal? (lexp-minus (lexp* -1 '(2 x) '(3 y))
                            (lexp* -1 '(2 x) '(42 z)))
                (lexp* 0 '(3 y) '(-42 z)))
  (check-equal? (lexp-minus (lexp* 0)
                            (lexp* -1 '(2 x) '(42 z)))
                (lexp* 1 '(-2 x) '(-42 z))))

; lexp-has-var?
(define/cond-fme-contract (lexp-has-var? l x)
  (-> lexp? any/c boolean?)
  (not (zero? (lexp-coeff l x))))

(module+ test
  (check-false (lexp-has-var? (lexp* 17 '(42 x)) 'y))
  (check-not-false (lexp-has-var? (lexp* 17 '(42 x)) 'x)))

; lexp-add1
(define/cond-fme-contract (lexp-add1 l)
  (-> lexp? lexp?)
  (match l
    [(lexp: c h)
     (lexp (add1 c) h)]
    [_ (error 'lexp-add1 "given invalid lexp ~a" l)]))

(module+ test 
  (check-equal? (lexp-add1 (lexp* 0)) (lexp* 1))
  (check-equal? (lexp-add1 (lexp* 1 '(5 x))) 
                (lexp* 2 '(5 x))))

(define/cond-fme-contract (constant-lexp? l)
  (-> lexp? (or/c exact-integer? #f))
  (match l
    [(lexp: const terms)
     (and (hash-empty? terms)
          const)]
    [_ (error 'constant-lexp? "invalid arg ~a" l)]))

;; if this lexp is 1*x, return x
(define/cond-fme-contract (simple-lexp? exp)
  (-> lexp? any/c)
  (match exp
    [(lexp: c terms)
     (and
      ;; ps is length 1? (i.e. only 1 variable)
      (and (zero? c)
           (= 1 (hash-count terms))
           (let ([pair (car (hash->list terms))])
             (and (= 1 (cdr pair))
                  (car pair)))))]
    [_ (error 'simple-lexp? "given invalid lexp ~a" exp)]))


;; lexp->string
(define/cond-fme-contract (lexp->string e [pp #f])
  (-> lexp? (-> any/c any/c) string?)
  (define vars (lexp-vars e))
  (define const (lexp-const e))
  (define term->string 
    (λ (x) (string-append (if (= 1 (lexp-coeff e x))
                              ""
                              (number->string (lexp-coeff e x)))
                           "(" (if pp
                                   (pp x)
                                   (~a x)) ")")))
  (cond
    [(set-empty? vars) (number->string const)]
    [(zero? const)
     (for/fold ([str (term->string (set-first vars))])
               ([var (in-list (set-rest vars))])
       (string-append str " + " (term->string var)))]
    [else
     (for/fold ([str (number->string const)])
               ([var (in-set vars)])
       (string-append str " + " (term->string var)))]))


;; ********** ********** L E Q s ********* **********
(define leq? (flat-contract (cons/c lexp? lexp?)))
(define/cond-fme-contract leq
  (-> lexp? lexp? leq?)
  cons)
(define leq-lhs car)
(define leq-rhs cdr)

; leq-exps
(define/cond-fme-contract (leq-lexps ineq)
  (-> leq? (values lexp? lexp?))
  (match ineq
    [(leq: lhs rhs)
     (values lhs rhs)]
    [_ (error 'leq-lexps "given invalid leq ~a" ineq)]))


; leq-contains-var
(define/cond-fme-contract (leq-contains-var? ineq x)
  (-> leq? any/c boolean?)
  (match ineq
    [(leq: lhs rhs)
     (or (lexp-has-var? lhs x)
         (lexp-has-var? rhs x))]
    [_ (error 'leq-contains-var? "given invalid leq ~a" ineq)]))

; leq-vars
(define/cond-fme-contract (leq-vars ineq)
  (-> leq? set?)
  (let-values ([(l r) (leq-lexps ineq)])
    (set-union (lexp-vars l)
               (lexp-vars r))))

; leq-negate
; ~ (l1 <= l2) ->
; l2 <= 1 + l1 
; (obviously this is valid for integers only)
(define/cond-fme-contract (leq-negate ineq)
  (-> leq? leq?)
  (match ineq
    [(leq: (lexp: c-l terms-l) (lexp: c-r terms-r))
     (define c-r* (add1 c-r))
     (cond
       [(= c-l c-r*)
        (leq (lexp 0 terms-r) (lexp 0 terms-l))]
       [(< c-l c-r*)
        (leq (lexp (- c-r* c-l) terms-r) (lexp 0 terms-l))]
       [else
        (leq (lexp 0 terms-r) (lexp (- c-l c-r*) terms-l))])]
    [_ (error 'leq-negate "invalid ineq ~a" ineq)]))

(module+ test
  (require rackunit)
  
  (check-equal? (leq-negate (leq (lexp* 0 '(1 x))
                                  (lexp* 0 '(1 y))))
                (leq (lexp* 1 '(1 y))
                     (lexp* 0 '(1 x)))))

;; leq-isolate-var
;; converts leq with x into either:
;;  1) ax <= by + cz + ...
;;  or
;;  2) by + cz + ... <= ax
;;  where a is a positive integer and x is on at most 
;;  one side of the inequality
(define/cond-fme-contract (leq-isolate-var ineq x)
  (-> leq? any/c leq?)
  (match ineq
    [(leq: (lexp: lhs-c lhs-h) (lexp: rhs-c rhs-h))
     (define x-lhs-coeff (hash-ref lhs-h x 0))
     (define x-rhs-coeff (hash-ref rhs-h x 0))
     (cond
       ;; ...1 + ax + ...2 <= ...3 + ax + ...4
       ;; remove x
       ;; --> ;; ...1 + ...2 <= ...3 + ...4
       [(= x-lhs-coeff x-rhs-coeff)
        (define lhs* (lexp lhs-c (hash-remove lhs-h x)))
        (define rhs* (lexp rhs-c (hash-remove rhs-h x)))
        (leq lhs* rhs*)]
       ;; ...1 + ax + ...2 <= ...3 + bx + ...4  where a < b
       ;; isolate x so it is on the rhs
       ;; --> ...1 + ...2 - ...3 - ...4 <= (bx - ax)
       [(< x-lhs-coeff x-rhs-coeff)
        (define lhs* ;; lhs - rhs (w/ x removed from the result)
          (let ([lhs-c* (- lhs-c rhs-c)]
                [lhs-h* (terms-minus lhs-h rhs-h)])
            (lexp lhs-c* (hash-remove lhs-h* x))))
        (define rhs* (lexp  0 (hasheq x (- x-rhs-coeff x-lhs-coeff))))
        (leq lhs* rhs*)]
       ;; ...1 + ax + ...2 <= ...3 + bx + ...4  where a > b
       ;; isolate x so it is on the lhs
       ;; --> (ax - bx) <= ...3 + ...4 - ...1 - ...2
       [else
        (define lhs* (lexp  0 (hasheq x (- x-lhs-coeff x-rhs-coeff))))
        (define rhs*
          (let ([rhs-c* (- rhs-c lhs-c)]
                [rhs-h* (terms-minus rhs-h lhs-h)])
            (lexp rhs-c* (hash-remove rhs-h* x))))
        (leq lhs* rhs*)])]
    [_ (error 'leq-isolate-var "invalid leq ~a" ineq)]))

; x lhs
(module+ test
  (check-equal? (leq-isolate-var (leq (lexp* '(3 x) '(2 z) '(5 y))
                                       (lexp* '(1 x) '(1 z)))
                                 'x)
                (leq (lexp* '(2 x)) (lexp* '(-5 y) '(-1 z))))
  
  ;; x rhs
  (check-equal? (leq-isolate-var (leq (lexp* '(3 x) '(2 z) '(5 y))
                                       (lexp* '(1 z) '(33 x)))
                                 'x)
                (leq (lexp* '(1 z) '(5 y)) (lexp* '(30 x))))
  ;; x eq
  (check-equal? (leq-isolate-var (leq (lexp* '(42 x) '(2 z) '(5 y))
                                       (lexp* '(42 x) '(1 z)))
                                 'x)
                (leq (lexp* '(2 z) '(5 y))
                      (lexp* '(1 z))))
  ;; no x
  (check-equal? (leq-isolate-var (leq (lexp* '(2 z) '(5 y))
                                       (lexp* '(1 z)))
                                 'x)
                (leq (lexp* '(2 z) '(5 y))
                      (lexp* '(1 z))))
  
  ; x mix
  (check-equal? (leq-isolate-var (leq (lexp* '(2 x) '(4 y) 1)
                                       (lexp* '(2 y))) 'x)
                (leq (lexp* '(2 x))
                      (lexp* '-1 '(-2 y)))))


;; leq-join
;; takes a pair a1x <= l1 and l2 <= a2x
;; and returns a2l1 <= a1l2
(define/cond-fme-contract (leq-join leq1 leq2 x)
  (-> leq? leq? any/c leq?)
  ;; leq1: ... + ax + .... <= ... + bx + ...
  ;; leq2: ... + cx + .... <= ... + dx + ...
  (let-values ([(l1 r1) (leq-lexps leq1)]
               [(l2 r2) (leq-lexps leq2)])
    (let ([a (lexp-coeff l1 x)] [b (lexp-coeff r1 x)]
          [c (lexp-coeff l2 x)] [d (lexp-coeff r2 x)])
      (cond
        ;; leq1: ax <= lexp1
        ;; leq2: lexp2 <= dx
        [(and (zero? b) (zero? c))
         (leq (lexp-scale l2 a)
              (lexp-scale r1 d))]
        ;; leq1: lexp1 <= bx 
        ;; leq2: cx <= lexp2
        [(and (zero? a) (zero? d))
         (leq (lexp-scale l1 c)
              (lexp-scale r2 b))]
        [else
         (error 'leq-join "cannot join ~a and ~a by ~a" leq1 leq2 x)]))))

(module+ test 
  (check-equal? (leq-join (leq (lexp* '(2 x))
                               (lexp* '(4 y) 10))
                          (leq (lexp* '(4 z) 2)
                               (lexp* '(4 x)))
                          'x)
                (leq (lexp* '(8 z) 4)
                     (lexp* '(16 y) 40))))


;; trivially-valid?
(define/cond-fme-contract (leq-trivially-valid? ineq)
  (-> leq? boolean?)
  (let-values ([(l r) (leq-lexps ineq)])
      (or (and (constant-lexp? l)
               (constant-lexp? r)
               (<= (lexp-const l) (lexp-const r)))
          (equal? l r))))

(define/cond-fme-contract (leq-trivially-invalid? ineq)
  (-> leq? boolean?)
  (let-values ([(l r) (leq-lexps ineq)])
    (and (constant-lexp? l)
         (constant-lexp? r)
         (< (lexp-const r) (lexp-const l)))))


(define/cond-fme-contract (leq->string ineq [pp #f])
  (-> leq? (-> any/c any/c) string?)
  (define-values (lhs rhs) (leq-lexps ineq))
  (string-append (lexp->string lhs pp) " ≤ " (lexp->string rhs pp)))

;; ******** ******** SLIs ******** ********

(define sli? (flat-contract (set/c leq?)))

(define/cond-fme-contract (sli->string sli)
  (-> sli? string?)
  (string-append 
   (cond
     [(set-empty? sli) "("]
     [else
      (for/fold ([str (leq->string (set-first sli))])
                ([ineq (set-rest sli)])
        (string-append str " ∧ "(leq->string ineq)))])
   ")"))

(define/cond-fme-contract (sli-trivially-valid? s)
  (-> sli? boolean?)
  (for/and ([ineq (in-set s)])
    (leq-trivially-valid? ineq)))

; sli-vars
(define/cond-fme-contract (sli-vars sli)
  (-> sli? set?)
  (for/fold ([vars (seteq)])
            ([l (in-set sli)])
    (set-union vars
               (leq-vars l))))

(module+ test
  (require rackunit)
  
  (check-equal? (sli-vars (set (leq (lexp* '(1 x))
                                    (lexp* '(1 y)))
                               (leq (lexp* '(1 x) '(1 z))
                                    (lexp* '(1 q)))
                               (leq (lexp* '(1 r) '(3 z))
                                    (lexp* '(1 x)))))
                (seteq 'r 'q 'z 'y 'x))
  (check-equal? (set-count (sli-vars (set (leq (lexp* '(1 x))
                                               (lexp* '(1 y)))
                                          (leq (lexp* '(1 x) '(1 z))
                                               (lexp* '(1 q)))
                                          (leq (lexp* '(1 r) '(3 z))
                                               (lexp* '(1 x))))))
                5))


;; sli-partition
;; partitions leq expressions into
;; 3 lists of x-normalized inequalities:
;;  value 1) set of (ax <= by + cz + ...) leqs
;;  value 2) set of form (by + cz + ... <= ax) leqs
;;  value 3) leqs w/o x
(define/cond-fme-contract (sli-partition leqs x)
  (-> sli? any/c (values sli? sli? sli?))
  (for/fold ([xlhs (set)]
             [xrhs (set)]
             [nox (set)]) 
            ([ineq (in-set leqs)])
    (let ([ineq (leq-isolate-var ineq x)])
      (cond
        [(lexp-has-var? (leq-lhs ineq) x)
         (values (set-add xlhs ineq) xrhs nox)]
        [(lexp-has-var? (leq-rhs ineq) x)
         (values xlhs (set-add xrhs ineq) nox)]
        [else
         (values xlhs xrhs (set-add nox ineq))]))))

(module+ test
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition (set (leq (lexp* '(2 x) '(4 y) 1)
                                                       (lexp* '(2 y)))) 
                                             'x)])
                  (list lt gt no))
                (list (set (leq (lexp* '(2 x)) 
                                (lexp* '(-2 y) -1)))
                      (set)
                      (set)))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition (set (leq (lexp* '(2 x) '(4 y) 1)
                                                       (lexp* '(2 y)))
                                                  (leq (lexp* '(2 x) '(4 y))
                                                       (lexp* '(2 y) '(42 x)))) 
                                             'x)])
                  (list lt gt no))
                (list (set (leq (lexp* '(2 x)) 
                                 (lexp* '(-2 y) -1)))
                      (set (leq (lexp* '(2 y))
                                 (lexp* '(40 x))))
                      (set)))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition (set (leq (lexp* '(2 x) '(4 y) -1)
                                                       (lexp* '(2 y)))
                                                  (leq (lexp* '(2 x) '(4 y))
                                                       (lexp* '(2 y) '(42 x)))
                                                  (leq (lexp* '(2 z) '(4 y))
                                                       (lexp* '(2 y) '(42 q)))) 
                                             'x)])
                  (list lt gt no))
                (list (set (leq (lexp* '(2 x)) 
                                (lexp* '(-2 y) 1)))
                      (set (leq (lexp* '(2 y))
                                (lexp* '(40 x))))
                      (set (leq (lexp* '(2 z) '(4 y))
                                (lexp* '(2 y) '(42 q)))))))


;; cartesian-map
;; map of f over each pair of cartesian
;; product of input lists
;; order not guaranteed
(define/cond-fme-contract (cartesian-map f xs ys)
  (-> procedure? set? set? set?)
  (for*/fold ([result (set)]) 
             ([x (in-set xs)] 
              [y (in-set ys)])
    (set-add result (f x y))))


;; eliminate-var
;; reduces the system of linear inequalties,
;; removing x
(define/cond-fme-contract (fme-elim sli x)
  (-> sli? any/c sli?)
  (define-values (xltleqs xgtleqs noxleqs) (sli-partition sli x))
  (set-union (cartesian-map (curryr leq-join x) 
                            xltleqs
                            xgtleqs)
             noxleqs))

;; reduces the system of linear inequalties,
;; removing variables x for which (pred? x) = #t
(define/cond-fme-contract (fme-elim-filter sli pred?)
  (-> sli? (-> any/c boolean?) sli?)
  (for/fold ([s sli]) 
            ([x (in-set (sli-vars sli))])
    (if (pred? x)
        (fme-elim s x)
        s)))

;; sli-satisfiable?
(define/cond-fme-contract (fme-sat? sli)
  (-> sli? boolean?)
  (let* ([vars (sli-vars sli)]
         [simple-system (for/fold ([s sli]) 
                                  ([x (in-set vars)])
                          (fme-elim s x))])
    (for/and ([ineq (in-set simple-system)])
      (leq-trivially-valid? ineq))))


(module+ test
  ; 3x + 2y <= 7; 6x + 4y <= 15;  -x <= 1; 0 <= 2y has integer solutions
  (check-true (fme-sat? (set (leq (lexp* '(3 x) '(2 y))
                                  (lexp* 7))
                             (leq (lexp* '(6 x) '(4 y))
                                  (lexp* 15))
                             (leq (lexp* '(-1 x))
                                  (lexp* 1))
                             (leq (lexp* 0)
                                  (lexp* '(2 y))))))
  
  ; 3x + 2y <= 4; 1 <= x; 1 <= y no solutions 
  (check-false (fme-sat? (set (leq (lexp* '(3 x) '(2 y))
                                   (lexp* 4))
                              (leq (lexp* 1)
                                   (lexp* '(1 x)))
                              (leq (lexp* 1)
                                   (lexp* '(1 y)))))))

;;**********************************************************************
;; Logical Implication for Integer Linear Inequalities
;; using Fourier-Motzkin elimination
;;**********************************************************************

(define/cond-fme-contract (fme-imp-leq? s ineq)
  (-> sli? leq? boolean?)
  (or (set-member? s ineq)
      (not (fme-sat? (set-add s (leq-negate ineq))))))

(module+ test
  ; transitivity! x <= y /\ y <= z --> x <= z
  (check-true (fme-imp-leq? (set (leq (lexp* '(1 x))
                                      (lexp* '(1 y)))
                                 (leq (lexp* '(1 y))
                                      (lexp* '(1 z))))
                            (leq (lexp* '(1 x))
                                 (lexp* '(1 z)))))


  ; x  <= x;
  (check-true (fme-imp-leq? (set)
                            (leq (lexp* '(1 x))
                                 (lexp* '(1 x)))))
  
  ; x  - 1 <= x + 1;
  (check-true (fme-imp-leq? (set)
                            (leq (lexp* '(1 x) -1)
                                 (lexp* '(1 x) 1))))
  
  
  ; x + y <= z; 1 <= y; 0 <= x --> x + 1 <= z
  (check-true (fme-imp-leq? (set (leq (lexp* '(1 x) '(1 y))
                                      (lexp* '(1 z)))
                                 (leq (lexp* 1)
                                      (lexp* '(1 y)))
                                 (leq (lexp*)
                                      (lexp* '(1 x))))
                            (leq (lexp* '(1 x) 1)
                                 (lexp* '(1 z))))))

;;**********************************************************************
;; Simple Inequality Implication   (does P imply Q)
;;**********************************************************************
(define/cond-fme-contract (leq-imp-leq? P Q) 
  (-> leq? leq? boolean?)
  (or (equal? P Q)
      ;; (P -> Q)  ==  (~P or Q) == ~(P and ~Q)
      (not (fme-sat? (set P (leq-negate Q))))))

(module+ test
  (check-true (leq-imp-leq? (leq (lexp* '(1 x))
                                 (lexp* '(1 y)))
                            (leq (lexp* '(1 x))
                                 (lexp* '(1 y)))))
  (check-true (leq-imp-leq? (leq (lexp* '(1 x))
                                 (lexp* 14))
                            (leq (lexp* '(1 x))
                                 (lexp* 15))))
  (check-true (leq-imp-leq? (leq (lexp* '(1 x) '(1 y))
                                 (lexp* 14))
                            (leq (lexp* '(1 x) '(1 y))
                                 (lexp* 20))))
  (check-false (leq-imp-leq? (leq (lexp* '(1 x) '(1 y))
                                  (lexp* 14))
                             (leq (lexp* '(1 x))
                                  (lexp* 14)))))

;;**********************************************************************
;; Contradictory leqs?  ~(P and Q)
;;**********************************************************************
(define/cond-fme-contract (contradictory-leqs? P Q) 
  (-> leq? leq? boolean?)
  ;; (P -> Q)  ==  (~P or Q) == ~(P and ~Q)
  (not (fme-sat? (set P Q))))

(module+ test
  (check-true (contradictory-leqs? (leq (lexp* 2)
                                        (lexp* 1))
                                   (leq (lexp* '(1 y))
                                        (lexp* '(1 x)))))
  (check-true (contradictory-leqs? (leq (lexp* '(1 x))
                                        (lexp* '(1 y)))
                                   (leq (lexp* 1 '(1 y))
                                        (lexp* '(1 x)))))
  (check-false (contradictory-leqs? (leq (lexp* '(1 x))
                                         (lexp* '(1 y)))
                                    (leq (lexp* '(1 x))
                                         (lexp* '(1 y)))))
  (check-false (contradictory-leqs? (leq (lexp* 1)
                                         (lexp* 2))
                                    (leq (lexp* 2)
                                         (lexp* 3)))))
;;**********************************************************************
;; Logical Implication for Systems of Integer Linear Inequalities
;; using Fourier-Motzkin elimination
;;**********************************************************************

(define/cond-fme-contract (fme-imp? axioms goals)
  (-> sli? sli? boolean?)
  (for/and ([ineq (in-set goals)])
    (fme-imp-leq? axioms ineq)))


(module+ test
  ;; 4 <= 3 is false
  (check-false (fme-imp? (set)
                         (set (leq (lexp* 4)
                                   (lexp* 3)))))
  ;; P and ~P --> false
  (check-true (fme-imp? (set (leq (lexp*) (lexp* '(1 y)))
                             (leq-negate (leq (lexp*) (lexp* '(1 y)))))
                        (set (leq (lexp* 4)
                                  (lexp* 3)))))
  
  
  ;; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
  (check-true (fme-imp? (set (leq (lexp* '(1 x) '(1 y))
                                  (lexp* '(1 z)))
                             (leq (lexp*)
                                  (lexp* '(1 y)))
                             (leq (lexp*)
                                  (lexp* '(1 x))))
                        (set (leq (lexp* '(1 x))
                                  (lexp* '(1 z)))
                             (leq (lexp* '(1 y))
                                  (lexp* '(1 z))))))
  
  ;; x + y <= z; 0 <= y; 0 <= x -/-> x <= z /\ y <= q
  (check-false (fme-imp? (set (leq (lexp* '(1 x) '(1 y))
                                   (lexp* '(1 z)))
                              (leq (lexp*)
                                   (lexp* '(1 y)))
                              (leq (lexp*)
                                   (lexp* '(1 x))))
                         (set (leq (lexp* '(1 x))
                                   (lexp* '(1 z)))
                              (leq (lexp* '(1 y))
                                   (lexp* '(1 q))))))
  
  ;; 7x <= 29 --> x <= 4
  (check-true (fme-imp? (set (leq (lexp* '(7 x))
                                  (lexp* 29)))
                        (set (leq (lexp* '(1 x))
                                  (lexp* 4)))))
  ;; 7x <= 28 --> x <= 4
  (check-true (fme-imp? (set (leq (lexp* '(7 x))
                                  (lexp* 28)))
                        (set (leq (lexp* '(1 x))
                                  (lexp* 4)))))
  ;; 7x <= 28 does not --> x <= 3
  (check-false (fme-imp? (set (leq (lexp* '(7 x))
                                   (lexp* 28)))
                         (set (leq (lexp* '(1 x))
                                   (lexp* 3)))))
  
  
  ;; 7x <= 27 --> x <= 3
  (check-true (fme-imp? (set (leq (lexp* '(7 x))
                                  (lexp* 27)))
                        (set (leq (lexp* '(1 x))
                                  (lexp* 3)))))
  
  ;; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
  ;; x <= y + z; 
  ;; 29r <= x + y + z + q; 
  ;; 0 <= x;  
  ;; 0 <= x + y + z; 
  ;; 0 <= x + z; 
  ;; x <= z
  ;; z + 1 <= t
  ;; 0 <= x + y;
  ;; 0 <= x + r;
  ;; 0 <= x + r + q;
  ;; -->
  ;; 0 <= t
  (check-true (fme-imp? (set (leq (lexp* '(4 x) '(3 y) '(9 z) '(20 q) '(-100 r) 42)
                                  (lexp* '(4 x) '(3 y) '(9 z) '(20 q) '(100 r)))
                             (leq (lexp* '(1 x))
                                  (lexp* '(1 y) '(1 z)))
                             (leq (lexp* '(29 r))
                                  (lexp* '(1 x) '(1 y) '(1 z) '(1 q)))
                             (leq (lexp*)
                                  (lexp* '(1 x)))
                             (leq (lexp*)
                                  (lexp* '(1 x) '(1 y) '(1 z)))
                             (leq (lexp*)
                                  (lexp* '(1 x) '(1 z)))
                             (leq (lexp* '(1 x))
                                  (lexp* '(1 z)))
                             (leq (lexp* '(1 z) 1)
                                  (lexp* '(1 t)))
                             (leq (lexp*)
                                  (lexp* '(1 x) '(1 y)))
                             (leq (lexp*)
                                  (lexp* '(1 x) '(1 r)))
                             (leq (lexp*)
                                  (lexp* '(1 x) '(1 r) '(1 q))))
                        (set (leq (lexp*)
                                  (lexp* '(1 t))))))
  
  ;; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
  ;; x <= y + z; 
  ;; 29r <= x + y + z + q; 
  ;; 0 <= x;  
  ;; 0 <= x + y + z; 
  ;; 0 <= x + z; 
  ;; x <= z
  ;; z + 1 <= t
  ;; 0 <= x + y;
  ;; 0 <= x + r;
  ;; 0 <= x + r + q;
  ;; -/->
  ;; t <= 0
  (check-false (fme-imp? (set (leq (lexp* '(4 x) '(3 y) '(9 z) '(20 q) '(-100 r) 42)
                                   (lexp* '(4 x) '(3 y) '(9 z) '(20 q) '(100 r)))
                              (leq (lexp* '(1 x))
                                   (lexp* '(1 y) '(1 z)))
                              (leq (lexp* '(29 r))
                                   (lexp* '(1 x) '(1 y) '(1 z) '(1 q)))
                              (leq (lexp*)
                                   (lexp* '(1 x)))
                              (leq (lexp*)
                                   (lexp* '(1 x) '(1 y) '(1 z)))
                              (leq (lexp*)
                                   (lexp* '(1 x) '(1 z)))
                              (leq (lexp* '(1 x))
                                   (lexp* '(1 z)))
                              (leq (lexp* '(1 z) 1)
                                   (lexp* '(1 t)))
                              (leq (lexp*)
                                   (lexp* '(1 x) '(1 y)))
                              (leq (lexp*)
                                   (lexp* '(1 x) '(1 r)))
                              (leq (lexp*)
                                   (lexp* '(1 x) '(1 r) '(1 q))))
                         (set (leq (lexp* '(1 t))
                                   (lexp*))))))


;; adds a new leq to an sli,
;; ensuring we are not 'duplicating' info
;; that is obvious or already assumed
;; returns #f if new contradicts a particular leq
;; NOTE: this assumes 's' already has similarly been
;; treated in the past and does not contain
;; obviously duplicate info. i.e. if we find a weaker
;; statement, we assume it's the only weaker one in the set
(define/cond-fme-contract (sli-add-leq s new)
  (-> sli? leq? (or/c #f sli?))
  (cond
    [(or (leq-trivially-valid? new)
         (set-member? s new)) s]
    [else
     (let loop ([sys s]
                [to-do s])
       (if (set-empty? to-do)
           (set-add sys new) ;; we got to the end w/o problems, add new
           (let ([ineq (set-first to-do)])
             (cond
               ;; new is weaker than our current assumptions, return sys
               [(leq-imp-leq? ineq new)
                sys]
               ;; an inequality in our system is weaker than the new one
               [(leq-imp-leq? new ineq)
                (set-add (set-remove sys ineq) new)]
               [(contradictory-leqs? ineq new)
                #f]
               [else (loop sys (set-rest to-do))]))))]))

(module+ test
  (check-equal? (sli-add-leq (set)
                             (leq (lexp*)
                                  (lexp* '(1 x))))
                (set (leq (lexp*)
                          (lexp* '(1 x)))))
  (check-equal? (sli-add-leq (set (leq (lexp*)
                                       (lexp* '(1 x)))
                                  (leq (lexp*)
                                       (lexp* '(1 y))))
                             (leq (lexp*)
                                  (lexp* '(1 y))))
                (set (leq (lexp*)
                          (lexp* '(1 x)))
                     (leq (lexp*)
                          (lexp* '(1 y)))))
  (check-equal? (sli-add-leq (set (leq (lexp*)
                                       (lexp* '(1 x)))
                                  (leq (lexp*)
                                       (lexp* '(1 y))))
                             (leq (lexp* 1)
                                  (lexp* '(1 y))))
                (set (leq (lexp*)
                          (lexp* '(1 x)))
                     (leq (lexp* 1)
                          (lexp* '(1 y)))))
  (check-equal? (sli-add-leq (set (leq (lexp*)
                                       (lexp* '(1 x)))
                                  (leq (lexp* 1)
                                       (lexp* '(1 y))))
                             (leq (lexp* 0)
                                  (lexp* '(1 y))))
                (set (leq (lexp*)
                          (lexp* '(1 x)))
                     (leq (lexp* 1)
                          (lexp* '(1 y)))))
  (check-false (sli-add-leq (set (leq (lexp* 0)
                                      (lexp* '(1 y))))
                            (leq (lexp* '(1 y))
                                 (lexp* -1)))))



(define/cond-fme-contract (sli-union orig addition)
  (-> sli? sli? (or/c #f sli?))
  (let loop ([sys orig]
             [additions addition])
    (cond
      [(not sys) #f]
      [(set-empty? additions) sys]
      [else
       (loop (sli-add-leq sys (set-first additions))
             (set-rest additions))])))

(module+ test
  (check-false (sli-union (set (leq (lexp* 0)
                                    (lexp* '(1 y))))
                          (set (leq (lexp* '(1 y))
                                    (lexp* -1))))))


(define/cond-fme-contract (sli-union/sat? orig addition)
  (-> sli? sli? (or/c #f sli?))
  (let ([sys* (sli-union orig addition)])
    (if (and sys* (fme-sat? sys*))
        sys*
        #f)))

;; takes an sli that may contain duplicate
;; information (e.g. x <= 0 and x <= 1)
;; and reduces is
(define (reduce-sli s)
  (let loop ([s (set)]
             [ineqs s])
    (cond
    [(not s) #f]
    [(set-empty? ineqs) s]
    [else (loop (sli-add-leq s (set-first ineqs)) (set-rest ineqs))])))

(module+ test
  (check-false (reduce-sli (set (leq (lexp* 0)
                                     (lexp* '(1 y)))
                                (leq (lexp* '(1 y))
                                     (lexp* -1))))))

(define (reduce-sli/sat? s)
  (let ([s (reduce-sli s)])
    (and s (fme-sat? s) s)))

(module+ test
  (check-false (reduce-sli/sat? (set (leq (lexp* 0)
                                          (lexp* '(1 y)))
                                     (leq (lexp* '(1 y))
                                          (lexp* -1))))))