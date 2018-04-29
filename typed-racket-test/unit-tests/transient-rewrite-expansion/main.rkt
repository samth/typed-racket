#lang racket/base

;; TODO
;; - fix datum-literals ?

(require
  "../test-utils.rkt"
  rackunit
  racket/pretty
  racket/list
  racket/set
  syntax/parse
  racket/runtime-path
  (only-in racket/format ~a)
  (only-in syntax/modread with-module-reading-parameterization))

(provide tests)
(gen-test-main)

(define-runtime-path PWD ".")

;; ---

(define-syntax-rule (syntax-predicate pat)
  (syntax-parser [pat #true] [_ #false]))

(define (no-transient-assert? stx)
  (null? (stx-find-transient-assert* stx)))

(define (not-implemented stx)
  #f)

;; ---

(define (run-test filename . predicate*)
  (printf "transient-rewrite test: ~a~n" filename)
  (define mod-stx
    ;; thanks: read-lang-file
    (call-with-input-file (build-path PWD filename)
      (lambda (in-port)
        (port-count-lines! in-port)
        (with-module-reading-parameterization
          (lambda ()
            (read-syntax (object-name in-port) in-port))))))
  (define stx
    (parameterize ((current-namespace (make-base-namespace)))
      (expand mod-stx)))
  (for/and ((p? (in-list predicate*)))
    (if (p? stx)
      #true
      (raise-arguments-error 'expand-test
                             "predicate failed"
                             "predicate" (object-name p?)
                             "file" filename))))

(define (stx-find orig-stx p?)
  (define stx* (stx-find* orig-stx p?))
  (if (or (null? stx*)
          (not (null? (cdr stx*))))
    (raise-arguments-error 'stx-find "non-unique results" "num matches" (length stx*) "orig-stx" orig-stx "predicate" p? "matches" stx*)
    (car stx*)))

(define (stx-find* orig-stx p?)
  (let loop ((stx orig-stx))
    (cond
      [(syntax? stx)
       (let ((v (p? stx)))
         (if v
           (list
             (if (eq? #true v) stx v))
           (loop (syntax-e stx))))]
      [(pair? stx)
       (append (loop (car stx)) (loop (cdr stx)))]
      [else
        '()])))

(define (stx-find-transient-assert orig-stx)
  (stx-find orig-stx transient-assert?))

(define (stx-find-transient-assert* orig-stx)
  (stx-find* orig-stx transient-assert?))

(define transient-assert?
  (syntax-predicate
    ((~literal #%plain-app) (~datum transient-assert) . _)))

(define (stx-find-define-predicate-ctc stx pred-name)
  (let* ((lift-id
           (stx-find stx
             (syntax-parser
               #:datum-literals (define-values let-values #%app)
               ((define-values (name:id) (let-values (((:id) (#%app fcp:id lift:id))) _))
                #:when (eq? (syntax-e #'name) pred-name)
                #'lift)
               (_ #f))
             ))
         (lift-ctc
           (stx-find stx
             (syntax-parser
               (((~datum define-values) (lt:id) ctc:id)
                #:when (eq? (syntax-e #'lt) (syntax-e lift-id))
                #'ctc)
               (_ #f))))
         (ctc*
           (stx-find* stx
             (syntax-parser
               #:datum-literals (define-values lambda)
               ((define-values (g:id) (lambda (_) body))
                #:when (eq? (syntax-e #'g) (syntax-e lift-ctc))
                #'body)
               (_ #f)))))
    (cond
      [(null? ctc*)
       lift-ctc]
      [(null? (cdr ctc*))
       (car ctc*)]
      [else
       (raise-arguments-error 'stx-find-define-predicate-ctc "cannot find lifted" "pred" pred-name)])))

(define (split-transient-assert stx)
  (define expr (if (syntax? stx) (syntax->datum stx) stx))
  (define srcloc
    (let* ((v (sixth expr))
           (v (and (pair? v) (pair? (cdr v)) (cadr v))))
      v))
  (values (third expr)
          (fourth expr)
          (second (fifth expr))
          (and (list? srcloc) (second srcloc))))

(define ((transient-assert-matches #:expr [this-expr #f] #:shape [this-shape #f] #:type [this-type #f] #:line [this-line #f]) stx)
  (define-values [that-expr that-shape that-type that-line] (split-transient-assert stx))
  (and
    (asym-equal? this-expr that-expr)
    (asym-equal? this-shape that-shape)
    (asym-equal? this-type that-type)
    (asym-equal? this-line that-line)))

(define (asym-equal? a b)
  (or (not a) (equal? a b)))

;; ---

(define test-registry
  (list
    (list "case-lambda.rkt"
          (lambda (stx)
            (and
              (let* ((f0-stx (stx-find
                               stx
                               (syntax-predicate
                                 ((~literal define-values) ((~datum f0)) ((~literal case-lambda) _)))))
                     (f0-assert (stx-find-transient-assert f0-stx))
                     (f0-match? (transient-assert-matches #:expr 'x #:shape 'symbol?  #:type "Symbol")))
                (f0-match? f0-assert))
              (let* ((all-assert* (stx-find-transient-assert* stx))
                     (y-pred (transient-assert-matches #:expr 'y #:shape 'none/c/proc #:type "Nothing"))
                     (z-pred (transient-assert-matches #:expr 'z #:shape 'none/c/proc #:type "Nothing")))
                (and
                  (memf y-pred all-assert*)
                  (memf z-pred all-assert*))))))

    (list "cdr.rkt"
          no-transient-assert?)

    (list "default-continuation-prompt-tag.rkt"
          no-transient-assert?)

    (list "for.rkt"
          (lambda (stx)
            (define all-assert* (stx-find-transient-assert* stx))
            (define car-pred (transient-assert-matches #:type "(U 'A 'B 'C)" #:line 2133))
            (for/and ((assert (in-list all-assert*)))
              (car-pred assert))))

    (list "list.rkt"
          (lambda (stx)
            (define all-assert* (stx-find-transient-assert* stx))
            (define line-nums
              (with-input-from-file "list.rkt"
                (lambda ()
                  (for/list ((ln (in-lines))
                             (n (in-naturals 1))
                             #:when (regexp-match? #rx"yes transient-assert" ln))
                    n))))
            (and
              (= (length all-assert*) (length line-nums))
              (for/and ((assert (in-list all-assert*))
                        (num (in-list line-nums)))
                ((transient-assert-matches #:line num) assert)))))

    #;(list "object-private.rkt"
          (lambda (stx)
            (define all-assert* (stx-find-transient-assert* stx))
            (and
              (= 1 (length all-assert*))
              (andmap (transient-assert-matches #:type "Symbol") all-assert*))))

    (list "predicate.rkt"
          (lambda (stx)
            (define List?-stx (stx-find-define-predicate-ctc stx 'List?))
            (define Vector?-stx (stx-find-define-predicate-ctc stx 'Vector?))
            (define List-pred
              (syntax-parser
                #:datum-literals (if #%app list? = quote length)
                ((if (#%app list? _:id)
                  (#%app = (quote 2) (#%app length _:id))
                  (quote #f))
                 #true)
                (_ #false)))
            (define Vector-pred (syntax-predicate (~literal vector?)))
            (and
              (List-pred List?-stx)
              (Vector-pred Vector?-stx))))

    (list "struct-predicate.rkt"
          (lambda (stx)
            (define all-assert* (stx-find-transient-assert* stx))
            (define all-line*
              (for/list ((assert (in-list all-assert*)))
                (define-values [_a _b _c line] (split-transient-assert assert))
                line))
            (define struct-line-num
              (with-input-from-file "struct-predicate.rkt"
                (lambda ()
                  (for/first ((ln (in-lines))
                              (n (in-naturals))
                              #:when (regexp-match? #rx"^\\(struct .*\\)$" ln))
                    n))))
            (define late-line*
              (filter (lambda (n) (and n (< struct-line-num n))) all-line*))
            (= 1 (length late-line*))))
  ))

(define tests
  (test-suite "Transient Rewrite Tests"
    (for ((x (in-list test-registry)))
      (check-true (apply run-test x)))))

