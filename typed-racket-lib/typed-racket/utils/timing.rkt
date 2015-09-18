#lang racket/base
(require (for-syntax racket/base))
(provide start-timing do-time)

;; some macros to do some timing, only when `timing?' is #t
(define-for-syntax timing? #t)

(define (pad str len pad-char)
  (define l (string-length str))
  (if (>= l len)
      str
      (string-append str (make-string (- len l) pad-char))))


(define-syntax (make-timer stx)
  (syntax-case stx ()
    [(make-timer logger-name start-timing do-time)
     (with-syntax ([lg-debug (datum->syntax #'logger-name (string->symbol (format "log-~a-debug" (syntax-e #'logger-name))))])
       #'(begin
           (define-logger logger-name)
           (define last-time #f) (define initial-time #f) (define gc-time #f)
           (define offset #f) (define mod-name #f) (define initial-gc #f)
           (define (set!-initial-time t) (set! initial-time t))
           (define (set!-offset t) (set! offset t))
           (define (set!-last-time t) (set! last-time t))
           (define (set!-gc-time t) (set! gc-time t))
           (define (set!-initial-gc t) (set! initial-gc t))
           (define (set!-mod-name m) (set! mod-name m))
           (define-syntaxes (start-timing do-time)
             (if timing?
                 (values
                  (syntax-rules ()
                    [(_ mod)
                     (lg-debug
                      (let ()
                        (when last-time
                          (error 'start-timing "Timing already started"))
                        (define t0 (current-inexact-milliseconds))
                        (define t-p (current-process-milliseconds))
                        (set!-offset (- t0 t-p))
                        (set!-last-time t0)
                        (set!-mod-name mod)
                        (set!-initial-time t0)
                        (set!-initial-gc (current-gc-milliseconds))
                        (set!-gc-time initial-gc)
                        (format "~a at ~a"
                                (pad (format "~a : Starting" mod) 40 #\space) (- initial-time offset))))])
                  (syntax-rules ()
                    [(_ msg)
                     (lg-debug
                      (begin
                        (unless last-time
                          (start-timing #f))
                        (let* ([t (current-inexact-milliseconds)]
                               [gc (current-gc-milliseconds)]
                               [old last-time]
                               [diff (- t old)]
                               [gc-diff (- gc gc-time)]
                               [new-msg (pad msg 40 #\space)])
                          (set!-last-time t)
                          (set!-gc-time gc)
                          (format "~a : ~a at ~a\tlast step: ~a\tgc: ~a\ttotal gc: ~a\ttotal: ~a"
                                  mod-name new-msg (- t offset) diff gc-diff (- gc initial-gc) (- t initial-time)))))]))
                 (values (lambda _ #'(void)) (lambda _ #'(void)))))))]))

(make-timer tr-timing start-timing do-time)
(make-timer infer-timing start-infer-timer do-infer-time)
(provide start-infer-timer do-infer-time)
