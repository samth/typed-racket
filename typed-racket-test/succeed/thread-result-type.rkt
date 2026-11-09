#lang typed/racket

;; `thread` records its thunk's result in the thread's type when given
;; `#:keep 'results`; otherwise `thread-wait` produces `(void)`.

(define t0 (thread (λ () 5)))
(ann t0 Thread)
(ann t0 (Threadof Void))
(ann (thread-wait t0) Void)

(define t1 (thread (λ () 5) #:keep 'results))
(ann t1 (Threadof Positive-Byte))
(unless (equal? (thread-wait t1) 5)
  (error 'thread-wait "expected the kept result"))

;; a thread killed before finishing produces the failure result
(define t2 (thread (λ () (sleep 1000) "done") #:keep 'results))
(kill-thread t2)
(define r2 : (U String Void Symbol) (thread-wait t2 (λ () 'failed)))
(unless (eq? r2 'failed)
  (error 'thread-wait "expected the failure thunk's result"))
(ann (thread-wait t2) (U String Void))

;; `#:keep #f` is the same as no `#:keep`
(ann (thread (λ () 5) #:keep #f) Thread)
(ann (thread (λ () 5) #:pool #f) Thread)

;; existing code that annotates threads as `Thread` keeps working
(define t4 : Thread (thread (λ () (sleep 0))))
(define (wait-void [t : Thread]) : Void (thread-wait t))
(wait-void t4)

;; a thunk with several results gets `ThreadTop`
(define t3 (thread (λ () (values 1 2)) #:keep 'results))
(ann t3 ThreadTop)

;; a thread with unknown results can produce any number of values
(define (wait-all [t : ThreadTop]) : (Listof Any)
  (call-with-values (λ () (thread-wait t)) (λ [rs : Any *] rs)))
(unless (equal? (wait-all t1) '(5))
  (error 'thread-wait "expected the kept result"))
(unless (equal? (wait-all t3) '(1 2))
  (error 'thread-wait "expected both results"))
(ann (current-thread) ThreadTop)

;; subtyping: `Threadof` is covariant, `ThreadTop` is its top, and a
;; thread is an event that synchronizes to itself
(ann t1 (Threadof Integer))
(ann t1 ThreadTop)
(ann t0 ThreadTop)
(ann t1 (Evtof (Threadof Integer)))
(ann (sync t1) (Threadof Integer))
(ann (sync t0) Thread)
(ann (thread/suspend-to-kill void) Thread)
(ann (ann t1 (U String (Threadof Integer))) (U String ThreadTop))
(ann (list t0 t1) (Listof ThreadTop))
(ann (thread? t1) #t)

;; inference through `thread-wait`
(define (wait-kept [t : (Threadof Integer)]) : (U Integer Void)
  (thread-wait t))
(wait-kept t1)
