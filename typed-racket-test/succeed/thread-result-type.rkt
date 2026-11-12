#lang typed/racket

;; `thread` records its thunk's result in the thread's type when given
;; `#:keep 'results`; otherwise `thread-wait` produces `(void)`.

(define t0 (thread (λ () 5)))
(ann t0 (Threadof Void))
(ann (thread-wait t0) Void)
(define (wait-void) : Void (thread-wait t0))
(wait-void)

(define t1 (thread (λ () 5) #:keep 'results))
(ann t1 (Threadof Positive-Byte))
(unless (equal? (thread-wait t1) 5)
  (error 'thread-wait "expected the kept result"))

;; any immutable first-order result can be kept
(ann (thread (λ () (list "a" 'b (vector-immutable 1 2))) #:keep 'results)
     (Threadof (List String 'b (Immutable-Vector Positive-Byte Positive-Byte))))

;; a thread killed before finishing produces the failure result
(define t2 (thread (λ () (sleep 1000) "done") #:keep 'results))
(kill-thread t2)
(define r2 : (U String Void Symbol) (thread-wait t2 (λ () 'failed)))
(unless (eq? r2 'failed)
  (error 'thread-wait "expected the failure thunk's result"))
(ann (thread-wait t2) (U String Void))

;; `#:keep #f` is the same as no `#:keep`, and then any thunk is allowed
(ann (thread (λ () 5) #:keep #f) (Threadof Void))
(ann (thread (λ () 5) #:pool #f) (Threadof Void))
(ann (thread (λ () (box 5))) (Threadof Void))
(ann (thread (λ () (values add1 2))) (Threadof Void))

;; a `#:keep` argument that might be `'results` gives a `Thread`
(define (start [keep : (U #f 'results)]) : Thread
  (thread (λ () "s") #:keep keep))
(start 'results)

;; a thread with unknown results can produce any number of values
(define (wait-all [t : Thread]) : (Listof Any)
  (call-with-values (λ () (thread-wait t)) (λ [rs : Any *] rs)))
(unless (equal? (wait-all t1) '(5))
  (error 'thread-wait "expected the kept result"))
(ann (current-thread) Thread)
(define self : Thread (current-thread))
(thread-send (thread (λ () (thread-receive))) self)

;; subtyping: `Threadof` is covariant, `Thread` is its top, and a
;; thread is an event that synchronizes to itself
(ann t1 (Threadof Integer))
(ann t1 Thread)
(ann t0 Thread)
(ann t1 (Evtof (Threadof Integer)))
(ann (sync t1) (Threadof Integer))
(ann (thread/suspend-to-kill void) (Threadof Void))
(ann (ann t1 (U String (Threadof Integer))) (U String Thread))
(ann (list t0 t1) (Listof Thread))
(ann (thread? t1) #t)

;; inference through `thread-wait`
(define (wait-kept [t : (Threadof Integer)]) : (U Integer Void)
  (thread-wait t))
(wait-kept t1)
