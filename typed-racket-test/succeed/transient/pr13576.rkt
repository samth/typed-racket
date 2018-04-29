#lang typed/racket/shallow/base

(define: (A ...) (lister args : A ... A) : (List A ... A)
   args)
