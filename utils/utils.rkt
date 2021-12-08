#lang rosette

(provide (all-defined-out))

; list functions that have reasonable defaults rather than throwing errors

(define (list-ref-noerr l i)
  (if (&&  (>= i 0) (< i (length l))) (list-ref l i)
      0))

(define (list-tail-noerr l i)
  (if (&& (>= i 0) (<= i (length l))) (list-tail l i)
      (list)))

(define (list-append l i)
  (append l (list i)))

(define (list-empty)
  (list))

(define (list-prepend i l)
  (append (list i) l))

(define (list-take-noerr l i)
  (if (<= i 0) (list) (if (&& (>= i 0) (< i (length l))) (take l i) l )))

(define (list-concat l1 l2)
  (append l1 l2))

; tuple functions

(define (make-tuple e1 . es)
  (cons e1 es))