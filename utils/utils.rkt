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

(define (tupleGet t i)
  (list-ref-noerr t i))

; set functions

(define (set-singleton v)
  (list v))

(define (set-create)
  (list))

(define (set-union s1 s2)
  (append s1 s2))

(define (set-member v s1)
   (member v s1) [1])

(define (set-insert v s1)
  (cons v s1))

(define (set-subset s1 s2)
  (andmap (lambda (v) (set-member v s2)) s1))

(define (set-minus s1 s2)
  (filter (lambda (v) (not (set-member v s2))) s1))
