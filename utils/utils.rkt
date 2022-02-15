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

(define (merge as bs)
  (match* (as bs)
    [((list) bs)  bs]
    [(as (list))  as]
    [((list a as ...) (list b bs ...))
     (if (= a b)
      (merge (cons a as) bs)
      (if (< a b)
         (cons a (merge as (cons b bs)))
         (cons b (merge (cons a as) bs)))
     )]))

; todo: eliminate once input sets don't have duplicates
(define (set-eq s1 s2)
  (equal? s1 s2))

; todo: use merge-sort and constrain input sets to not have duplicate elements
(define (set-union s1 s2)
  (sort (remove-duplicates (append s1 s2)) <))

(define (set-member v s1)
  (ormap (lambda (c) (equal? v c)) s1))

(define (set-insert v s1)
  (set-union (set-singleton v) s1))

(define (set-subset s1 s2)
  (andmap (lambda (v) (set-member v s2)) s1))

(define (set-minus s1 s2)
  (filter (lambda (v) (not (set-member v s2))) s1))
