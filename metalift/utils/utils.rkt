#lang rosette/safe

(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)

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
  (cons i l))

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

(define (set-eq s1 s2)
  (equal? s1 s2))

(define (set-union as bs)
  (match* (as bs)
    [((list) bs)  bs]
    [(as (list))  as]
    [((list a as ...) (list b bs ...))
     (if (equal? a b)
      (set-union (cons a as) bs)
      (if (< a b)
         (cons a (set-union as (cons b bs)))
         (cons b (set-union (cons a as) bs)))
     )]))

(define (set-member v s1)
  (ormap (lambda (c) (equal? v c)) s1))

(define (set-insert v s1)
  (set-union (set-singleton v) s1))

(define (set-subset s1 s2)
  (match* (s1 s2)
    [((list) bs)  #t]
    [(as (list))  #f]
    [((list a as ...) (list b bs ...))
     (if (equal? a b)
      (set-subset as bs)
      (if (< a b)
         #f
         (set-subset (cons a as) bs))
     )]))

(define (set-minus s1 s2)
  (match* (s1 s2)
    [((list) bs)  (list)]
    [(as (list))  as]
    [((list a as ...) (list b bs ...))
     (if (equal? a b)
      (set-minus as bs)
      (if (< a b)
         (cons a (set-minus as (cons b bs)))
         (set-minus (cons a as) bs))
     )]))

; map functions

(define (map-create)
  (list))

(define (map-normalize m)
  (match* (m)
    [((list)) (map-create)]
    [((list a as ...))
     (map-insert (map-normalize as) (car a) (cdr a) (lambda (a b) b))
     ]))

(define (map-eq s1 s2)
  (equal? s1 s2))

(define (map-union as bs value-merge)
  (match* (as bs)
    [((list) bs)  bs]
    [(as (list))  as]
    [((list a as ...) (list b bs ...))
     (if (equal? (car a) (car b))
      (cons (cons (car a) (value-merge (cdr a) (cdr b))) (map-union as bs value-merge))
      (if (< (car a) (car b))
         (cons a (map-union as (cons b bs) value-merge))
         (cons b (map-union (cons a as) bs value-merge)))
     )]))

(define (map-get m k default)
  (match* (m)
    [((list)) default]
    [((list a as ...))
     (if (equal? (car a) k)
      (cdr a)
      (map-get as k default)
     )]))

(define (map-singleton k v)
  (list (cons k v)))

(define (map-insert m k v value-merge)
  (map-union (map-singleton k v) m value-merge))

(define (map-minus m keys)
  (match* (m keys)
    [((list) bs)  (list)]
    [(as (list))  as]
    [((list a as ...) (list b bs ...))
     (if (equal? (car a) b)
      (map-minus as bs)
      (if (< (car a) b)
         (cons a (map-minus as (cons b bs)))
         (map-minus (cons a as) bs))
     )]))

(define (map-values m)
  (map (lambda (a) (cdr a)) m))


;nested list functions
(define (list-list-ref-noerr l i)
  (if (&&  (>= i 0) (< i (length l))) (list-ref l i)
      (list)))

(define (list-list-tail-noerr l i)
  (if (&& (>= i 0) (<= i (length l))) (list-tail l i)
      (list)))

(define (list-list-prepend i l)
  (if (list? i)
    (if (> (length i ) 0)
    (append (list i) l) (append l i)) (append (list i) l) ))

(define (list-list-take-noerr l i)
  (if (<= i 0) (list) (if (&& (>= i 0) (< i (length l))) (take l i) l )))

(define (list-list-length l) (length l))

(define (list-list-append l i)
(append l (list i)))

(define (list-list-empty)
  (list))