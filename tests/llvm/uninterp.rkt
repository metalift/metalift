#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)



 (define-symbolic uninterp (~> integer? integer? integer?)) 

(define-grammar (test_gram i9 arg arg1)
 [rv (choose (equal? i9 (+ (uninterp arg arg) (uninterp arg1 arg1) ) ))]

) 

(define (test i9 arg arg1) (test_gram i9 arg arg1 #:depth 10))

(define-symbolic test_arg integer?)
(define-symbolic test_arg1 integer?)
(define-symbolic test_bb boolean?)
(define-symbolic test_i3 integer?)
(define-symbolic test_i4 integer?)
(define-symbolic test_i5 integer?)
(define-symbolic test_i6 integer?)
(define-symbolic test_i7 integer?)
(define-symbolic test_i8 integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (=> (&& (equal? test_bb (=> (&& (&& (equal? test_i3 test_arg ) (equal? test_i4 test_arg ) (equal? test_i5 (uninterp test_arg test_arg) ) (equal? test_i6 test_arg1 ) (equal? test_i7 test_arg1 ) (equal? test_i8 (uninterp test_arg1 test_arg1) ) ) (&& true true true ) ) (test (+ (uninterp test_arg test_arg) (uninterp test_arg1 test_arg1) ) test_arg test_arg1) ) ) ) test_bb )))

(define sol
 (synthesize
 #:forall (list test_arg test_arg1 test_bb test_i3 test_i4 test_i5 test_i6 test_i7 test_i8)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
