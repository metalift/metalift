#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)



 (define-bounded (my_add x y) 
(+ x y )) 

(define-grammar (test_gram i8 arg arg1)
 [rv (choose (equal? i8 (my_add arg arg1) ))]

) 

(define (test i8 arg arg1) (test_gram i8 arg arg1 #:depth 10))

(define-symbolic test_arg integer?)
(define-symbolic test_arg1 integer?)
(define-symbolic test_bb boolean?)
(define-symbolic test_i4 integer?)
(define-symbolic test_i5 integer?)
(define-symbolic test_i6 integer?)
(define-symbolic test_i7 integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (=> (&& (equal? test_bb (=> (&& (&& (equal? test_i4 test_arg ) (equal? test_i5 test_arg1 ) (equal? test_i6 test_arg ) (equal? test_i7 test_arg1 ) ) (&& true true true ) ) (test (+ test_arg test_arg1 ) test_arg test_arg1) ) ) ) test_bb )))

(define sol
 (synthesize
 #:forall (list test_arg test_arg1 test_bb test_i4 test_i5 test_i6 test_i7)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
