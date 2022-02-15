#lang rosette
(require "../utils/bounded.rkt")
(require "../utils/utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)



 (define-symbolic uninterp (~> integer? integer? integer?)) 

(define-grammar (test_gram tmp9 arg arg1)
 [rv (choose (equal? tmp9 (+ (uninterp arg arg) (uninterp arg1 arg1) ) ))]

) 

(define (test tmp9 arg arg1) (test_gram tmp9 arg arg1 #:depth 10))

(define-symbolic test_tmp3 integer?)
(define-symbolic test_arg1 integer?)
(define-symbolic test_tmp5 integer?)
(define-symbolic test_tmp6 integer?)
(define-symbolic test_arg integer?)
(define-symbolic test_tmp7 integer?)
(define-symbolic test_tmp4 integer?)
(define-symbolic test_tmp8 integer?)
(define-symbolic test_bb boolean?)
(current-bitwidth 6)
(define (assertions)
 (assert (=> (&& (equal? test_bb (=> (&& (&& (equal? test_tmp3 test_arg ) (equal? test_tmp5 (uninterp test_arg test_arg) ) (equal? test_tmp6 test_arg1 ) (equal? test_tmp7 test_arg1 ) (equal? test_tmp4 test_arg ) (equal? test_tmp8 (uninterp test_arg1 test_arg1) ) ) (&& true true true ) ) (test (+ (uninterp test_arg test_arg) (uninterp test_arg1 test_arg1) ) test_arg test_arg1) ) ) ) test_bb )))

(define sol
 (synthesize
 #:forall (list test_tmp3 test_arg1 test_tmp5 test_tmp6 test_arg test_tmp7 test_tmp4 test_tmp8 test_bb)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
