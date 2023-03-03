#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)



 (define-bounded (multiply arg1 arg2) 
(if (equal? (length arg1 ) 0 ) (list-empty ) (list-prepend (* (list-ref-noerr arg1 0 ) (list-ref-noerr arg2 0 ) ) (multiply (list-tail-noerr arg1 1 ) (list-tail-noerr arg2 1 )) ) )) 

(define-grammar (inv0_gram i3 i4 arg arg1)
 [rv (choose (&& (v0) (&& (v2) (v3) ) ))]
[v0 (choose (equal? i3 (multiply (list-take-noerr (v1) i4 ) (list-take-noerr (v1) i4 )) ))]
[v1 (choose arg arg1)]
[v2 (choose (>= i4 (length arg ) ) (<= i4 (length arg ) ) (> i4 (length arg ) ) (< i4 (length arg ) ) (equal? i4 (length arg ) ))]
[v3 (choose (<= i4 (v4) ) (> i4 (v4) ) (>= i4 (v4) ) (< i4 (v4) ) (equal? i4 (v4) ))]
[v4 (choose 0 1)]
) 

(define-grammar (test_gram i25 arg arg1)
 [rv (choose (v0))]
[v0 (choose (equal? i25 (multiply (v1) (v1)) ))]
[v1 (choose arg arg1)]
) 

(define (inv0 i3 i4 arg arg1) (inv0_gram i3 i4 arg arg1 #:depth 10))
(define (test i25 arg arg1) (test_gram i25 arg arg1 #:depth 10))

(define-symbolic test_arg_BOUNDEDSET-0 integer?)
(define-symbolic test_arg_BOUNDEDSET-1 integer?)
(define-symbolic test_arg_BOUNDEDSET-len integer?)
(define test_arg (take (list test_arg_BOUNDEDSET-0 test_arg_BOUNDEDSET-1) test_arg_BOUNDEDSET-len))
(define-symbolic test_arg1_BOUNDEDSET-0 integer?)
(define-symbolic test_arg1_BOUNDEDSET-1 integer?)
(define-symbolic test_arg1_BOUNDEDSET-len integer?)
(define test_arg1 (take (list test_arg1_BOUNDEDSET-0 test_arg1_BOUNDEDSET-1) test_arg1_BOUNDEDSET-len))
(define-symbolic test_bb boolean?)
(define-symbolic test_bb11 boolean?)
(define-symbolic test_bb21 boolean?)
(define-symbolic test_bb24 boolean?)
(define-symbolic test_bb26 boolean?)
(define-symbolic test_bb27 boolean?)
(define-symbolic test_bb6 boolean?)
(define-symbolic test_i10 boolean?)
(define-symbolic test_i12_BOUNDEDSET-0 integer?)
(define-symbolic test_i12_BOUNDEDSET-1 integer?)
(define-symbolic test_i12_BOUNDEDSET-len integer?)
(define test_i12 (take (list test_i12_BOUNDEDSET-0 test_i12_BOUNDEDSET-1) test_i12_BOUNDEDSET-len))
(define-symbolic test_i13_BOUNDEDSET-0 integer?)
(define-symbolic test_i13_BOUNDEDSET-1 integer?)
(define-symbolic test_i13_BOUNDEDSET-len integer?)
(define test_i13 (take (list test_i13_BOUNDEDSET-0 test_i13_BOUNDEDSET-1) test_i13_BOUNDEDSET-len))
(define-symbolic test_i14 integer?)
(define-symbolic test_i15 integer?)
(define-symbolic test_i16_BOUNDEDSET-0 integer?)
(define-symbolic test_i16_BOUNDEDSET-1 integer?)
(define-symbolic test_i16_BOUNDEDSET-len integer?)
(define test_i16 (take (list test_i16_BOUNDEDSET-0 test_i16_BOUNDEDSET-1) test_i16_BOUNDEDSET-len))
(define-symbolic test_i17 integer?)
(define-symbolic test_i18 integer?)
(define-symbolic test_i20_BOUNDEDSET-0 integer?)
(define-symbolic test_i20_BOUNDEDSET-1 integer?)
(define-symbolic test_i20_BOUNDEDSET-len integer?)
(define test_i20 (take (list test_i20_BOUNDEDSET-0 test_i20_BOUNDEDSET-1) test_i20_BOUNDEDSET-len))
(define-symbolic test_i22 integer?)
(define-symbolic test_i25_BOUNDEDSET-0 integer?)
(define-symbolic test_i25_BOUNDEDSET-1 integer?)
(define-symbolic test_i25_BOUNDEDSET-len integer?)
(define test_i25 (take (list test_i25_BOUNDEDSET-0 test_i25_BOUNDEDSET-1) test_i25_BOUNDEDSET-len))
(define-symbolic test_i3_0_BOUNDEDSET-0 integer?)
(define-symbolic test_i3_0_BOUNDEDSET-1 integer?)
(define-symbolic test_i3_0_BOUNDEDSET-len integer?)
(define test_i3_0 (take (list test_i3_0_BOUNDEDSET-0 test_i3_0_BOUNDEDSET-1) test_i3_0_BOUNDEDSET-len))
(define-symbolic test_i4_1 integer?)
(define-symbolic test_i5_BOUNDEDSET-0 integer?)
(define-symbolic test_i5_BOUNDEDSET-1 integer?)
(define-symbolic test_i5_BOUNDEDSET-len integer?)
(define test_i5 (take (list test_i5_BOUNDEDSET-0 test_i5_BOUNDEDSET-1) test_i5_BOUNDEDSET-len))
(define-symbolic test_i7 integer?)
(define-symbolic test_i8_BOUNDEDSET-0 integer?)
(define-symbolic test_i8_BOUNDEDSET-1 integer?)
(define-symbolic test_i8_BOUNDEDSET-len integer?)
(define test_i8 (take (list test_i8_BOUNDEDSET-0 test_i8_BOUNDEDSET-1) test_i8_BOUNDEDSET-len))
(define-symbolic test_i9 integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (=> (&& (equal? test_bb (=> (equal? test_i5 (list-empty ) ) (&& test_bb6 ( inv0 (list-empty ) 0 test_arg test_arg1 ) ) ) ) (equal? test_bb11 (=> (&& (&& (equal? test_i12 test_i3_0 ) (equal? test_i13 test_arg ) (equal? test_i14 test_i4_1 ) (equal? test_i15 (list-ref-noerr test_arg test_i4_1 ) ) (equal? test_i16 test_arg1 ) (equal? test_i17 test_i4_1 ) (equal? test_i18 (list-ref-noerr test_arg1 test_i4_1 ) ) (equal? test_i20 (list-append test_i3_0 (* (list-ref-noerr test_arg test_i4_1 ) (list-ref-noerr test_arg1 test_i4_1 ) ) ) ) ) (&& ( inv0 test_i3_0 test_i4_1 test_arg test_arg1 ) (< test_i4_1 (length test_arg ) ) ) ) test_bb21 ) ) (equal? test_bb21 (=> (&& (equal? test_i22 test_i4_1 ) (&& ( inv0 test_i3_0 test_i4_1 test_arg test_arg1 ) (< test_i4_1 (length test_arg ) ) ) ) ( inv0 (list-append test_i3_0 (* (list-ref-noerr test_arg test_i4_1 ) (list-ref-noerr test_arg1 test_i4_1 ) ) ) (+ test_i4_1 1 ) test_arg test_arg1 ) ) ) (equal? test_bb24 (=> (&& (equal? test_i25 test_i3_0 ) (&& ( inv0 test_i3_0 test_i4_1 test_arg test_arg1 ) (! (< test_i4_1 (length test_arg ) ) ) ) ) (test test_i3_0 test_arg test_arg1) ) ) (equal? test_bb26 (=> (&& ( inv0 test_i3_0 test_i4_1 test_arg test_arg1 ) (< test_i4_1 (length test_arg ) ) ) test_bb11 ) ) (equal? test_bb27 (=> (&& ( inv0 test_i3_0 test_i4_1 test_arg test_arg1 ) (! (< test_i4_1 (length test_arg ) ) ) ) test_bb24 ) ) (equal? test_bb6 (=> (&& (&& (equal? test_i10 (< test_i4_1 (length test_arg ) ) ) (equal? test_i7 test_i4_1 ) (equal? test_i8 test_arg ) (equal? test_i9 (length test_arg ) ) ) ( inv0 test_i3_0 test_i4_1 test_arg test_arg1 ) ) (&& test_bb27 test_bb26 ) ) ) ) test_bb )))

(define sol
 (synthesize
 #:forall (list test_arg_BOUNDEDSET-0 test_arg_BOUNDEDSET-1 test_arg_BOUNDEDSET-len test_arg1_BOUNDEDSET-0 test_arg1_BOUNDEDSET-1 test_arg1_BOUNDEDSET-len test_bb test_bb11 test_bb21 test_bb24 test_bb26 test_bb27 test_bb6 test_i10 test_i12_BOUNDEDSET-0 test_i12_BOUNDEDSET-1 test_i12_BOUNDEDSET-len test_i13_BOUNDEDSET-0 test_i13_BOUNDEDSET-1 test_i13_BOUNDEDSET-len test_i14 test_i15 test_i16_BOUNDEDSET-0 test_i16_BOUNDEDSET-1 test_i16_BOUNDEDSET-len test_i17 test_i18 test_i20_BOUNDEDSET-0 test_i20_BOUNDEDSET-1 test_i20_BOUNDEDSET-len test_i22 test_i25_BOUNDEDSET-0 test_i25_BOUNDEDSET-1 test_i25_BOUNDEDSET-len test_i3_0_BOUNDEDSET-0 test_i3_0_BOUNDEDSET-1 test_i3_0_BOUNDEDSET-len test_i4_1 test_i5_BOUNDEDSET-0 test_i5_BOUNDEDSET-1 test_i5_BOUNDEDSET-len test_i7 test_i8_BOUNDEDSET-0 test_i8_BOUNDEDSET-1 test_i8_BOUNDEDSET-len test_i9)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
