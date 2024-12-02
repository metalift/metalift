#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (mag_array_inv0_gram a i n sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? sum (reduce_sum (vec_elemwise_mul (v0) (v0))) ) ))]
[v0 (choose (list-take-noerr a i ))]
)

(define-grammar (mag_array_ps_gram a n mag_array_rv)
 [rv (choose (equal? mag_array_rv (reduce_sum (vec_elemwise_mul (v0) (v0))) ))]
[v0 (choose (list-take-noerr a n ))]
)

(define (mag_array_inv0 a i n sum) (mag_array_inv0_gram a i n sum #:depth 10))
(define (mag_array_ps a n mag_array_rv) (mag_array_ps_gram a n mag_array_rv #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1) a_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic mag_array_rv integer?)
(define-symbolic n integer?)
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= n 1 ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (mag_array_inv0 a 0 n 0) ) (=> (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (mag_array_inv0 a i n sum) ) (mag_array_inv0 a (+ i 1 ) n (+ sum (* (list-ref-noerr a i ) (list-ref-noerr a i ) ) )) ) ) (=> (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (mag_array_inv0 a i n sum) ) (mag_array_ps a n sum) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 i mag_array_rv n sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
