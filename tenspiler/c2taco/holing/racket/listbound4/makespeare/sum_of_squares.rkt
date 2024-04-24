#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))

(define-grammar (sum_of_squares_inv0_gram arr i n sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? sum (reduce_sum (vec_elemwise_mul (v0) (v0) )) ) ))]
[v0 (choose (list-take-noerr arr i ))]
)

(define-grammar (sum_of_squares_ps_gram arr n sum_of_squares_rv)
 [rv (choose (equal? sum_of_squares_rv (reduce_sum (vec_elemwise_mul (v0) (v0) )) ))]
[v0 (choose (list-take-noerr arr n ))]
)

(define (sum_of_squares_inv0 arr i n sum) (sum_of_squares_inv0_gram arr i n sum #:depth 10))
(define (sum_of_squares_ps arr n sum_of_squares_rv) (sum_of_squares_ps_gram arr n sum_of_squares_rv #:depth 10))

(define-symbolic arr_BOUNDEDSET-len integer?)
(define-symbolic arr_BOUNDEDSET-0 integer?)
(define-symbolic arr_BOUNDEDSET-1 integer?)
(define-symbolic arr_BOUNDEDSET-2 integer?)
(define-symbolic arr_BOUNDEDSET-3 integer?)
(define arr (take (list arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 arr_BOUNDEDSET-2 arr_BOUNDEDSET-3) arr_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic sum integer?)
(define-symbolic sum_of_squares_rv integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= n 1 ) (> (length arr ) 0 ) ) (>= (length arr ) n ) ) (sum_of_squares_inv0 arr 0 n 0) ) (=> (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (> (length arr ) 0 ) ) (>= (length arr ) n ) ) (sum_of_squares_inv0 arr i n sum) ) (sum_of_squares_inv0 arr (+ i 1 ) n (+ sum (* (list-ref-noerr arr i ) (list-ref-noerr arr i ) ) )) ) ) (=> (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (> (length arr ) 0 ) ) (>= (length arr ) n ) ) (sum_of_squares_inv0 arr i n sum) ) (sum_of_squares_ps arr n sum) ) )))


    (define sol0
        (synthesize
            #:forall (list arr_BOUNDEDSET-len arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 arr_BOUNDEDSET-2 arr_BOUNDEDSET-3 i n sum sum_of_squares_rv)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
