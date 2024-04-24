#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))

(define-grammar (array_sum_inv0_gram arr i n sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? sum (reduce_sum (v0)) ) ))]
[v0 (choose (list-take-noerr arr i ))]
)

(define-grammar (array_sum_ps_gram arr n array_sum_rv)
 [rv (choose (equal? array_sum_rv (reduce_sum (v0)) ))]
[v0 (choose (list-take-noerr arr n ))]
)

(define (array_sum_inv0 arr i n sum) (array_sum_inv0_gram arr i n sum #:depth 10))
(define (array_sum_ps arr n array_sum_rv) (array_sum_ps_gram arr n array_sum_rv #:depth 10))

(define-symbolic arr_BOUNDEDSET-len integer?)
(define-symbolic arr_BOUNDEDSET-0 integer?)
(define-symbolic arr_BOUNDEDSET-1 integer?)
(define arr (take (list arr_BOUNDEDSET-0 arr_BOUNDEDSET-1) arr_BOUNDEDSET-len))
(define-symbolic array_sum_rv integer?)
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= n 1 ) (> (length arr ) 0 ) ) (>= (length arr ) n ) ) (array_sum_inv0 arr 0 n 0) ) (=> (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (> (length arr ) 0 ) ) (>= (length arr ) n ) ) (array_sum_inv0 arr i n sum) ) (array_sum_inv0 arr (+ i 1 ) n (+ sum (list-ref-noerr arr i ) )) ) ) (=> (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (> (length arr ) 0 ) ) (>= (length arr ) n ) ) (array_sum_inv0 arr i n sum) ) (array_sum_ps arr n sum) ) )))


    (define sol0
        (synthesize
            #:forall (list arr_BOUNDEDSET-len arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 array_sum_rv i n sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
