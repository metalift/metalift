#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))

(define-grammar (dot_inv0_gram a b i n sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? sum (reduce_sum (vec_elemwise_mul (v0) (v0) )) ) ))]
[v0 (choose (list-take-noerr a i ) (list-take-noerr b i ))]
)

(define-grammar (dot_ps_gram a b n dot_rv)
 [rv (choose (equal? dot_rv (reduce_sum (vec_elemwise_mul (v0) (v0) )) ))]
[v0 (choose (list-take-noerr a n ) (list-take-noerr b n ))]
)

(define (dot_inv0 a b i n sum) (dot_inv0_gram a b i n sum #:depth 10))
(define (dot_ps a b n dot_rv) (dot_ps_gram a b n dot_rv #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define-symbolic a_BOUNDEDSET-2 integer?)
(define-symbolic a_BOUNDEDSET-3 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1 a_BOUNDEDSET-2 a_BOUNDEDSET-3) a_BOUNDEDSET-len))
(define-symbolic b_BOUNDEDSET-len integer?)
(define-symbolic b_BOUNDEDSET-0 integer?)
(define-symbolic b_BOUNDEDSET-1 integer?)
(define-symbolic b_BOUNDEDSET-2 integer?)
(define-symbolic b_BOUNDEDSET-3 integer?)
(define b (take (list b_BOUNDEDSET-0 b_BOUNDEDSET-1 b_BOUNDEDSET-2 b_BOUNDEDSET-3) b_BOUNDEDSET-len))
(define-symbolic dot_rv integer?)
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (&& (&& (>= n 1 ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (> (length b ) 0 ) ) (>= (length b ) n ) ) (dot_inv0 a b 0 n 0) ) (=> (&& (&& (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (> (length b ) 0 ) ) (>= (length b ) n ) ) (dot_inv0 a b i n sum) ) (dot_inv0 a b (+ i 1 ) n (+ sum (* (list-ref-noerr a i ) (list-ref-noerr b i ) ) )) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (> (length b ) 0 ) ) (>= (length b ) n ) ) (dot_inv0 a b i n sum) ) (dot_ps a b n sum) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 a_BOUNDEDSET-2 a_BOUNDEDSET-3 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 b_BOUNDEDSET-2 b_BOUNDEDSET-3 dot_rv i n sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
