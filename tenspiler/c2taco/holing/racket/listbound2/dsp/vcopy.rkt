#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


(define-grammar (vcopy_inv0_gram a agg.result i n)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (list-take-noerr a i ))]
)

(define-grammar (vcopy_ps_gram a n vcopy_rv)
 [rv (choose (equal? vcopy_rv (v0) ))]
[v0 (choose (list-take-noerr a n ))]
)

(define (vcopy_inv0 a agg.result i n) (vcopy_inv0_gram a agg.result i n #:depth 10))
(define (vcopy_ps a n vcopy_rv) (vcopy_ps_gram a n vcopy_rv #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1) a_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic vcopy_rv_BOUNDEDSET-len integer?)
(define-symbolic vcopy_rv_BOUNDEDSET-0 integer?)
(define-symbolic vcopy_rv_BOUNDEDSET-1 integer?)
(define vcopy_rv (take (list vcopy_rv_BOUNDEDSET-0 vcopy_rv_BOUNDEDSET-1) vcopy_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length a ) n ) ) (vcopy_inv0 a (list-empty ) 0 n) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length a ) n ) ) (vcopy_inv0 a agg.result i n) ) (vcopy_inv0 a (list-append agg.result (list-ref-noerr a i ) ) (+ i 1 ) n) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length a ) n ) ) (vcopy_inv0 a agg.result i n) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length a ) n ) ) (vcopy_inv0 a agg.result i n) ) ) (vcopy_ps a n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 i n vcopy_rv_BOUNDEDSET-len vcopy_rv_BOUNDEDSET-0 vcopy_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
