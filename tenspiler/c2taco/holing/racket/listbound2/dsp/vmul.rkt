#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (vmul_inv0_gram a agg.result b i n ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_elemwise_mul (v0) (v0)) ) ))]
[v0 (choose (list-take-noerr a i ) (list-take-noerr b i ))]
)

(define-grammar (vmul_ps_gram a b n vmul_rv)
 [rv (choose (equal? vmul_rv (vec_elemwise_mul (v0) (v0)) ))]
[v0 (choose (list-take-noerr a n ) (list-take-noerr b n ))]
)

(define (vmul_inv0 a agg.result b i n ref.tmp) (vmul_inv0_gram a agg.result b i n ref.tmp #:depth 10))
(define (vmul_ps a b n vmul_rv) (vmul_ps_gram a b n vmul_rv #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1) a_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic b_BOUNDEDSET-len integer?)
(define-symbolic b_BOUNDEDSET-0 integer?)
(define-symbolic b_BOUNDEDSET-1 integer?)
(define b (take (list b_BOUNDEDSET-0 b_BOUNDEDSET-1) b_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic vmul_rv_BOUNDEDSET-len integer?)
(define-symbolic vmul_rv_BOUNDEDSET-0 integer?)
(define-symbolic vmul_rv_BOUNDEDSET-1 integer?)
(define vmul_rv (take (list vmul_rv_BOUNDEDSET-0 vmul_rv_BOUNDEDSET-1) vmul_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= n 1 ) (>= (length a ) n ) ) (>= (length b ) n ) ) (vmul_inv0 a (list-empty ) b 0 n 0) ) (=> (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length a ) n ) ) (>= (length b ) n ) ) (vmul_inv0 a agg.result b i n ref.tmp) ) (vmul_inv0 a (list-append agg.result (* (list-ref-noerr a i ) (list-ref-noerr b i ) ) ) b (+ i 1 ) n (* (list-ref-noerr a i ) (list-ref-noerr b i ) )) ) ) (=> (or (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length a ) n ) ) (>= (length b ) n ) ) (vmul_inv0 a agg.result b i n ref.tmp) ) (&& (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length a ) n ) ) (>= (length b ) n ) ) (vmul_inv0 a agg.result b i n ref.tmp) ) ) (vmul_ps a b n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 i n ref.tmp vmul_rv_BOUNDEDSET-len vmul_rv_BOUNDEDSET-0 vmul_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
