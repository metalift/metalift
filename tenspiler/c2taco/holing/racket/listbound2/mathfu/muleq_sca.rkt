#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))

(define-grammar (muleq_sca_inv0_gram a agg.result b i n ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_scalar_mul (v0) (v1)) ) ))]
[v0 (choose b)]
[v1 (choose (list-take-noerr a i ))]
)

(define-grammar (muleq_sca_ps_gram a b n muleq_sca_rv)
 [rv (choose (equal? muleq_sca_rv (vec_scalar_mul (v0) (v1)) ))]
[v0 (choose b)]
[v1 (choose (list-take-noerr a n ))]
)

(define (muleq_sca_inv0 a agg.result b i n ref.tmp) (muleq_sca_inv0_gram a agg.result b i n ref.tmp #:depth 10))
(define (muleq_sca_ps a b n muleq_sca_rv) (muleq_sca_ps_gram a b n muleq_sca_rv #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1) a_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic b integer?)
(define-symbolic i integer?)
(define-symbolic muleq_sca_rv_BOUNDEDSET-len integer?)
(define-symbolic muleq_sca_rv_BOUNDEDSET-0 integer?)
(define-symbolic muleq_sca_rv_BOUNDEDSET-1 integer?)
(define muleq_sca_rv (take (list muleq_sca_rv_BOUNDEDSET-0 muleq_sca_rv_BOUNDEDSET-1) muleq_sca_rv_BOUNDEDSET-len))
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length a ) n ) ) (muleq_sca_inv0 a (list-empty ) b 0 n 0) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length a ) n ) ) (muleq_sca_inv0 a agg.result b i n ref.tmp) ) (muleq_sca_inv0 a (list-append agg.result (* (list-ref-noerr a i ) b ) ) b (+ i 1 ) n (* (list-ref-noerr a i ) b )) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length a ) n ) ) (muleq_sca_inv0 a agg.result b i n ref.tmp) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length a ) n ) ) (muleq_sca_inv0 a agg.result b i n ref.tmp) ) ) (muleq_sca_ps a b n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 b i muleq_sca_rv_BOUNDEDSET-len muleq_sca_rv_BOUNDEDSET-0 muleq_sca_rv_BOUNDEDSET-1 n ref.tmp)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
