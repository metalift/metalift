#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/sahilbhatia/Documents/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))

(define-grammar (pluseq_inv0_gram a agg.result b i n ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_elemwise_add (v0) (v0) ) ) ))]
[v0 (choose (list-take-noerr a i ) (list-take-noerr b i ))]
)

(define-grammar (pluseq_ps_gram a b n pluseq_rv)
 [rv (choose (equal? pluseq_rv (vec_elemwise_add (v0) (v0) ) ))]
[v0 (choose (list-take-noerr a n ) (list-take-noerr b n ))]
)

(define (pluseq_inv0 a agg.result b i n ref.tmp) (pluseq_inv0_gram a agg.result b i n ref.tmp #:depth 10))
(define (pluseq_ps a b n pluseq_rv) (pluseq_ps_gram a b n pluseq_rv #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define-symbolic a_BOUNDEDSET-2 integer?)
(define-symbolic a_BOUNDEDSET-3 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1 a_BOUNDEDSET-2 a_BOUNDEDSET-3) a_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) agg.result_BOUNDEDSET-len))
(define-symbolic b_BOUNDEDSET-len integer?)
(define-symbolic b_BOUNDEDSET-0 integer?)
(define-symbolic b_BOUNDEDSET-1 integer?)
(define-symbolic b_BOUNDEDSET-2 integer?)
(define-symbolic b_BOUNDEDSET-3 integer?)
(define b (take (list b_BOUNDEDSET-0 b_BOUNDEDSET-1 b_BOUNDEDSET-2 b_BOUNDEDSET-3) b_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic pluseq_rv_BOUNDEDSET-len integer?)
(define-symbolic pluseq_rv_BOUNDEDSET-0 integer?)
(define-symbolic pluseq_rv_BOUNDEDSET-1 integer?)
(define-symbolic pluseq_rv_BOUNDEDSET-2 integer?)
(define-symbolic pluseq_rv_BOUNDEDSET-3 integer?)
(define pluseq_rv (take (list pluseq_rv_BOUNDEDSET-0 pluseq_rv_BOUNDEDSET-1 pluseq_rv_BOUNDEDSET-2 pluseq_rv_BOUNDEDSET-3) pluseq_rv_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= n 1 ) (>= (length a ) n ) ) (>= (length b ) n ) ) (pluseq_inv0 a (list-empty ) b 0 n 0) ) (=> (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length a ) n ) ) (>= (length b ) n ) ) (pluseq_inv0 a agg.result b i n ref.tmp) ) (pluseq_inv0 a (list-append agg.result (+ (list-ref-noerr a i ) (list-ref-noerr b i ) ) ) b (+ i 1 ) n (+ (list-ref-noerr a i ) (list-ref-noerr b i ) )) ) ) (=> (or (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length a ) n ) ) (>= (length b ) n ) ) (pluseq_inv0 a agg.result b i n ref.tmp) ) (&& (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length a ) n ) ) (>= (length b ) n ) ) (pluseq_inv0 a agg.result b i n ref.tmp) ) ) (pluseq_ps a b n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 a_BOUNDEDSET-2 a_BOUNDEDSET-3 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 b_BOUNDEDSET-2 b_BOUNDEDSET-3 i n pluseq_rv_BOUNDEDSET-len pluseq_rv_BOUNDEDSET-0 pluseq_rv_BOUNDEDSET-1 pluseq_rv_BOUNDEDSET-2 pluseq_rv_BOUNDEDSET-3 ref.tmp)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
