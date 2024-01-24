#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (transformer_part4_inv0_gram agg.result hidden_dim i input1 input2 ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i hidden_dim ) ) (equal? agg.result (vec_elemwise_mul (v0) (v0)) ) ))]
[v0 (choose (list-take-noerr input1 i ) (list-take-noerr input2 i ))]
)

(define-grammar (transformer_part4_ps_gram input1 input2 hidden_dim transformer_part4_rv)
 [rv (choose (equal? transformer_part4_rv (vec_elemwise_mul (v0) (v0)) ))]
[v0 (choose (list-take-noerr input1 hidden_dim ) (list-take-noerr input2 hidden_dim ))]
)

(define (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp) (transformer_part4_inv0_gram agg.result hidden_dim i input1 input2 ref.tmp #:depth 10))
(define (transformer_part4_ps input1 input2 hidden_dim transformer_part4_rv) (transformer_part4_ps_gram input1 input2 hidden_dim transformer_part4_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define-symbolic agg.result_BOUNDEDSET-4 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4) agg.result_BOUNDEDSET-len))
(define-symbolic hidden_dim integer?)
(define-symbolic i integer?)
(define-symbolic input1_BOUNDEDSET-len integer?)
(define-symbolic input1_BOUNDEDSET-0 integer?)
(define-symbolic input1_BOUNDEDSET-1 integer?)
(define-symbolic input1_BOUNDEDSET-2 integer?)
(define-symbolic input1_BOUNDEDSET-3 integer?)
(define-symbolic input1_BOUNDEDSET-4 integer?)
(define input1 (take (list input1_BOUNDEDSET-0 input1_BOUNDEDSET-1 input1_BOUNDEDSET-2 input1_BOUNDEDSET-3 input1_BOUNDEDSET-4) input1_BOUNDEDSET-len))
(define-symbolic input2_BOUNDEDSET-len integer?)
(define-symbolic input2_BOUNDEDSET-0 integer?)
(define-symbolic input2_BOUNDEDSET-1 integer?)
(define-symbolic input2_BOUNDEDSET-2 integer?)
(define-symbolic input2_BOUNDEDSET-3 integer?)
(define-symbolic input2_BOUNDEDSET-4 integer?)
(define input2 (take (list input2_BOUNDEDSET-0 input2_BOUNDEDSET-1 input2_BOUNDEDSET-2 input2_BOUNDEDSET-3 input2_BOUNDEDSET-4) input2_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic transformer_part4_rv_BOUNDEDSET-len integer?)
(define-symbolic transformer_part4_rv_BOUNDEDSET-0 integer?)
(define-symbolic transformer_part4_rv_BOUNDEDSET-1 integer?)
(define-symbolic transformer_part4_rv_BOUNDEDSET-2 integer?)
(define-symbolic transformer_part4_rv_BOUNDEDSET-3 integer?)
(define-symbolic transformer_part4_rv_BOUNDEDSET-4 integer?)
(define transformer_part4_rv (take (list transformer_part4_rv_BOUNDEDSET-0 transformer_part4_rv_BOUNDEDSET-1 transformer_part4_rv_BOUNDEDSET-2 transformer_part4_rv_BOUNDEDSET-3 transformer_part4_rv_BOUNDEDSET-4) transformer_part4_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= hidden_dim 0 ) (>= (length input1 ) hidden_dim ) ) (>= (length input2 ) hidden_dim ) ) (transformer_part4_inv0 (list-empty ) hidden_dim 0 input1 input2 0) ) (=> (&& (&& (&& (&& (< i hidden_dim ) (>= hidden_dim 0 ) ) (>= (length input1 ) hidden_dim ) ) (>= (length input2 ) hidden_dim ) ) (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp) ) (transformer_part4_inv0 (list-append agg.result (* (list-ref-noerr input1 i ) (list-ref-noerr input2 i ) ) ) hidden_dim (+ i 1 ) input1 input2 (* (list-ref-noerr input1 i ) (list-ref-noerr input2 i ) )) ) ) (=> (or (&& (&& (&& (&& (! (< i hidden_dim ) ) (>= hidden_dim 0 ) ) (>= (length input1 ) hidden_dim ) ) (>= (length input2 ) hidden_dim ) ) (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp) ) (&& (&& (&& (&& (&& (! true ) (! (< i hidden_dim ) ) ) (>= hidden_dim 0 ) ) (>= (length input1 ) hidden_dim ) ) (>= (length input2 ) hidden_dim ) ) (transformer_part4_inv0 agg.result hidden_dim i input1 input2 ref.tmp) ) ) (transformer_part4_ps input1 input2 hidden_dim agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 hidden_dim i input1_BOUNDEDSET-len input1_BOUNDEDSET-0 input1_BOUNDEDSET-1 input1_BOUNDEDSET-2 input1_BOUNDEDSET-3 input1_BOUNDEDSET-4 input2_BOUNDEDSET-len input2_BOUNDEDSET-0 input2_BOUNDEDSET-1 input2_BOUNDEDSET-2 input2_BOUNDEDSET-3 input2_BOUNDEDSET-4 ref.tmp transformer_part4_rv_BOUNDEDSET-len transformer_part4_rv_BOUNDEDSET-0 transformer_part4_rv_BOUNDEDSET-1 transformer_part4_rv_BOUNDEDSET-2 transformer_part4_rv_BOUNDEDSET-3 transformer_part4_rv_BOUNDEDSET-4)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
