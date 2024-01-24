#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (scalar_vec_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- a (list-ref-noerr x 0 ) ) (scalar_vec_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int) ) ))

(define-grammar (transformer_part3_inv0_gram agg.result curr hidden_dim i input)
 [rv (choose (&& (&& (>= i 0 ) (<= i hidden_dim ) ) (equal? agg.result (vec_elemwise_mul (v0) (scalar_vec_div (v1) (vec_scalar_add (v1) (vec_map (scalar_vec_sub 0 (v0)) map_int_to_int)))) ) ))]
[v0 (choose (list-take-noerr input i ))]
[v1 (choose 1)]
)

(define-grammar (transformer_part3_ps_gram input hidden_dim transformer_part3_rv)
 [rv (choose (equal? transformer_part3_rv (vec_elemwise_mul (v0) (scalar_vec_div (v1) (vec_scalar_add (v1) (vec_map (scalar_vec_sub 0 (v0)) map_int_to_int)))) ))]
[v0 (choose (list-take-noerr input hidden_dim ))]
[v1 (choose 1)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ))]
)

(define (transformer_part3_inv0 agg.result curr hidden_dim i input) (transformer_part3_inv0_gram agg.result curr hidden_dim i input #:depth 10))
(define (transformer_part3_ps input hidden_dim transformer_part3_rv) (transformer_part3_ps_gram input hidden_dim transformer_part3_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) agg.result_BOUNDEDSET-len))
(define-symbolic curr integer?)
(define-symbolic hidden_dim integer?)
(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define-symbolic input_BOUNDEDSET-2 integer?)
(define-symbolic input_BOUNDEDSET-3 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3) input_BOUNDEDSET-len))
(define-symbolic transformer_part3_rv_BOUNDEDSET-len integer?)
(define-symbolic transformer_part3_rv_BOUNDEDSET-0 integer?)
(define-symbolic transformer_part3_rv_BOUNDEDSET-1 integer?)
(define-symbolic transformer_part3_rv_BOUNDEDSET-2 integer?)
(define-symbolic transformer_part3_rv_BOUNDEDSET-3 integer?)
(define transformer_part3_rv (take (list transformer_part3_rv_BOUNDEDSET-0 transformer_part3_rv_BOUNDEDSET-1 transformer_part3_rv_BOUNDEDSET-2 transformer_part3_rv_BOUNDEDSET-3) transformer_part3_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= hidden_dim 0 ) (>= (length input ) hidden_dim ) ) (transformer_part3_inv0 (list-empty ) 0 hidden_dim 0 input) ) (=> (&& (&& (&& (< i hidden_dim ) (>= hidden_dim 0 ) ) (>= (length input ) hidden_dim ) ) (transformer_part3_inv0 agg.result curr hidden_dim i input) ) (transformer_part3_inv0 (list-append agg.result (* (list-ref-noerr input i ) (quotient-noerr 1 (+ 1 (integer-exp-noerr (- 0 (list-ref-noerr input i ) ) ) ) ) ) ) (* (list-ref-noerr input i ) (quotient-noerr 1 (+ 1 (integer-exp-noerr (- 0 (list-ref-noerr input i ) ) ) ) ) ) hidden_dim (+ i 1 ) input) ) ) (=> (or (&& (&& (&& (! (< i hidden_dim ) ) (>= hidden_dim 0 ) ) (>= (length input ) hidden_dim ) ) (transformer_part3_inv0 agg.result curr hidden_dim i input) ) (&& (&& (&& (&& (! true ) (! (< i hidden_dim ) ) ) (>= hidden_dim 0 ) ) (>= (length input ) hidden_dim ) ) (transformer_part3_inv0 agg.result curr hidden_dim i input) ) ) (transformer_part3_ps input hidden_dim agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 curr hidden_dim i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3 transformer_part3_rv_BOUNDEDSET-len transformer_part3_rv_BOUNDEDSET-0 transformer_part3_rv_BOUNDEDSET-1 transformer_part3_rv_BOUNDEDSET-2 transformer_part3_rv_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
