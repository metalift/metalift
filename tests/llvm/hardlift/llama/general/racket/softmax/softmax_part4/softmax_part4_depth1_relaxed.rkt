#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 )) ) ))

(define-grammar (softmax_part4_inv0_gram agg.result i max_pos ref.tmp sum unnormalized_output)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose max_pos (- max_pos 1 ) (+ max_pos 1 ))]
[v2 (choose (v3) (v5))]
[v3 (choose (list-slice-noerr unnormalized_output (v0) (v4) ))]
[v4 (choose i (- i 1 ) (+ i 1 ))]
[v5 (choose (v6) (vec_elemwise_add (v3) (v3)) (vec_elemwise_sub (v3) (v3)) (vec_elemwise_mul (v3) (v3)) (vec_elemwise_div (v3) (v3)) (vec_scalar_add (v7) (v3)) (vec_scalar_sub (v7) (v3)) (vec_scalar_mul (v7) (v3)) (vec_scalar_div (v7) (v3)) (scalar_vec_sub (v7) (v3)) (scalar_vec_div (v7) (v3)))]
[v6 (choose (vec_map (v3) map_int_to_int))]
[v7 (choose sum max_pos)]
)

(define-grammar (softmax_part4_ps_gram unnormalized_output max_pos sum softmax_part4_rv)
 [rv (choose (equal? softmax_part4_rv (v0) ))]
[v0 (choose (v1) (v4))]
[v1 (choose (list-slice-noerr unnormalized_output (v2) (v3) ))]
[v2 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v3 (choose max_pos (- max_pos 1 ) (+ max_pos 1 ))]
[v4 (choose (v5) (vec_elemwise_add (v1) (v1)) (vec_elemwise_sub (v1) (v1)) (vec_elemwise_mul (v1) (v1)) (vec_elemwise_div (v1) (v1)) (vec_scalar_add (v6) (v1)) (vec_scalar_sub (v6) (v1)) (vec_scalar_mul (v6) (v1)) (vec_scalar_div (v6) (v1)) (scalar_vec_sub (v6) (v1)) (scalar_vec_div (v6) (v1)))]
[v5 (choose (vec_map (v1) map_int_to_int))]
[v6 (choose sum max_pos)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) (softmax_part4_inv0_gram agg.result i max_pos ref.tmp sum unnormalized_output #:depth 10))
(define (softmax_part4_ps unnormalized_output max_pos sum softmax_part4_rv) (softmax_part4_ps_gram unnormalized_output max_pos sum softmax_part4_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic max_pos integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-len integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-0 integer?)
(define-symbolic softmax_part4_rv_BOUNDEDSET-1 integer?)
(define softmax_part4_rv (take (list softmax_part4_rv_BOUNDEDSET-0 softmax_part4_rv_BOUNDEDSET-1) softmax_part4_rv_BOUNDEDSET-len))
(define-symbolic sum integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-len integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-0 integer?)
(define-symbolic unnormalized_output_BOUNDEDSET-1 integer?)
(define unnormalized_output (take (list unnormalized_output_BOUNDEDSET-0 unnormalized_output_BOUNDEDSET-1) unnormalized_output_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (> (length unnormalized_output ) 0 ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 (list-empty ) 0 max_pos 0 sum unnormalized_output) ) (=> (&& (&& (&& (&& (< i max_pos ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) (softmax_part4_inv0 (list-append agg.result (quotient-noerr (list-ref-noerr unnormalized_output i ) sum ) ) (+ i 1 ) max_pos (quotient-noerr (list-ref-noerr unnormalized_output i ) sum ) sum unnormalized_output) ) ) (=> (or (&& (&& (&& (&& (! (< i max_pos ) ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) (&& (&& (&& (&& (&& (! true ) (! (< i max_pos ) ) ) (> (length unnormalized_output ) 0 ) ) (<= max_pos (length unnormalized_output ) ) ) (>= max_pos 1 ) ) (softmax_part4_inv0 agg.result i max_pos ref.tmp sum unnormalized_output) ) ) (softmax_part4_ps unnormalized_output max_pos sum agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 i max_pos ref.tmp softmax_part4_rv_BOUNDEDSET-len softmax_part4_rv_BOUNDEDSET-0 softmax_part4_rv_BOUNDEDSET-1 sum unnormalized_output_BOUNDEDSET-len unnormalized_output_BOUNDEDSET-0 unnormalized_output_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
