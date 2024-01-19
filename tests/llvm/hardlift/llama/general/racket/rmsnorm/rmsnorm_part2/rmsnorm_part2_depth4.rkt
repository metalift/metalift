#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (rmsnorm_part2_inv0_gram agg.result i input ref.tmp ss weight)
 [rv (choose (&& (&& (>= i 0 ) (<= i (length input ) ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (v1) (v17))]
[v1 (choose (v2) (vec_elemwise_add (v2) (v2)) (vec_elemwise_sub (v2) (v2)) (vec_elemwise_mul (v2) (v2)) (vec_elemwise_div (v2) (v2)) (vec_scalar_add (v16) (v2)) (vec_scalar_sub (v16) (v2)) (vec_scalar_mul (v16) (v2)) (vec_scalar_div (v16) (v2)) (scalar_vec_sub (v16) (v2)) (scalar_vec_div (v16) (v2)))]
[v2 (choose (v3) (v15))]
[v3 (choose (v4) (vec_elemwise_add (v4) (v4)) (vec_elemwise_sub (v4) (v4)) (vec_elemwise_mul (v4) (v4)) (vec_elemwise_div (v4) (v4)) (vec_scalar_add (v14) (v4)) (vec_scalar_sub (v14) (v4)) (vec_scalar_mul (v14) (v4)) (vec_scalar_div (v14) (v4)) (scalar_vec_sub (v14) (v4)) (scalar_vec_div (v14) (v4)))]
[v4 (choose (v5) (v13))]
[v5 (choose (v6) (vec_elemwise_add (v6) (v6)) (vec_elemwise_sub (v6) (v6)) (vec_elemwise_mul (v6) (v6)) (vec_elemwise_div (v6) (v6)) (vec_scalar_add (v12) (v6)) (vec_scalar_sub (v12) (v6)) (vec_scalar_mul (v12) (v6)) (vec_scalar_div (v12) (v6)) (scalar_vec_sub (v12) (v6)) (scalar_vec_div (v12) (v6)))]
[v6 (choose (v7) (v11))]
[v7 (choose (v8) (vec_elemwise_add (v8) (v8)) (vec_elemwise_sub (v8) (v8)) (vec_elemwise_mul (v8) (v8)) (vec_elemwise_div (v8) (v8)) (vec_scalar_add (v9) (v8)) (vec_scalar_sub (v9) (v8)) (vec_scalar_mul (v9) (v8)) (vec_scalar_div (v9) (v8)) (scalar_vec_sub (v9) (v8)) (scalar_vec_div (v9) (v8)))]
[v8 (choose (list-slice-noerr input 0 i ) (list-slice-noerr weight 0 i ))]
[v9 (choose (v10) (+ (v10) (v10) ) (- (v10) (v10) ) (* (v10) (v10) ) (quotient-noerr (v10) (v10) ))]
[v10 (choose 1 ss (length input ))]
[v11 (choose (vec_map (v7) map_int_to_int))]
[v12 (choose (v9) (+ (v9) (v9) ) (- (v9) (v9) ) (* (v9) (v9) ) (quotient-noerr (v9) (v9) ))]
[v13 (choose (vec_map (v5) map_int_to_int))]
[v14 (choose (v12) (+ (v12) (v12) ) (- (v12) (v12) ) (* (v12) (v12) ) (quotient-noerr (v12) (v12) ))]
[v15 (choose (vec_map (v3) map_int_to_int))]
[v16 (choose (v14) (+ (v14) (v14) ) (- (v14) (v14) ) (* (v14) (v14) ) (quotient-noerr (v14) (v14) ))]
[v17 (choose (vec_map (v1) map_int_to_int))]
)

(define-grammar (rmsnorm_part2_ps_gram input weight ss rmsnorm_part2_rv)
 [rv (choose (equal? rmsnorm_part2_rv (v0) ))]
[v0 (choose (v1) (v17))]
[v1 (choose (v2) (vec_elemwise_add (v2) (v2)) (vec_elemwise_sub (v2) (v2)) (vec_elemwise_mul (v2) (v2)) (vec_elemwise_div (v2) (v2)) (vec_scalar_add (v16) (v2)) (vec_scalar_sub (v16) (v2)) (vec_scalar_mul (v16) (v2)) (vec_scalar_div (v16) (v2)) (scalar_vec_sub (v16) (v2)) (scalar_vec_div (v16) (v2)))]
[v2 (choose (v3) (v15))]
[v3 (choose (v4) (vec_elemwise_add (v4) (v4)) (vec_elemwise_sub (v4) (v4)) (vec_elemwise_mul (v4) (v4)) (vec_elemwise_div (v4) (v4)) (vec_scalar_add (v14) (v4)) (vec_scalar_sub (v14) (v4)) (vec_scalar_mul (v14) (v4)) (vec_scalar_div (v14) (v4)) (scalar_vec_sub (v14) (v4)) (scalar_vec_div (v14) (v4)))]
[v4 (choose (v5) (v13))]
[v5 (choose (v6) (vec_elemwise_add (v6) (v6)) (vec_elemwise_sub (v6) (v6)) (vec_elemwise_mul (v6) (v6)) (vec_elemwise_div (v6) (v6)) (vec_scalar_add (v12) (v6)) (vec_scalar_sub (v12) (v6)) (vec_scalar_mul (v12) (v6)) (vec_scalar_div (v12) (v6)) (scalar_vec_sub (v12) (v6)) (scalar_vec_div (v12) (v6)))]
[v6 (choose (v7) (v11))]
[v7 (choose (v8) (vec_elemwise_add (v8) (v8)) (vec_elemwise_sub (v8) (v8)) (vec_elemwise_mul (v8) (v8)) (vec_elemwise_div (v8) (v8)) (vec_scalar_add (v9) (v8)) (vec_scalar_sub (v9) (v8)) (vec_scalar_mul (v9) (v8)) (vec_scalar_div (v9) (v8)) (scalar_vec_sub (v9) (v8)) (scalar_vec_div (v9) (v8)))]
[v8 (choose (list-slice-noerr input 0 (length input ) ) (list-slice-noerr weight 0 (length input ) ))]
[v9 (choose (v10) (+ (v10) (v10) ) (- (v10) (v10) ) (* (v10) (v10) ) (quotient-noerr (v10) (v10) ))]
[v10 (choose 1 ss (length input ))]
[v11 (choose (vec_map (v7) map_int_to_int))]
[v12 (choose (v9) (+ (v9) (v9) ) (- (v9) (v9) ) (* (v9) (v9) ) (quotient-noerr (v9) (v9) ))]
[v13 (choose (vec_map (v5) map_int_to_int))]
[v14 (choose (v12) (+ (v12) (v12) ) (- (v12) (v12) ) (* (v12) (v12) ) (quotient-noerr (v12) (v12) ))]
[v15 (choose (vec_map (v3) map_int_to_int))]
[v16 (choose (v14) (+ (v14) (v14) ) (- (v14) (v14) ) (* (v14) (v14) ) (quotient-noerr (v14) (v14) ))]
[v17 (choose (vec_map (v1) map_int_to_int))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) (rmsnorm_part2_inv0_gram agg.result i input ref.tmp ss weight #:depth 10))
(define (rmsnorm_part2_ps input weight ss rmsnorm_part2_rv) (rmsnorm_part2_ps_gram input weight ss rmsnorm_part2_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1) input_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-len integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-0 integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-1 integer?)
(define rmsnorm_part2_rv (take (list rmsnorm_part2_rv_BOUNDEDSET-0 rmsnorm_part2_rv_BOUNDEDSET-1) rmsnorm_part2_rv_BOUNDEDSET-len))
(define-symbolic ss integer?)
(define-symbolic weight_BOUNDEDSET-len integer?)
(define-symbolic weight_BOUNDEDSET-0 integer?)
(define-symbolic weight_BOUNDEDSET-1 integer?)
(define weight (take (list weight_BOUNDEDSET-0 weight_BOUNDEDSET-1) weight_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (equal? (length input ) (length weight ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 (list-empty ) 0 input 0 ss weight) ) (=> (&& (&& (&& (< i (length input ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) ) (rmsnorm_part2_inv0 (list-append agg.result (* (* (quotient-noerr 1 (integer-sqrt-noerr (+ (quotient-noerr ss (length input ) ) 1 ) ) ) (list-ref-noerr input i ) ) (list-ref-noerr weight i ) ) ) (+ i 1 ) input (* (* (quotient-noerr 1 (integer-sqrt-noerr (+ (quotient-noerr ss (length input ) ) 1 ) ) ) (list-ref-noerr input i ) ) (list-ref-noerr weight i ) ) ss weight) ) ) (=> (or (&& (&& (&& (! (< i (length input ) ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) ) (&& (&& (&& (&& (! true ) (! (< i (length input ) ) ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) ) ) (rmsnorm_part2_ps input weight ss agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 ref.tmp rmsnorm_part2_rv_BOUNDEDSET-len rmsnorm_part2_rv_BOUNDEDSET-0 rmsnorm_part2_rv_BOUNDEDSET-1 ss weight_BOUNDEDSET-len weight_BOUNDEDSET-0 weight_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
