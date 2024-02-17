#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) a ) (vec_scalar_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- a (list-ref-noerr x 0 ) ) (scalar_vec_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int) ) ))

(define-grammar (rmsnorm_part2_inv0_gram agg.result i input ref.tmp ss weight)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose (length input ) (- (length input ) 1 ) (+ (length input ) 1 ))]
[v2 (choose (v3) (v7))]
[v3 (choose (list-slice-noerr input (v4) (v4) ) (list-slice-noerr weight (v4) (v4) ))]
[v4 (choose (v5) (v6))]
[v5 (choose 0 (length input ) i 1 ss)]
[v6 (choose (integer-sqrt-noerr (v5) ) (integer-exp-noerr (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v7 (choose (v8) (vec_elemwise_add (v3) (v3)) (vec_elemwise_sub (v3) (v3)) (vec_elemwise_mul (v3) (v3)) (vec_elemwise_div (v3) (v3)) (vec_scalar_add (v9) (v3)) (vec_scalar_sub (v9) (v3)) (vec_scalar_mul (v9) (v3)) (vec_scalar_div (v9) (v3)) (scalar_vec_sub (v9) (v3)) (scalar_vec_div (v9) (v3)))]
[v8 (choose (vec_map (v3) map_int_to_int))]
[v9 (choose 1 ss (length input ))]
)

(define-grammar (rmsnorm_part2_ps_gram input weight ss rmsnorm_part2_rv)
 [rv (choose (equal? rmsnorm_part2_rv (v0) ))]
[v0 (choose (v1) (v5))]
[v1 (choose (list-slice-noerr input (v2) (v2) ) (list-slice-noerr weight (v2) (v2) ))]
[v2 (choose (v3) (v4))]
[v3 (choose 0 (length input ) 1 ss)]
[v4 (choose (integer-sqrt-noerr (v3) ) (integer-exp-noerr (v3) ) (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v5 (choose (v6) (vec_elemwise_add (v1) (v1)) (vec_elemwise_sub (v1) (v1)) (vec_elemwise_mul (v1) (v1)) (vec_elemwise_div (v1) (v1)) (vec_scalar_add (v7) (v1)) (vec_scalar_sub (v7) (v1)) (vec_scalar_mul (v7) (v1)) (vec_scalar_div (v7) (v1)) (scalar_vec_sub (v7) (v1)) (scalar_vec_div (v7) (v1)))]
[v6 (choose (vec_map (v1) map_int_to_int))]
[v7 (choose 1 ss (length input ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) (rmsnorm_part2_inv0_gram agg.result i input ref.tmp ss weight #:depth 10))
(define (rmsnorm_part2_ps input weight ss rmsnorm_part2_rv) (rmsnorm_part2_ps_gram input weight ss rmsnorm_part2_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

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
