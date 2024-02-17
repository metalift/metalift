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


 (define-bounded (reduce_max x)
(if (<= (length x ) 1 ) (list-ref-noerr x 0 ) (if (> (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_mul x)
(if (< (length x ) 1 ) 1 (* (list-ref-noerr x 0 ) (reduce_mul (list-tail-noerr x 1 )) ) ))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (list-list-length matrix_x ) 1 ) (< (length (list-list-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (list-list-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (list-list-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (list-list-tail-noerr matrix_x 1 ) x ) ) ))

(define-grammar (matmul_inv0_gram agg.result col curr input row weight)
 [rv (choose (&& (&& (>= row (v0) ) (<= row (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose (list-list-length weight ) (- (list-list-length weight ) 1 ) (+ (list-list-length weight ) 1 ))]
[v2 (choose (v3))]
[v3 (choose (list-slice-noerr input (v4) (v4) ) (list-list-ref-noerr (v7) (v4) ))]
[v4 (choose (v5))]
[v5 (choose (v6) (- (v6) 1 ) (+ (v6) 1 ))]
[v6 (choose 0 row (list-list-length weight ) (length input ))]
[v7 (choose (list-list-col-slice-noerr (list-list-slice-noerr weight (v4) (v4) ) (v4) (v4) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr weight (v4) (v4) ) (v4) (v4) ) ))]
)

(define-grammar (matmul_inv1_gram col curr input weight agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= row (v0) ) (< row (v1) ) ) (>= col (v0) ) ) (<= col (v2) ) ) (equal? curr (v3) ) ) (equal? agg.result (v4) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose (list-list-length weight ) (- (list-list-length weight ) 1 ) (+ (list-list-length weight ) 1 ))]
[v2 (choose (length input ) (- (length input ) 1 ) (+ (length input ) 1 ))]
[v3 (choose (reduce_sum (v4)) (reduce_mul (v4)) (reduce_max (v4)))]
[v4 (choose (v5))]
[v5 (choose (list-slice-noerr input (v6) (v6) ) (list-list-ref-noerr (v9) (v6) ))]
[v6 (choose (v7))]
[v7 (choose (v8) (- (v8) 1 ) (+ (v8) 1 ))]
[v8 (choose 0 row (list-list-length weight ) (length input ))]
[v9 (choose (list-list-col-slice-noerr (list-list-slice-noerr weight (v6) (v6) ) (v6) (v6) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr weight (v6) (v6) ) (v6) (v6) ) ))]
)

(define-grammar (matmul_ps_gram weight input matmul_rv)
 [rv (choose (equal? matmul_rv (v0) ))]
[v0 (choose (v1))]
[v1 (choose (list-slice-noerr input (v2) (v2) ) (list-list-ref-noerr (v5) (v2) ))]
[v2 (choose (v3))]
[v3 (choose (v4) (- (v4) 1 ) (+ (v4) 1 ))]
[v4 (choose 0 (list-list-length weight ) (length input ))]
[v5 (choose (list-list-col-slice-noerr (list-list-slice-noerr weight (v2) (v2) ) (v2) (v2) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr weight (v2) (v2) ) (v2) (v2) ) ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (matmul_inv0 agg.result col curr input row weight) (matmul_inv0_gram agg.result col curr input row weight #:depth 10))
(define (matmul_inv1 col curr input weight agg.result row) (matmul_inv1_gram col curr input weight agg.result row #:depth 10))
(define (matmul_ps weight input matmul_rv) (matmul_ps_gram weight input matmul_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic col integer?)
(define-symbolic curr integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1) input_BOUNDEDSET-len))
(define-symbolic matmul_rv_BOUNDEDSET-len integer?)
(define-symbolic matmul_rv_BOUNDEDSET-0 integer?)
(define-symbolic matmul_rv_BOUNDEDSET-1 integer?)
(define matmul_rv (take (list matmul_rv_BOUNDEDSET-0 matmul_rv_BOUNDEDSET-1) matmul_rv_BOUNDEDSET-len))
(define-symbolic row integer?)
(define-symbolic weight_BOUNDEDSET-len integer?)
(define-symbolic weight_BOUNDEDSET-0 integer?)
(define-symbolic weight_BOUNDEDSET-1 integer?)
(define-symbolic weight_BOUNDEDSET-2 integer?)
(define-symbolic weight_BOUNDEDSET-3 integer?)
(define weight (take (list (list weight_BOUNDEDSET-0 weight_BOUNDEDSET-1) (list weight_BOUNDEDSET-2 weight_BOUNDEDSET-3)) weight_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length weight ) 0 ) (> (length (list-list-ref-noerr weight 0 ) ) 0 ) ) (equal? (length (list-list-ref-noerr weight 0 ) ) (length input ) ) ) (matmul_inv0 (list-empty ) 0 0 input 0 weight) ) (=> (&& (&& (&& (&& (< row (list-list-length weight ) ) (> (list-list-length weight ) 0 ) ) (> (length (list-list-ref-noerr weight 0 ) ) 0 ) ) (equal? (length (list-list-ref-noerr weight 0 ) ) (length input ) ) ) (matmul_inv0 agg.result col curr input row weight) ) (matmul_inv1 0 0 input weight agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (< col (length input ) ) (< row (list-list-length weight ) ) ) (> (list-list-length weight ) 0 ) ) (> (length (list-list-ref-noerr weight 0 ) ) 0 ) ) (equal? (length (list-list-ref-noerr weight 0 ) ) (length input ) ) ) (matmul_inv0 agg.result col curr input row weight) ) (matmul_inv1 col curr input weight agg.result row) ) (matmul_inv1 (+ col 1 ) (+ curr (* (list-ref-noerr (list-list-ref-noerr weight row ) col ) (list-ref-noerr input col ) ) ) input weight agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length input ) ) ) (< row (list-list-length weight ) ) ) (> (list-list-length weight ) 0 ) ) (> (length (list-list-ref-noerr weight 0 ) ) 0 ) ) (equal? (length (list-list-ref-noerr weight 0 ) ) (length input ) ) ) (matmul_inv0 agg.result col curr input row weight) ) (matmul_inv1 col curr input weight agg.result row) ) (matmul_inv0 (list-append agg.result curr ) col curr input (+ row 1 ) weight) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length weight ) ) ) (> (list-list-length weight ) 0 ) ) (> (length (list-list-ref-noerr weight 0 ) ) 0 ) ) (equal? (length (list-list-ref-noerr weight 0 ) ) (length input ) ) ) (matmul_inv0 agg.result col curr input row weight) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length weight ) ) ) ) (> (list-list-length weight ) 0 ) ) (> (length (list-list-ref-noerr weight 0 ) ) 0 ) ) (equal? (length (list-list-ref-noerr weight 0 ) ) (length input ) ) ) (matmul_inv0 agg.result col curr input row weight) ) ) (matmul_ps weight input agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 col curr input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 matmul_rv_BOUNDEDSET-len matmul_rv_BOUNDEDSET-0 matmul_rv_BOUNDEDSET-1 row weight_BOUNDEDSET-len weight_BOUNDEDSET-0 weight_BOUNDEDSET-1 weight_BOUNDEDSET-2 weight_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
