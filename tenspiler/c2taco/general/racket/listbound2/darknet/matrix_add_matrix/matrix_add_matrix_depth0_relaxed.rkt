#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (matrix-length matrix_x ) 1 ) (< (length (matrix-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (matrix-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) x )) (matrix_vec_mul (matrix-tail-noerr matrix_x 1 ) x ) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int ) ) ))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (vec_scalar_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) a ) (vec_scalar_sub a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (scalar_vec_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- a (list-ref-noerr x 0 ) ) (scalar_vec_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (matrix_scalar_add a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_add a (matrix-ref-noerr matrix_x 0 ) ) (matrix_scalar_add a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_sub a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_sub a (matrix-ref-noerr matrix_x 0 ) ) (matrix_scalar_sub a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_mul a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_mul a (matrix-ref-noerr matrix_x 0 ) ) (matrix_scalar_mul a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_div a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_div a (matrix-ref-noerr matrix_x 0 ) ) (matrix_scalar_div a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (scalar_matrix_sub a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (scalar_vec_sub a (matrix-ref-noerr matrix_x 0 )) (scalar_matrix_sub a (matrix-tail-noerr matrix_x 1 )) ) ))


 (define-bounded (scalar_matrix_div a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (scalar_vec_div a (matrix-ref-noerr matrix_x 0 )) (scalar_matrix_div a (matrix-tail-noerr matrix_x 1 )) ) ))


 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_add matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_add (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 ) ) (matrix_elemwise_add (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_sub matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_sub (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 ) ) (matrix_elemwise_sub (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_mul matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 ) ) (matrix_elemwise_mul (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_div matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_div (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 ) ) (matrix_elemwise_div (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))

(define-grammar (matrix_add_matrix_inv0_gram agg.result from_matrix i j ref.tmp row_vec to_matrix)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose (matrix-length from_matrix ) (- (matrix-length from_matrix ) 1 ) (+ (matrix-length from_matrix ) 1 ))]
[v2 (choose (v3))]
[v3 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr (v4) (v5) (v5) ) (v5) (v5) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr (v4) (v5) (v5) ) (v5) (v5) ) ))]
[v4 (choose from_matrix to_matrix)]
[v5 (choose (v6))]
[v6 (choose (v7) (- (v7) 1 ) (+ (v7) 1 ))]
[v7 (choose 0 (matrix-length from_matrix ) (length (matrix-ref-noerr from_matrix 0 ) ) i)]
)

(define-grammar (matrix_add_matrix_inv1_gram from_matrix j ref.tmp row_vec to_matrix agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i (v0) ) (< i (v1) ) ) (>= j (v0) ) ) (<= j (v2) ) ) (equal? row_vec (v3) ) ) (equal? agg.result (v9) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose (matrix-length from_matrix ) (- (matrix-length from_matrix ) 1 ) (+ (matrix-length from_matrix ) 1 ))]
[v2 (choose (length (matrix-ref-noerr from_matrix 0 ) ) (- (length (matrix-ref-noerr from_matrix 0 ) ) 1 ) (+ (length (matrix-ref-noerr from_matrix 0 ) ) 1 ))]
[v3 (choose (matrix-ref-noerr (v4) (v6) ))]
[v4 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr (v5) (v6) (v6) ) (v6) (v6) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr (v5) (v6) (v6) ) (v6) (v6) ) ))]
[v5 (choose from_matrix to_matrix)]
[v6 (choose (v7))]
[v7 (choose (v8) (- (v8) 1 ) (+ (v8) 1 ))]
[v8 (choose 0 (matrix-length from_matrix ) (length (matrix-ref-noerr from_matrix 0 ) ) i j)]
[v9 (choose (v4))]
)

(define-grammar (matrix_add_matrix_ps_gram from_matrix to_matrix matrix_add_matrix_rv)
 [rv (choose (equal? matrix_add_matrix_rv (v0) ))]
[v0 (choose (v1))]
[v1 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) ))]
[v2 (choose from_matrix to_matrix)]
[v3 (choose (v4))]
[v4 (choose (v5) (- (v5) 1 ) (+ (v5) 1 ))]
[v5 (choose 0 (matrix-length from_matrix ) (length (matrix-ref-noerr from_matrix 0 ) ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix) (matrix_add_matrix_inv0_gram agg.result from_matrix i j ref.tmp row_vec to_matrix #:depth 10))
(define (matrix_add_matrix_inv1 from_matrix j ref.tmp row_vec to_matrix agg.result i) (matrix_add_matrix_inv1_gram from_matrix j ref.tmp row_vec to_matrix agg.result i #:depth 10))
(define (matrix_add_matrix_ps from_matrix to_matrix matrix_add_matrix_rv) (matrix_add_matrix_ps_gram from_matrix to_matrix matrix_add_matrix_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) (list agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3)) agg.result_BOUNDEDSET-len))
(define-symbolic from_matrix_BOUNDEDSET-len integer?)
(define-symbolic from_matrix_BOUNDEDSET-0 integer?)
(define-symbolic from_matrix_BOUNDEDSET-1 integer?)
(define-symbolic from_matrix_BOUNDEDSET-2 integer?)
(define-symbolic from_matrix_BOUNDEDSET-3 integer?)
(define from_matrix (take (list (list from_matrix_BOUNDEDSET-0 from_matrix_BOUNDEDSET-1) (list from_matrix_BOUNDEDSET-2 from_matrix_BOUNDEDSET-3)) from_matrix_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-len integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-0 integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-1 integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-2 integer?)
(define-symbolic matrix_add_matrix_rv_BOUNDEDSET-3 integer?)
(define matrix_add_matrix_rv (take (list (list matrix_add_matrix_rv_BOUNDEDSET-0 matrix_add_matrix_rv_BOUNDEDSET-1) (list matrix_add_matrix_rv_BOUNDEDSET-2 matrix_add_matrix_rv_BOUNDEDSET-3)) matrix_add_matrix_rv_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(define-symbolic to_matrix_BOUNDEDSET-len integer?)
(define-symbolic to_matrix_BOUNDEDSET-0 integer?)
(define-symbolic to_matrix_BOUNDEDSET-1 integer?)
(define-symbolic to_matrix_BOUNDEDSET-2 integer?)
(define-symbolic to_matrix_BOUNDEDSET-3 integer?)
(define to_matrix (take (list (list to_matrix_BOUNDEDSET-0 to_matrix_BOUNDEDSET-1) (list to_matrix_BOUNDEDSET-2 to_matrix_BOUNDEDSET-3)) to_matrix_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (matrix-length from_matrix ) 1 ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 (matrix-empty ) from_matrix 0 0 0 (list-empty ) to_matrix ) ) (=> (&& (&& (&& (&& (< i (matrix-length from_matrix ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (matrix_add_matrix_inv1 from_matrix 0 ref.tmp (list-empty ) to_matrix agg.result i ) ) ) (=> (&& (&& (&& (&& (&& (&& (< j (length (matrix-ref-noerr from_matrix 0 ) ) ) (< i (matrix-length from_matrix ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (matrix_add_matrix_inv1 from_matrix j ref.tmp row_vec to_matrix agg.result i ) ) (matrix_add_matrix_inv1 from_matrix (+ j 1 ) (+ (list-ref-noerr (matrix-ref-noerr from_matrix i ) j ) (list-ref-noerr (matrix-ref-noerr to_matrix i ) j ) ) (list-append row_vec (+ (list-ref-noerr (matrix-ref-noerr from_matrix i ) j ) (list-ref-noerr (matrix-ref-noerr to_matrix i ) j ) ) ) to_matrix agg.result i ) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< j (length (matrix-ref-noerr from_matrix 0 ) ) ) ) (< i (matrix-length from_matrix ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (matrix_add_matrix_inv1 from_matrix j ref.tmp row_vec to_matrix agg.result i ) ) (matrix_add_matrix_inv0 (matrix-append agg.result row_vec ) from_matrix (+ i 1 ) j ref.tmp row_vec to_matrix ) ) ) (=> (or (&& (&& (&& (&& (! (< i (matrix-length from_matrix ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) (&& (&& (&& (&& (&& (! true ) (! (< i (matrix-length from_matrix ) ) ) ) (> (matrix-length from_matrix ) 1 ) ) (equal? (matrix-length from_matrix ) (matrix-length to_matrix ) ) ) (equal? (length (matrix-ref-noerr from_matrix 0 ) ) (length (matrix-ref-noerr to_matrix 0 ) ) ) ) (matrix_add_matrix_inv0 agg.result from_matrix i j ref.tmp row_vec to_matrix ) ) ) (matrix_add_matrix_ps from_matrix to_matrix agg.result ) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 from_matrix_BOUNDEDSET-len from_matrix_BOUNDEDSET-0 from_matrix_BOUNDEDSET-1 from_matrix_BOUNDEDSET-2 from_matrix_BOUNDEDSET-3 i j matrix_add_matrix_rv_BOUNDEDSET-len matrix_add_matrix_rv_BOUNDEDSET-0 matrix_add_matrix_rv_BOUNDEDSET-1 matrix_add_matrix_rv_BOUNDEDSET-2 matrix_add_matrix_rv_BOUNDEDSET-3 ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 to_matrix_BOUNDEDSET-len to_matrix_BOUNDEDSET-0 to_matrix_BOUNDEDSET-1 to_matrix_BOUNDEDSET-2 to_matrix_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
