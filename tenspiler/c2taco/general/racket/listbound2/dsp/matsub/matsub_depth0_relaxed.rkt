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

(define-grammar (matsub_inv0_gram agg.result i j m matA matB n ref.tmp row_vec)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose m (- m 1 ) (+ m 1 ))]
[v2 (choose (v3))]
[v3 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr (v4) (v5) (v5) ) (v5) (v5) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr (v4) (v5) (v5) ) (v5) (v5) ) ))]
[v4 (choose matA matB)]
[v5 (choose (v6))]
[v6 (choose (v7) (- (v7) 1 ) (+ (v7) 1 ))]
[v7 (choose 0 m n i)]
)

(define-grammar (matsub_inv1_gram j m matA matB n ref.tmp row_vec agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i (v0) ) (< i (v1) ) ) (>= j (v0) ) ) (<= j (v2) ) ) (equal? row_vec (v3) ) ) (equal? agg.result (v9) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose m (- m 1 ) (+ m 1 ))]
[v2 (choose n (- n 1 ) (+ n 1 ))]
[v3 (choose (matrix-ref-noerr (v4) (v6) ))]
[v4 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr (v5) (v6) (v6) ) (v6) (v6) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr (v5) (v6) (v6) ) (v6) (v6) ) ))]
[v5 (choose matA matB)]
[v6 (choose (v7))]
[v7 (choose (v8) (- (v8) 1 ) (+ (v8) 1 ))]
[v8 (choose 0 m n i j)]
[v9 (choose (v4))]
)

(define-grammar (matsub_ps_gram matA matB m n matsub_rv)
 [rv (choose (equal? matsub_rv (v0) ))]
[v0 (choose (v1))]
[v1 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) ))]
[v2 (choose matA matB)]
[v3 (choose (v4))]
[v4 (choose (v5) (- (v5) 1 ) (+ (v5) 1 ))]
[v5 (choose 0 m n)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) (matsub_inv0_gram agg.result i j m matA matB n ref.tmp row_vec #:depth 10))
(define (matsub_inv1 j m matA matB n ref.tmp row_vec agg.result i) (matsub_inv1_gram j m matA matB n ref.tmp row_vec agg.result i #:depth 10))
(define (matsub_ps matA matB m n matsub_rv) (matsub_ps_gram matA matB m n matsub_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) (list agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3)) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic m integer?)
(define-symbolic matA_BOUNDEDSET-len integer?)
(define-symbolic matA_BOUNDEDSET-0 integer?)
(define-symbolic matA_BOUNDEDSET-1 integer?)
(define-symbolic matA_BOUNDEDSET-2 integer?)
(define-symbolic matA_BOUNDEDSET-3 integer?)
(define matA (take (list (list matA_BOUNDEDSET-0 matA_BOUNDEDSET-1) (list matA_BOUNDEDSET-2 matA_BOUNDEDSET-3)) matA_BOUNDEDSET-len))
(define-symbolic matB_BOUNDEDSET-len integer?)
(define-symbolic matB_BOUNDEDSET-0 integer?)
(define-symbolic matB_BOUNDEDSET-1 integer?)
(define-symbolic matB_BOUNDEDSET-2 integer?)
(define-symbolic matB_BOUNDEDSET-3 integer?)
(define matB (take (list (list matB_BOUNDEDSET-0 matB_BOUNDEDSET-1) (list matB_BOUNDEDSET-2 matB_BOUNDEDSET-3)) matB_BOUNDEDSET-len))
(define-symbolic matsub_rv_BOUNDEDSET-len integer?)
(define-symbolic matsub_rv_BOUNDEDSET-0 integer?)
(define-symbolic matsub_rv_BOUNDEDSET-1 integer?)
(define-symbolic matsub_rv_BOUNDEDSET-2 integer?)
(define-symbolic matsub_rv_BOUNDEDSET-3 integer?)
(define matsub_rv (take (list (list matsub_rv_BOUNDEDSET-0 matsub_rv_BOUNDEDSET-1) (list matsub_rv_BOUNDEDSET-2 matsub_rv_BOUNDEDSET-3)) matsub_rv_BOUNDEDSET-len))
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (&& (&& (>= m 1 ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 (matrix-empty ) 0 0 m matA matB n 0 (list-empty )) ) (=> (&& (&& (&& (&& (&& (&& (&& (< i m ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (matsub_inv1 0 m matA matB n ref.tmp (list-empty ) agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (< j n ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (matsub_inv1 j m matA matB n ref.tmp row_vec agg.result i) ) (matsub_inv1 (+ j 1 ) m matA matB n (- (list-ref-noerr (matrix-ref-noerr matA i ) j ) (list-ref-noerr (matrix-ref-noerr matB i ) j ) ) (list-append row_vec (- (list-ref-noerr (matrix-ref-noerr matA i ) j ) (list-ref-noerr (matrix-ref-noerr matB i ) j ) ) ) agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (&& (! (< j n ) ) (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (matsub_inv1 j m matA matB n ref.tmp row_vec agg.result i) ) (matsub_inv0 (matrix-append agg.result row_vec ) (+ i 1 ) j m matA matB n ref.tmp row_vec) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (! (< i m ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) (&& (&& (&& (&& (&& (&& (&& (&& (! true ) (! (< i m ) ) ) (>= m 1 ) ) (>= n 1 ) ) (>= (matrix-length matA ) m ) ) (>= (matrix-length matB ) m ) ) (>= (length (matrix-ref-noerr matA 0 ) ) n ) ) (>= (length (matrix-ref-noerr matB 0 ) ) n ) ) (matsub_inv0 agg.result i j m matA matB n ref.tmp row_vec) ) ) (matsub_ps matA matB m n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 i j m matA_BOUNDEDSET-len matA_BOUNDEDSET-0 matA_BOUNDEDSET-1 matA_BOUNDEDSET-2 matA_BOUNDEDSET-3 matB_BOUNDEDSET-len matB_BOUNDEDSET-0 matB_BOUNDEDSET-1 matB_BOUNDEDSET-2 matB_BOUNDEDSET-3 matsub_rv_BOUNDEDSET-len matsub_rv_BOUNDEDSET-0 matsub_rv_BOUNDEDSET-1 matsub_rv_BOUNDEDSET-2 matsub_rv_BOUNDEDSET-3 n ref.tmp row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
