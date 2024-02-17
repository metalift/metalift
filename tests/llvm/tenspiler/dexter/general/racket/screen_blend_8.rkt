#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



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


 (define-bounded (matrix_scalar_add a matrix_x)
(if (< (list-list-length matrix_x ) 1 ) (list-list-empty ) (list-list-prepend (vec_scalar_add a (list-list-ref-noerr matrix_x 0 )) (matrix_scalar_add a (list-list-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_sub a matrix_x)
(if (< (list-list-length matrix_x ) 1 ) (list-list-empty ) (list-list-prepend (vec_scalar_sub a (list-list-ref-noerr matrix_x 0 )) (matrix_scalar_sub a (list-list-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_mul a matrix_x)
(if (< (list-list-length matrix_x ) 1 ) (list-list-empty ) (list-list-prepend (vec_scalar_mul a (list-list-ref-noerr matrix_x 0 )) (matrix_scalar_mul a (list-list-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_div a matrix_x)
(if (< (list-list-length matrix_x ) 1 ) (list-list-empty ) (list-list-prepend (vec_scalar_div a (list-list-ref-noerr matrix_x 0 )) (matrix_scalar_div a (list-list-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (scalar_matrix_sub a matrix_x)
(if (< (list-list-length matrix_x ) 1 ) (list-list-empty ) (list-list-prepend (scalar_vec_sub a (list-list-ref-noerr matrix_x 0 )) (scalar_matrix_sub a (list-list-tail-noerr matrix_x 1 )) ) ))


 (define-bounded (scalar_matrix_div a matrix_x)
(if (< (list-list-length matrix_x ) 1 ) (list-list-empty ) (list-list-prepend (scalar_vec_div a (list-list-ref-noerr matrix_x 0 )) (scalar_matrix_div a (list-list-tail-noerr matrix_x 1 )) ) ))


 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (matrix_elemwise_add matrix_x matrix_y)
(if (or (< (list-list-length matrix_x ) 1 ) (! (equal? (list-list-length matrix_x ) (list-list-length matrix_y ) ) ) ) (list-list-empty ) (list-list-prepend (vec_elemwise_add (list-list-ref-noerr matrix_x 0 ) (list-list-ref-noerr matrix_y 0 )) (matrix_elemwise_add (list-list-tail-noerr matrix_x 1 ) (list-list-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_sub matrix_x matrix_y)
(if (or (< (list-list-length matrix_x ) 1 ) (! (equal? (list-list-length matrix_x ) (list-list-length matrix_y ) ) ) ) (list-list-empty ) (list-list-prepend (vec_elemwise_sub (list-list-ref-noerr matrix_x 0 ) (list-list-ref-noerr matrix_y 0 )) (matrix_elemwise_sub (list-list-tail-noerr matrix_x 1 ) (list-list-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_mul matrix_x matrix_y)
(if (or (< (list-list-length matrix_x ) 1 ) (! (equal? (list-list-length matrix_x ) (list-list-length matrix_y ) ) ) ) (list-list-empty ) (list-list-prepend (vec_elemwise_mul (list-list-ref-noerr matrix_x 0 ) (list-list-ref-noerr matrix_y 0 )) (matrix_elemwise_mul (list-list-tail-noerr matrix_x 1 ) (list-list-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_div matrix_x matrix_y)
(if (or (< (list-list-length matrix_x ) 1 ) (! (equal? (list-list-length matrix_x ) (list-list-length matrix_y ) ) ) ) (list-list-empty ) (list-list-prepend (vec_elemwise_div (list-list-ref-noerr matrix_x 0 ) (list-list-ref-noerr matrix_y 0 )) (matrix_elemwise_div (list-list-tail-noerr matrix_x 1 ) (list-list-tail-noerr matrix_y 1 ) ) ) ))

(define-grammar (screen_blend_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (v1) (v3) (v5) (v7))]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v2) row ) (list-list-col-slice-noerr (v2) 0 row ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v2) row ) (list-list-col-slice-noerr (v2) 0 row ) ) ))]
[v2 (choose base active)]
[v3 (choose (matrix_elemwise_add (v1) (v1) ) (matrix_elemwise_sub (v1) (v1) ) (matrix_elemwise_mul (v1) (v1) ) (matrix_elemwise_div (v1) (v1) ) (matrix_scalar_add (v4) (v1) ) (matrix_scalar_sub (v4) (v1) ) (matrix_scalar_mul (v4) (v1) ) (matrix_scalar_div (v4) (v1) ) (scalar_matrix_sub (v4) (v1)) (scalar_matrix_div (v4) (v1)))]
[v4 (choose 32)]
[v5 (choose (matrix_elemwise_add (v3) (v1) ) (matrix_elemwise_sub (v3) (v1) ) (matrix_elemwise_mul (v3) (v1) ) (matrix_elemwise_div (v3) (v1) ) (matrix_scalar_add (v4) (v3) ) (matrix_scalar_sub (v4) (v3) ) (matrix_scalar_mul (v4) (v3) ) (matrix_scalar_div (v4) (v3) ) (scalar_matrix_sub (v4) (v3)) (scalar_matrix_div (v4) (v3)) (matrix_elemwise_sub (v1) (v3) ) (matrix_elemwise_div (v1) (v3) ) (matrix_scalar_add (v6) (v1) ) (matrix_scalar_sub (v6) (v1) ) (matrix_scalar_mul (v6) (v1) ) (matrix_scalar_div (v6) (v1) ) (scalar_matrix_sub (v6) (v1)) (scalar_matrix_div (v6) (v1)) (matrix_elemwise_add (v3) (v3) ) (matrix_elemwise_sub (v3) (v3) ) (matrix_elemwise_mul (v3) (v3) ) (matrix_elemwise_div (v3) (v3) ) (matrix_scalar_add (v6) (v3) ) (matrix_scalar_sub (v6) (v3) ) (matrix_scalar_mul (v6) (v3) ) (matrix_scalar_div (v6) (v3) ) (scalar_matrix_sub (v6) (v3)) (scalar_matrix_div (v6) (v3)))]
[v6 (choose (+ (v4) (v4) ) (- (v4) (v4) ) (* (v4) (v4) ) (quotient-noerr (v4) (v4) ))]
[v7 (choose (matrix_elemwise_add (v5) (v1) ) (matrix_elemwise_sub (v5) (v1) ) (matrix_elemwise_mul (v5) (v1) ) (matrix_elemwise_div (v5) (v1) ) (matrix_scalar_add (v4) (v5) ) (matrix_scalar_sub (v4) (v5) ) (matrix_scalar_mul (v4) (v5) ) (matrix_scalar_div (v4) (v5) ) (scalar_matrix_sub (v4) (v5)) (scalar_matrix_div (v4) (v5)) (matrix_elemwise_sub (v1) (v5) ) (matrix_elemwise_div (v1) (v5) ) (matrix_scalar_add (v8) (v1) ) (matrix_scalar_sub (v8) (v1) ) (matrix_scalar_mul (v8) (v1) ) (matrix_scalar_div (v8) (v1) ) (scalar_matrix_sub (v8) (v1)) (scalar_matrix_div (v8) (v1)) (matrix_elemwise_add (v5) (v3) ) (matrix_elemwise_sub (v5) (v3) ) (matrix_elemwise_mul (v5) (v3) ) (matrix_elemwise_div (v5) (v3) ) (matrix_scalar_add (v6) (v5) ) (matrix_scalar_sub (v6) (v5) ) (matrix_scalar_mul (v6) (v5) ) (matrix_scalar_div (v6) (v5) ) (scalar_matrix_sub (v6) (v5)) (scalar_matrix_div (v6) (v5)) (matrix_elemwise_sub (v3) (v5) ) (matrix_elemwise_div (v3) (v5) ) (matrix_scalar_add (v8) (v3) ) (matrix_scalar_sub (v8) (v3) ) (matrix_scalar_mul (v8) (v3) ) (matrix_scalar_div (v8) (v3) ) (scalar_matrix_sub (v8) (v3)) (scalar_matrix_div (v8) (v3)) (matrix_elemwise_add (v5) (v5) ) (matrix_elemwise_sub (v5) (v5) ) (matrix_elemwise_mul (v5) (v5) ) (matrix_elemwise_div (v5) (v5) ) (matrix_scalar_add (v8) (v5) ) (matrix_scalar_sub (v8) (v5) ) (matrix_scalar_mul (v8) (v5) ) (matrix_scalar_div (v8) (v5) ) (scalar_matrix_sub (v8) (v5)) (scalar_matrix_div (v8) (v5)))]
[v8 (choose (+ (v6) (v4) ) (- (v6) (v4) ) (* (v6) (v4) ) (quotient-noerr (v6) (v4) ) (- (v4) (v6) ) (quotient-noerr (v4) (v6) ) (+ (v6) (v6) ) (- (v6) (v6) ) (* (v6) (v6) ) (quotient-noerr (v6) (v6) ))]
)

(define-grammar (screen_blend_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (>= col 0 ) ) (<= col (length (list-list-ref-noerr base 0 ) ) ) ) (equal? row_vec (v0) ) ) (equal? agg.result (v8) ) ))]
[v0 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (v2) (v4) (v6))]
[v1 (choose base active)]
[v2 (choose (vec_elemwise_add (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_sub (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_mul (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_div (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_add (v3) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_sub (v3) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_mul (v3) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_div (v3) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (scalar_vec_sub (v3) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (scalar_vec_div (v3) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )))]
[v3 (choose 32)]
[v4 (choose (vec_elemwise_add (v2) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_sub (v2) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_mul (v2) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_div (v2) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_add (v3) (v2)) (vec_scalar_sub (v3) (v2)) (vec_scalar_mul (v3) (v2)) (vec_scalar_div (v3) (v2)) (scalar_vec_sub (v3) (v2)) (scalar_vec_div (v3) (v2)) (vec_elemwise_sub (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (v2)) (vec_elemwise_div (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (v2)) (vec_scalar_add (v5) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_sub (v5) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_mul (v5) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_div (v5) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (scalar_vec_sub (v5) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (scalar_vec_div (v5) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_add (v2) (v2)) (vec_elemwise_sub (v2) (v2)) (vec_elemwise_mul (v2) (v2)) (vec_elemwise_div (v2) (v2)) (vec_scalar_add (v5) (v2)) (vec_scalar_sub (v5) (v2)) (vec_scalar_mul (v5) (v2)) (vec_scalar_div (v5) (v2)) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v5 (choose (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v6 (choose (vec_elemwise_add (v4) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_sub (v4) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_mul (v4) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_div (v4) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_add (v3) (v4)) (vec_scalar_sub (v3) (v4)) (vec_scalar_mul (v3) (v4)) (vec_scalar_div (v3) (v4)) (scalar_vec_sub (v3) (v4)) (scalar_vec_div (v3) (v4)) (vec_elemwise_sub (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (v4)) (vec_elemwise_div (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) ) (v4)) (vec_scalar_add (v7) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_sub (v7) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_mul (v7) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_scalar_div (v7) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (scalar_vec_sub (v7) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (scalar_vec_div (v7) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v1) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v1) col ) row 1 ) ) 0 ) )) (vec_elemwise_add (v4) (v2)) (vec_elemwise_sub (v4) (v2)) (vec_elemwise_mul (v4) (v2)) (vec_elemwise_div (v4) (v2)) (vec_scalar_add (v5) (v4)) (vec_scalar_sub (v5) (v4)) (vec_scalar_mul (v5) (v4)) (vec_scalar_div (v5) (v4)) (scalar_vec_sub (v5) (v4)) (scalar_vec_div (v5) (v4)) (vec_elemwise_sub (v2) (v4)) (vec_elemwise_div (v2) (v4)) (vec_scalar_add (v7) (v2)) (vec_scalar_sub (v7) (v2)) (vec_scalar_mul (v7) (v2)) (vec_scalar_div (v7) (v2)) (scalar_vec_sub (v7) (v2)) (scalar_vec_div (v7) (v2)) (vec_elemwise_add (v4) (v4)) (vec_elemwise_sub (v4) (v4)) (vec_elemwise_mul (v4) (v4)) (vec_elemwise_div (v4) (v4)) (vec_scalar_add (v7) (v4)) (vec_scalar_sub (v7) (v4)) (vec_scalar_mul (v7) (v4)) (vec_scalar_div (v7) (v4)) (scalar_vec_sub (v7) (v4)) (scalar_vec_div (v7) (v4)))]
[v7 (choose (+ (v5) (v3) ) (- (v5) (v3) ) (* (v5) (v3) ) (quotient-noerr (v5) (v3) ) (- (v3) (v5) ) (quotient-noerr (v3) (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v8 (choose (v9) (v10) (v11) (v12))]
[v9 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v1) row ) (list-list-col-slice-noerr (v1) 0 row ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v1) row ) (list-list-col-slice-noerr (v1) 0 row ) ) ))]
[v10 (choose (matrix_elemwise_add (v9) (v9) ) (matrix_elemwise_sub (v9) (v9) ) (matrix_elemwise_mul (v9) (v9) ) (matrix_elemwise_div (v9) (v9) ) (matrix_scalar_add (v3) (v9) ) (matrix_scalar_sub (v3) (v9) ) (matrix_scalar_mul (v3) (v9) ) (matrix_scalar_div (v3) (v9) ) (scalar_matrix_sub (v3) (v9)) (scalar_matrix_div (v3) (v9)))]
[v11 (choose (matrix_elemwise_add (v10) (v9) ) (matrix_elemwise_sub (v10) (v9) ) (matrix_elemwise_mul (v10) (v9) ) (matrix_elemwise_div (v10) (v9) ) (matrix_scalar_add (v3) (v10) ) (matrix_scalar_sub (v3) (v10) ) (matrix_scalar_mul (v3) (v10) ) (matrix_scalar_div (v3) (v10) ) (scalar_matrix_sub (v3) (v10)) (scalar_matrix_div (v3) (v10)) (matrix_elemwise_sub (v9) (v10) ) (matrix_elemwise_div (v9) (v10) ) (matrix_scalar_add (v5) (v9) ) (matrix_scalar_sub (v5) (v9) ) (matrix_scalar_mul (v5) (v9) ) (matrix_scalar_div (v5) (v9) ) (scalar_matrix_sub (v5) (v9)) (scalar_matrix_div (v5) (v9)) (matrix_elemwise_add (v10) (v10) ) (matrix_elemwise_sub (v10) (v10) ) (matrix_elemwise_mul (v10) (v10) ) (matrix_elemwise_div (v10) (v10) ) (matrix_scalar_add (v5) (v10) ) (matrix_scalar_sub (v5) (v10) ) (matrix_scalar_mul (v5) (v10) ) (matrix_scalar_div (v5) (v10) ) (scalar_matrix_sub (v5) (v10)) (scalar_matrix_div (v5) (v10)))]
[v12 (choose (matrix_elemwise_add (v11) (v9) ) (matrix_elemwise_sub (v11) (v9) ) (matrix_elemwise_mul (v11) (v9) ) (matrix_elemwise_div (v11) (v9) ) (matrix_scalar_add (v3) (v11) ) (matrix_scalar_sub (v3) (v11) ) (matrix_scalar_mul (v3) (v11) ) (matrix_scalar_div (v3) (v11) ) (scalar_matrix_sub (v3) (v11)) (scalar_matrix_div (v3) (v11)) (matrix_elemwise_sub (v9) (v11) ) (matrix_elemwise_div (v9) (v11) ) (matrix_scalar_add (v7) (v9) ) (matrix_scalar_sub (v7) (v9) ) (matrix_scalar_mul (v7) (v9) ) (matrix_scalar_div (v7) (v9) ) (scalar_matrix_sub (v7) (v9)) (scalar_matrix_div (v7) (v9)) (matrix_elemwise_add (v11) (v10) ) (matrix_elemwise_sub (v11) (v10) ) (matrix_elemwise_mul (v11) (v10) ) (matrix_elemwise_div (v11) (v10) ) (matrix_scalar_add (v5) (v11) ) (matrix_scalar_sub (v5) (v11) ) (matrix_scalar_mul (v5) (v11) ) (matrix_scalar_div (v5) (v11) ) (scalar_matrix_sub (v5) (v11)) (scalar_matrix_div (v5) (v11)) (matrix_elemwise_sub (v10) (v11) ) (matrix_elemwise_div (v10) (v11) ) (matrix_scalar_add (v7) (v10) ) (matrix_scalar_sub (v7) (v10) ) (matrix_scalar_mul (v7) (v10) ) (matrix_scalar_div (v7) (v10) ) (scalar_matrix_sub (v7) (v10)) (scalar_matrix_div (v7) (v10)) (matrix_elemwise_add (v11) (v11) ) (matrix_elemwise_sub (v11) (v11) ) (matrix_elemwise_mul (v11) (v11) ) (matrix_elemwise_div (v11) (v11) ) (matrix_scalar_add (v7) (v11) ) (matrix_scalar_sub (v7) (v11) ) (matrix_scalar_mul (v7) (v11) ) (matrix_scalar_div (v7) (v11) ) (scalar_matrix_sub (v7) (v11)) (scalar_matrix_div (v7) (v11)))]
)

(define-grammar (screen_blend_8_ps_gram base active screen_blend_8_rv)
 [rv (choose (equal? screen_blend_8_rv (v0) ))]
[v0 (choose (v1) (v3) (v5) (v7))]
[v1 (choose (v2) (matrix-transpose-noerr (v2) ))]
[v2 (choose base active)]
[v3 (choose (matrix_elemwise_add (v1) (v1) ) (matrix_elemwise_sub (v1) (v1) ) (matrix_elemwise_mul (v1) (v1) ) (matrix_elemwise_div (v1) (v1) ) (matrix_scalar_add (v4) (v1) ) (matrix_scalar_sub (v4) (v1) ) (matrix_scalar_mul (v4) (v1) ) (matrix_scalar_div (v4) (v1) ) (scalar_matrix_sub (v4) (v1)) (scalar_matrix_div (v4) (v1)))]
[v4 (choose 32)]
[v5 (choose (matrix_elemwise_add (v3) (v1) ) (matrix_elemwise_sub (v3) (v1) ) (matrix_elemwise_mul (v3) (v1) ) (matrix_elemwise_div (v3) (v1) ) (matrix_scalar_add (v4) (v3) ) (matrix_scalar_sub (v4) (v3) ) (matrix_scalar_mul (v4) (v3) ) (matrix_scalar_div (v4) (v3) ) (scalar_matrix_sub (v4) (v3)) (scalar_matrix_div (v4) (v3)) (matrix_elemwise_sub (v1) (v3) ) (matrix_elemwise_div (v1) (v3) ) (matrix_scalar_add (v6) (v1) ) (matrix_scalar_sub (v6) (v1) ) (matrix_scalar_mul (v6) (v1) ) (matrix_scalar_div (v6) (v1) ) (scalar_matrix_sub (v6) (v1)) (scalar_matrix_div (v6) (v1)) (matrix_elemwise_add (v3) (v3) ) (matrix_elemwise_sub (v3) (v3) ) (matrix_elemwise_mul (v3) (v3) ) (matrix_elemwise_div (v3) (v3) ) (matrix_scalar_add (v6) (v3) ) (matrix_scalar_sub (v6) (v3) ) (matrix_scalar_mul (v6) (v3) ) (matrix_scalar_div (v6) (v3) ) (scalar_matrix_sub (v6) (v3)) (scalar_matrix_div (v6) (v3)))]
[v6 (choose (+ (v4) (v4) ) (- (v4) (v4) ) (* (v4) (v4) ) (quotient-noerr (v4) (v4) ))]
[v7 (choose (matrix_elemwise_add (v5) (v1) ) (matrix_elemwise_sub (v5) (v1) ) (matrix_elemwise_mul (v5) (v1) ) (matrix_elemwise_div (v5) (v1) ) (matrix_scalar_add (v4) (v5) ) (matrix_scalar_sub (v4) (v5) ) (matrix_scalar_mul (v4) (v5) ) (matrix_scalar_div (v4) (v5) ) (scalar_matrix_sub (v4) (v5)) (scalar_matrix_div (v4) (v5)) (matrix_elemwise_sub (v1) (v5) ) (matrix_elemwise_div (v1) (v5) ) (matrix_scalar_add (v8) (v1) ) (matrix_scalar_sub (v8) (v1) ) (matrix_scalar_mul (v8) (v1) ) (matrix_scalar_div (v8) (v1) ) (scalar_matrix_sub (v8) (v1)) (scalar_matrix_div (v8) (v1)) (matrix_elemwise_add (v5) (v3) ) (matrix_elemwise_sub (v5) (v3) ) (matrix_elemwise_mul (v5) (v3) ) (matrix_elemwise_div (v5) (v3) ) (matrix_scalar_add (v6) (v5) ) (matrix_scalar_sub (v6) (v5) ) (matrix_scalar_mul (v6) (v5) ) (matrix_scalar_div (v6) (v5) ) (scalar_matrix_sub (v6) (v5)) (scalar_matrix_div (v6) (v5)) (matrix_elemwise_sub (v3) (v5) ) (matrix_elemwise_div (v3) (v5) ) (matrix_scalar_add (v8) (v3) ) (matrix_scalar_sub (v8) (v3) ) (matrix_scalar_mul (v8) (v3) ) (matrix_scalar_div (v8) (v3) ) (scalar_matrix_sub (v8) (v3)) (scalar_matrix_div (v8) (v3)) (matrix_elemwise_add (v5) (v5) ) (matrix_elemwise_sub (v5) (v5) ) (matrix_elemwise_mul (v5) (v5) ) (matrix_elemwise_div (v5) (v5) ) (matrix_scalar_add (v8) (v5) ) (matrix_scalar_sub (v8) (v5) ) (matrix_scalar_mul (v8) (v5) ) (matrix_scalar_div (v8) (v5) ) (scalar_matrix_sub (v8) (v5)) (scalar_matrix_div (v8) (v5)))]
[v8 (choose (+ (v6) (v4) ) (- (v6) (v4) ) (* (v6) (v4) ) (quotient-noerr (v6) (v4) ) (- (v4) (v6) ) (quotient-noerr (v4) (v6) ) (+ (v6) (v6) ) (- (v6) (v6) ) (* (v6) (v6) ) (quotient-noerr (v6) (v6) ))]
)

(define-grammar (OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (screen_blend_8_inv0 active agg.result base col pixel row row_vec) (screen_blend_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (screen_blend_8_inv1 active base col pixel row_vec agg.result row) (screen_blend_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (screen_blend_8_ps base active screen_blend_8_rv) (screen_blend_8_ps_gram base active screen_blend_8_rv #:depth 10))

(define (OUTER_LOOP_INDEX_FIRST ) (OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))

(define-symbolic active_BOUNDEDSET-len integer?)
(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define-symbolic active_BOUNDEDSET-2 integer?)
(define-symbolic active_BOUNDEDSET-3 integer?)
(define active (take (list (list active_BOUNDEDSET-0 active_BOUNDEDSET-1) (list active_BOUNDEDSET-2 active_BOUNDEDSET-3)) active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) (list agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3)) agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-len integer?)
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define-symbolic base_BOUNDEDSET-2 integer?)
(define-symbolic base_BOUNDEDSET-3 integer?)
(define base (take (list (list base_BOUNDEDSET-0 base_BOUNDEDSET-1) (list base_BOUNDEDSET-2 base_BOUNDEDSET-3)) base_BOUNDEDSET-len))
(define-symbolic col integer?)
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(define-symbolic screen_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic screen_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic screen_blend_8_rv_BOUNDEDSET-1 integer?)
(define screen_blend_8_rv (take (list screen_blend_8_rv_BOUNDEDSET-0 screen_blend_8_rv_BOUNDEDSET-1) screen_blend_8_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length base ) 1 ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (screen_blend_8_inv0 active (list-list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (list-list-length base ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (screen_blend_8_inv0 active agg.result base col pixel row row_vec) ) (screen_blend_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (< col (length (list-list-ref-noerr base 0 ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (screen_blend_8_inv0 active agg.result base col pixel row row_vec) ) (screen_blend_8_inv1 active base col pixel row_vec agg.result row) ) (screen_blend_8_inv1 active base (+ col 1 ) (- (+ (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (quotient-noerr (* (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) 32 ) ) (list-append row_vec (- (+ (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (quotient-noerr (* (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) 32 ) ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (screen_blend_8_inv0 active agg.result base col pixel row row_vec) ) (screen_blend_8_inv1 active base col pixel row_vec agg.result row) ) (screen_blend_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (screen_blend_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length base ) ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (screen_blend_8_inv0 active agg.result base col pixel row row_vec) ) ) (screen_blend_8_ps base active agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 col pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 screen_blend_8_rv_BOUNDEDSET-len screen_blend_8_rv_BOUNDEDSET-0 screen_blend_8_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
