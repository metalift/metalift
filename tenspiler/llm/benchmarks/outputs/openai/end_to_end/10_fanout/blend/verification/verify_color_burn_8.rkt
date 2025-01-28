#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (matrix_col_slice matrix start end)
(if (< (matrix-length matrix ) 1 ) (matrix-empty ) (matrix-prepend (vec_slice (matrix-ref-noerr matrix 0 ) start end) (matrix-col-slice-noerr (matrix-tail-noerr matrix 1 ) start end ) ) ))


 (define-bounded (matrix_elemwise_add matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_add (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 )) (matrix_elemwise_add (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_div matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_div (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 )) (matrix_elemwise_div (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_mul matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 )) (matrix_elemwise_mul (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define-bounded (matrix_elemwise_sub matrix_x matrix_y)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vec_elemwise_sub (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 )) (matrix_elemwise_sub (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) ) ) ))


 (define (matrix_row_slice matrix start end)
(matrix-tail-noerr (matrix-take-noerr matrix end ) start ))


 (define-bounded (matrix_scalar_add a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_add a (matrix-ref-noerr matrix_x 0 )) (matrix_scalar_add a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_div a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_div a (matrix-ref-noerr matrix_x 0 )) (matrix_scalar_div a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_mul a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_mul a (matrix-ref-noerr matrix_x 0 )) (matrix_scalar_mul a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_scalar_sub a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (vec_scalar_sub a (matrix-ref-noerr matrix_x 0 )) (matrix_scalar_sub a (matrix-tail-noerr matrix_x 1 ) ) ) ))


 (define-bounded (matrix_transpose matrix)
(if (< (matrix-length matrix ) 1 ) (matrix-empty ) (matrix-prepend (firsts matrix) (matrix-transpose-noerr (rests matrix) ) ) ))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (matrix-length matrix_x ) 1 ) (< (length (matrix-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (matrix-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (matrix-tail-noerr matrix_x 1 ) x ) ) ))


 (define-bounded (matrix_where matrix_x matrix_y select_two_args_arg)
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (vector_where (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 ) select_two_args_arg) (matrix_where (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) select_two_args_arg ) ) ))


 (define-bounded (reduce_max x)
(if (<= (length x ) 1 ) (list-ref-noerr x 0 ) (if (> (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_mul x)
(if (< (length x ) 1 ) 1 (* (list-ref-noerr x 0 ) (reduce_mul (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (rests matrix)
(if (< (matrix-length matrix ) 1 ) (matrix-empty ) (matrix-col-slice-noerr matrix 1 (length (matrix-ref-noerr matrix 0 ) ) ) ))


 (define-bounded (scalar_matrix_div a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (scalar_vec_div a (matrix-ref-noerr matrix_x 0 )) (scalar_matrix_div a (matrix-tail-noerr matrix_x 1 )) ) ))


 (define-bounded (scalar_matrix_sub a matrix_x)
(if (< (matrix-length matrix_x ) 1 ) (matrix-empty ) (matrix-prepend (scalar_vec_sub a (matrix-ref-noerr matrix_x 0 )) (scalar_matrix_sub a (matrix-tail-noerr matrix_x 1 )) ) ))


 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- a (list-ref-noerr x 0 ) ) (scalar_vec_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int) ) ))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_scalar_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) a ) (vec_scalar_sub a (list-tail-noerr x 1 )) ) ))


 (define (vec_slice lst start end)
(list-tail-noerr (list-take-noerr lst end ) start ))


 (define-bounded (vector_where x y select_two_args_arg)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (select_two_args_arg (list-ref-noerr x 0 ) (list-ref-noerr y 0 )) (vector_where (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) select_two_args_arg) ) ))


 (define-bounded (condition_0a666e54 a b)
(if (equal? a 0 ) 32 b ))


 (define-bounded (color_burn_8_ps active base out)
(equal? out (matrix_where active (scalar_matrix_sub 32 (matrix_elemwise_div (scalar_matrix_sub 32 base) active )) condition_0a666e54 ) ))


 (define-bounded (condition_946256cd a b)
(if (equal? a 0 ) 32 b ))


 (define-bounded (color_burn_8_inv0 active base out row)
(&& (>= row 0 ) (&& (<= row (matrix-length base ) ) (equal? out (matrix_where (matrix-take-noerr active row ) (scalar_matrix_sub 32 (matrix_elemwise_div (scalar_matrix_sub 32 (matrix-take-noerr base row )) (matrix-take-noerr active row ) )) condition_946256cd ) ) ) ))


 (define-bounded (condition_ff3420c2 a b)
(if (equal? a 0 ) 32 b ))


 (define-bounded (condition_2cfc7e1c a b)
(if (equal? a 0 ) 32 b ))


 (define-bounded (color_burn_8_inv1 active base col out row row_vec)
(&& (>= col 0 ) (&& (<= col (length (matrix-ref-noerr base 0 ) ) ) (&& (>= row 0 ) (&& (< row (matrix-length base ) ) (&& (equal? row_vec (vector_where (list-take-noerr (matrix-ref-noerr active row ) col ) (scalar_vec_sub 32 (vec_elemwise_div (scalar_vec_sub 32 (list-take-noerr (matrix-ref-noerr base row ) col )) (list-take-noerr (matrix-ref-noerr active row ) col ))) condition_ff3420c2) ) (equal? out (matrix_where (matrix-take-noerr active row ) (scalar_matrix_sub 32 (matrix_elemwise_div (scalar_matrix_sub 32 (matrix-take-noerr base row )) (matrix-take-noerr active row ) )) condition_2cfc7e1c ) ) ) ) ) ) ))

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
(define-symbolic color_burn_8_rv_BOUNDEDSET-len integer?)
(define-symbolic color_burn_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic color_burn_8_rv_BOUNDEDSET-1 integer?)
(define-symbolic color_burn_8_rv_BOUNDEDSET-2 integer?)
(define-symbolic color_burn_8_rv_BOUNDEDSET-3 integer?)
(define color_burn_8_rv (take (list (list color_burn_8_rv_BOUNDEDSET-0 color_burn_8_rv_BOUNDEDSET-1) (list color_burn_8_rv_BOUNDEDSET-2 color_burn_8_rv_BOUNDEDSET-3)) color_burn_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define vc (verify (assert (&& (&& (&& (&& (=> (&& (&& (> (matrix-length base ) 1 ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base (matrix-empty ) 0) ) (=> (&& (&& (&& (&& (< row (matrix-length base ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) (color_burn_8_inv1 active base 0 agg.result row (list-empty )) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (equal? (list-ref-noerr (matrix-ref-noerr active row ) col ) 0 ) (< col (length (matrix-ref-noerr base 0 ) ) ) ) (< row (matrix-length base ) ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) (color_burn_8_inv1 active base col agg.result row row_vec) ) (&& (&& (&& (&& (&& (&& (&& (! (equal? (list-ref-noerr (matrix-ref-noerr active row ) col ) 0 ) ) (< col (length (matrix-ref-noerr base 0 ) ) ) ) (< row (matrix-length base ) ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) (color_burn_8_inv1 active base col agg.result row row_vec) ) ) (color_burn_8_inv1 active base (+ col 1 ) agg.result row (list-append row_vec (if (&& (&& (&& (&& (&& (&& (&& (! (equal? (list-ref-noerr (matrix-ref-noerr active row ) col ) 0 ) ) (< col (length (matrix-ref-noerr base 0 ) ) ) ) (< row (matrix-length base ) ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) (color_burn_8_inv1 active base col agg.result row row_vec) ) (- 32 (quotient-noerr (- 32 (list-ref-noerr (matrix-ref-noerr base row ) col ) ) (list-ref-noerr (matrix-ref-noerr active row ) col ) ) ) 32 ) )) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (matrix-ref-noerr base 0 ) ) ) ) (< row (matrix-length base ) ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) (color_burn_8_inv1 active base col agg.result row row_vec) ) (color_burn_8_inv0 active base (matrix-append agg.result row_vec ) (+ row 1 )) ) ) (=> (or (&& (&& (&& (&& (! (< row (matrix-length base ) ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) (&& (&& (&& (&& (&& (! true ) (! (< row (matrix-length base ) ) ) ) (> (matrix-length base ) 1 ) ) (equal? (matrix-length base ) (matrix-length active ) ) ) (equal? (length (matrix-ref-noerr base 0 ) ) (length (matrix-ref-noerr active 0 ) ) ) ) (color_burn_8_inv0 active base agg.result row) ) ) (color_burn_8_ps active base agg.result) ) ))))

vc
