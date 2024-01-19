#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (list-list-length matrix_x ) 1 ) (< (length (list-list-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (list-list-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (list-list-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (list-list-tail-noerr matrix_x 1 ) x ) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (selection_two_args x y select_two_args_arg)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (select_two_args_arg (list-ref-noerr x 0 ) (list-ref-noerr y 0 )) (selection_two_args (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) select_two_args_arg) ) ))


 (define-bounded (matrix_selection_two_args matrix_x matrix_y select_two_args_arg)
(if (or (< (list-list-length matrix_x ) 1 ) (! (equal? (list-list-length matrix_x ) (list-list-length matrix_y ) ) ) ) (list-list-empty ) (list-list-prepend (selection_two_args (list-list-ref-noerr matrix_x 0 ) (list-list-ref-noerr matrix_y 0 ) select_two_args_arg) (matrix_selection_two_args (list-list-tail-noerr matrix_x 1 ) (list-list-tail-noerr matrix_y 1 ) select_two_args_arg ) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int) ) ))


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

(define-grammar (lighten_blend_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (equal? agg.result (matrix_selection_two_args (v0) (v0) select_two_args ) ) ))]
[v0 (choose (list-list-col-slice-noerr (list-list-slice-noerr (v1) (v2) (v2) ) (v2) (v2) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr (v1) (v2) (v2) ) (v2) (v2) ) ))]
[v1 (choose base active)]
[v2 (choose 0 (list-list-length base ) row)]
)

(define-grammar (lighten_blend_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (>= col 0 ) ) (<= col (length (list-list-ref-noerr base 0 ) ) ) ) (equal? row_vec (selection_two_args (list-list-ref-noerr (v0) (v2) ) (list-list-ref-noerr (v0) (v2) ) select_two_args) ) ) (equal? agg.result (matrix_selection_two_args (v0) (v0) select_two_args ) ) ))]
[v0 (choose (list-list-col-slice-noerr (list-list-slice-noerr (v1) (v2) (v2) ) (v2) (v2) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr (v1) (v2) (v2) ) (v2) (v2) ) ))]
[v1 (choose base active)]
[v2 (choose 0 (list-list-length base ) (length (list-list-ref-noerr base 0 ) ) row col)]
)

(define-grammar (lighten_blend_8_ps_gram base active lighten_blend_8_rv)
 [rv (choose (equal? lighten_blend_8_rv (matrix_selection_two_args (list-list-col-slice-noerr (list-list-slice-noerr (v0) (v2) (v2) ) (v2) (v2) ) (list-list-col-slice-noerr (list-list-slice-noerr (v0) (v2) (v2) ) (v2) (v2) ) select_two_args ) ))]
[v0 (choose (v1) (matrix-transpose-noerr (v1) ))]
[v1 (choose base active)]
[v2 (choose 0 (list-list-length base ) (length (list-list-ref-noerr base 0 ) ))]
)

(define-grammar (select_two_args_gram int_x int_y)
 [rv (choose (if (v0) (v1) (v1) ))]
[v0 (choose (< (v1) (v1) ) (<= (v1) (v1) ) (equal? (v1) (v1) ) (>= (v1) (v1) ) (> (v1) (v1) ))]
[v1 (choose (v2))]
[v2 (choose int_x int_y 0 1)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) (lighten_blend_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (lighten_blend_8_inv1 active base col pixel row_vec agg.result row) (lighten_blend_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (lighten_blend_8_ps base active lighten_blend_8_rv) (lighten_blend_8_ps_gram base active lighten_blend_8_rv #:depth 10))

(define (select_two_args int_x int_y) (select_two_args_gram int_x int_y #:depth 10))
(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

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
(define-symbolic int_x integer?)
(define-symbolic int_y integer?)
(define-symbolic lighten_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic lighten_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic lighten_blend_8_rv_BOUNDEDSET-1 integer?)
(define lighten_blend_8_rv (take (list lighten_blend_8_rv_BOUNDEDSET-0 lighten_blend_8_rv_BOUNDEDSET-1) lighten_blend_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length base ) 1 ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active (list-list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (list-list-length base ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (lighten_blend_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (< (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (lighten_blend_8_inv1 active base col pixel row_vec agg.result row) ) (&& (&& (&& (&& (&& (&& (&& (! (< (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (lighten_blend_8_inv1 active base col pixel row_vec agg.result row) ) ) (lighten_blend_8_inv1 active base (+ col 1 ) (if (&& (&& (&& (&& (&& (&& (&& (! (< (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (lighten_blend_8_inv1 active base col pixel row_vec agg.result row) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (list-append row_vec (if (&& (&& (&& (&& (&& (&& (&& (! (< (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (lighten_blend_8_inv1 active base col pixel row_vec agg.result row) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (lighten_blend_8_inv1 active base col pixel row_vec agg.result row) ) (lighten_blend_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length base ) ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (lighten_blend_8_inv0 active agg.result base col pixel row row_vec) ) ) (lighten_blend_8_ps base active agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 col int_x int_y lighten_blend_8_rv_BOUNDEDSET-len lighten_blend_8_rv_BOUNDEDSET-0 lighten_blend_8_rv_BOUNDEDSET-1 pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
