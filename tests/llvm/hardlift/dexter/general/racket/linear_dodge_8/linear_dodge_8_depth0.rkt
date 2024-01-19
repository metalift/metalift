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

(define-grammar (linear_dodge_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (v1))]
[v1 (choose (list-list-col-slice-noerr (list-list-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) ))]
[v2 (choose base active)]
[v3 (choose 0 (list-list-length base ) row 0 1)]
)

(define-grammar (linear_dodge_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (>= col 0 ) ) (<= col (length (list-list-ref-noerr base 0 ) ) ) ) (equal? row_vec (v0) ) ) (equal? agg.result (v4) ) ))]
[v0 (choose (list-list-ref-noerr (v1) (v3) ))]
[v1 (choose (list-list-col-slice-noerr (list-list-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) ))]
[v2 (choose base active)]
[v3 (choose 0 (list-list-length base ) (length (list-list-ref-noerr base 0 ) ) row col 0 1)]
[v4 (choose (v1))]
)

(define-grammar (linear_dodge_8_ps_gram base active linear_dodge_8_rv)
 [rv (choose (equal? linear_dodge_8_rv (v0) ))]
[v0 (choose (v1))]
[v1 (choose (list-list-col-slice-noerr (list-list-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) (matrix-transpose-noerr (list-list-col-slice-noerr (list-list-slice-noerr (v2) (v3) (v3) ) (v3) (v3) ) ))]
[v2 (choose base active)]
[v3 (choose 0 (list-list-length base ) (length (list-list-ref-noerr base 0 ) ) 0 1)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) (linear_dodge_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (linear_dodge_8_inv1 active base col pixel row_vec agg.result row) (linear_dodge_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (linear_dodge_8_ps base active linear_dodge_8_rv) (linear_dodge_8_ps_gram base active linear_dodge_8_rv #:depth 10))

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
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-len integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-1 integer?)
(define linear_dodge_8_rv (take (list linear_dodge_8_rv_BOUNDEDSET-0 linear_dodge_8_rv_BOUNDEDSET-1) linear_dodge_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length base ) 1 ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active (list-list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (list-list-length base ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (linear_dodge_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (< col (length (list-list-ref-noerr base 0 ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (linear_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (linear_dodge_8_inv1 active base (+ col 1 ) (+ (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (list-append row_vec (+ (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (linear_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (linear_dodge_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length base ) ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) ) (linear_dodge_8_ps base active agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 col linear_dodge_8_rv_BOUNDEDSET-len linear_dodge_8_rv_BOUNDEDSET-0 linear_dodge_8_rv_BOUNDEDSET-1 pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
