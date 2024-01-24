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
 [rv (choose (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (equal? agg.result (matrix_elemwise_add (v0) (v0) ) ) ))]
[v0 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v1) row ) (list-list-col-slice-noerr (v1) 0 row ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v1) row ) (list-list-col-slice-noerr (v1) 0 row ) ) ))]
[v1 (choose base active)]
)

(define-grammar (linear_dodge_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= row 0 ) (<= row (list-list-length base ) ) ) (>= col 0 ) ) (<= col (length (list-list-ref-noerr base 0 ) ) ) ) (equal? row_vec (vec_elemwise_add (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v0) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v0) col ) row 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v0) row ) col ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v0) col ) row 1 ) ) 0 ) )) ) ) (equal? agg.result (matrix_elemwise_add (v1) (v1) ) ) ))]
[v0 (choose base active)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v0) row ) (list-list-col-slice-noerr (v0) 0 row ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v0) row ) (list-list-col-slice-noerr (v0) 0 row ) ) ))]
)

(define-grammar (linear_dodge_8_ps_gram base active linear_dodge_8_rv)
 [rv (choose (equal? linear_dodge_8_rv (matrix_elemwise_add (v0) (v0) ) ))]
[v0 (choose (v1) (matrix-transpose-noerr (v1) ))]
[v1 (choose base active)]
)

(define-grammar (OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
)

(define (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) (linear_dodge_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (linear_dodge_8_inv1 active base col pixel row_vec agg.result row) (linear_dodge_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (linear_dodge_8_ps base active linear_dodge_8_rv) (linear_dodge_8_ps_gram base active linear_dodge_8_rv #:depth 10))

(define (OUTER_LOOP_INDEX_FIRST ) (OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))

(define-symbolic active_BOUNDEDSET-len integer?)
(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define-symbolic active_BOUNDEDSET-2 integer?)
(define-symbolic active_BOUNDEDSET-3 integer?)
(define-symbolic active_BOUNDEDSET-4 integer?)
(define-symbolic active_BOUNDEDSET-5 integer?)
(define-symbolic active_BOUNDEDSET-6 integer?)
(define-symbolic active_BOUNDEDSET-7 integer?)
(define-symbolic active_BOUNDEDSET-8 integer?)
(define-symbolic active_BOUNDEDSET-9 integer?)
(define-symbolic active_BOUNDEDSET-10 integer?)
(define-symbolic active_BOUNDEDSET-11 integer?)
(define-symbolic active_BOUNDEDSET-12 integer?)
(define-symbolic active_BOUNDEDSET-13 integer?)
(define-symbolic active_BOUNDEDSET-14 integer?)
(define-symbolic active_BOUNDEDSET-15 integer?)
(define-symbolic active_BOUNDEDSET-16 integer?)
(define-symbolic active_BOUNDEDSET-17 integer?)
(define-symbolic active_BOUNDEDSET-18 integer?)
(define-symbolic active_BOUNDEDSET-19 integer?)
(define-symbolic active_BOUNDEDSET-20 integer?)
(define-symbolic active_BOUNDEDSET-21 integer?)
(define-symbolic active_BOUNDEDSET-22 integer?)
(define-symbolic active_BOUNDEDSET-23 integer?)
(define-symbolic active_BOUNDEDSET-24 integer?)
(define active (take (list (list active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4) (list active_BOUNDEDSET-5 active_BOUNDEDSET-6 active_BOUNDEDSET-7 active_BOUNDEDSET-8 active_BOUNDEDSET-9) (list active_BOUNDEDSET-10 active_BOUNDEDSET-11 active_BOUNDEDSET-12 active_BOUNDEDSET-13 active_BOUNDEDSET-14) (list active_BOUNDEDSET-15 active_BOUNDEDSET-16 active_BOUNDEDSET-17 active_BOUNDEDSET-18 active_BOUNDEDSET-19) (list active_BOUNDEDSET-20 active_BOUNDEDSET-21 active_BOUNDEDSET-22 active_BOUNDEDSET-23 active_BOUNDEDSET-24)) active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define-symbolic agg.result_BOUNDEDSET-4 integer?)
(define-symbolic agg.result_BOUNDEDSET-5 integer?)
(define-symbolic agg.result_BOUNDEDSET-6 integer?)
(define-symbolic agg.result_BOUNDEDSET-7 integer?)
(define-symbolic agg.result_BOUNDEDSET-8 integer?)
(define-symbolic agg.result_BOUNDEDSET-9 integer?)
(define-symbolic agg.result_BOUNDEDSET-10 integer?)
(define-symbolic agg.result_BOUNDEDSET-11 integer?)
(define-symbolic agg.result_BOUNDEDSET-12 integer?)
(define-symbolic agg.result_BOUNDEDSET-13 integer?)
(define-symbolic agg.result_BOUNDEDSET-14 integer?)
(define-symbolic agg.result_BOUNDEDSET-15 integer?)
(define-symbolic agg.result_BOUNDEDSET-16 integer?)
(define-symbolic agg.result_BOUNDEDSET-17 integer?)
(define-symbolic agg.result_BOUNDEDSET-18 integer?)
(define-symbolic agg.result_BOUNDEDSET-19 integer?)
(define-symbolic agg.result_BOUNDEDSET-20 integer?)
(define-symbolic agg.result_BOUNDEDSET-21 integer?)
(define-symbolic agg.result_BOUNDEDSET-22 integer?)
(define-symbolic agg.result_BOUNDEDSET-23 integer?)
(define-symbolic agg.result_BOUNDEDSET-24 integer?)
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4) (list agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 agg.result_BOUNDEDSET-9) (list agg.result_BOUNDEDSET-10 agg.result_BOUNDEDSET-11 agg.result_BOUNDEDSET-12 agg.result_BOUNDEDSET-13 agg.result_BOUNDEDSET-14) (list agg.result_BOUNDEDSET-15 agg.result_BOUNDEDSET-16 agg.result_BOUNDEDSET-17 agg.result_BOUNDEDSET-18 agg.result_BOUNDEDSET-19) (list agg.result_BOUNDEDSET-20 agg.result_BOUNDEDSET-21 agg.result_BOUNDEDSET-22 agg.result_BOUNDEDSET-23 agg.result_BOUNDEDSET-24)) agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-len integer?)
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define-symbolic base_BOUNDEDSET-2 integer?)
(define-symbolic base_BOUNDEDSET-3 integer?)
(define-symbolic base_BOUNDEDSET-4 integer?)
(define-symbolic base_BOUNDEDSET-5 integer?)
(define-symbolic base_BOUNDEDSET-6 integer?)
(define-symbolic base_BOUNDEDSET-7 integer?)
(define-symbolic base_BOUNDEDSET-8 integer?)
(define-symbolic base_BOUNDEDSET-9 integer?)
(define-symbolic base_BOUNDEDSET-10 integer?)
(define-symbolic base_BOUNDEDSET-11 integer?)
(define-symbolic base_BOUNDEDSET-12 integer?)
(define-symbolic base_BOUNDEDSET-13 integer?)
(define-symbolic base_BOUNDEDSET-14 integer?)
(define-symbolic base_BOUNDEDSET-15 integer?)
(define-symbolic base_BOUNDEDSET-16 integer?)
(define-symbolic base_BOUNDEDSET-17 integer?)
(define-symbolic base_BOUNDEDSET-18 integer?)
(define-symbolic base_BOUNDEDSET-19 integer?)
(define-symbolic base_BOUNDEDSET-20 integer?)
(define-symbolic base_BOUNDEDSET-21 integer?)
(define-symbolic base_BOUNDEDSET-22 integer?)
(define-symbolic base_BOUNDEDSET-23 integer?)
(define-symbolic base_BOUNDEDSET-24 integer?)
(define base (take (list (list base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4) (list base_BOUNDEDSET-5 base_BOUNDEDSET-6 base_BOUNDEDSET-7 base_BOUNDEDSET-8 base_BOUNDEDSET-9) (list base_BOUNDEDSET-10 base_BOUNDEDSET-11 base_BOUNDEDSET-12 base_BOUNDEDSET-13 base_BOUNDEDSET-14) (list base_BOUNDEDSET-15 base_BOUNDEDSET-16 base_BOUNDEDSET-17 base_BOUNDEDSET-18 base_BOUNDEDSET-19) (list base_BOUNDEDSET-20 base_BOUNDEDSET-21 base_BOUNDEDSET-22 base_BOUNDEDSET-23 base_BOUNDEDSET-24)) base_BOUNDEDSET-len))
(define-symbolic col integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-len integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-1 integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-2 integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-3 integer?)
(define-symbolic linear_dodge_8_rv_BOUNDEDSET-4 integer?)
(define linear_dodge_8_rv (take (list linear_dodge_8_rv_BOUNDEDSET-0 linear_dodge_8_rv_BOUNDEDSET-1 linear_dodge_8_rv_BOUNDEDSET-2 linear_dodge_8_rv_BOUNDEDSET-3 linear_dodge_8_rv_BOUNDEDSET-4) linear_dodge_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define-symbolic row_vec_BOUNDEDSET-2 integer?)
(define-symbolic row_vec_BOUNDEDSET-3 integer?)
(define-symbolic row_vec_BOUNDEDSET-4 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2 row_vec_BOUNDEDSET-3 row_vec_BOUNDEDSET-4) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length base ) 1 ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active (list-list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (list-list-length base ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (linear_dodge_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (< col (length (list-list-ref-noerr base 0 ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (linear_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (linear_dodge_8_inv1 active base (+ col 1 ) (+ (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (list-append row_vec (+ (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (linear_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (linear_dodge_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length base ) ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (linear_dodge_8_inv0 active agg.result base col pixel row row_vec) ) ) (linear_dodge_8_ps base active agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4 active_BOUNDEDSET-5 active_BOUNDEDSET-6 active_BOUNDEDSET-7 active_BOUNDEDSET-8 active_BOUNDEDSET-9 active_BOUNDEDSET-10 active_BOUNDEDSET-11 active_BOUNDEDSET-12 active_BOUNDEDSET-13 active_BOUNDEDSET-14 active_BOUNDEDSET-15 active_BOUNDEDSET-16 active_BOUNDEDSET-17 active_BOUNDEDSET-18 active_BOUNDEDSET-19 active_BOUNDEDSET-20 active_BOUNDEDSET-21 active_BOUNDEDSET-22 active_BOUNDEDSET-23 active_BOUNDEDSET-24 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 agg.result_BOUNDEDSET-9 agg.result_BOUNDEDSET-10 agg.result_BOUNDEDSET-11 agg.result_BOUNDEDSET-12 agg.result_BOUNDEDSET-13 agg.result_BOUNDEDSET-14 agg.result_BOUNDEDSET-15 agg.result_BOUNDEDSET-16 agg.result_BOUNDEDSET-17 agg.result_BOUNDEDSET-18 agg.result_BOUNDEDSET-19 agg.result_BOUNDEDSET-20 agg.result_BOUNDEDSET-21 agg.result_BOUNDEDSET-22 agg.result_BOUNDEDSET-23 agg.result_BOUNDEDSET-24 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4 base_BOUNDEDSET-5 base_BOUNDEDSET-6 base_BOUNDEDSET-7 base_BOUNDEDSET-8 base_BOUNDEDSET-9 base_BOUNDEDSET-10 base_BOUNDEDSET-11 base_BOUNDEDSET-12 base_BOUNDEDSET-13 base_BOUNDEDSET-14 base_BOUNDEDSET-15 base_BOUNDEDSET-16 base_BOUNDEDSET-17 base_BOUNDEDSET-18 base_BOUNDEDSET-19 base_BOUNDEDSET-20 base_BOUNDEDSET-21 base_BOUNDEDSET-22 base_BOUNDEDSET-23 base_BOUNDEDSET-24 col linear_dodge_8_rv_BOUNDEDSET-len linear_dodge_8_rv_BOUNDEDSET-0 linear_dodge_8_rv_BOUNDEDSET-1 linear_dodge_8_rv_BOUNDEDSET-2 linear_dodge_8_rv_BOUNDEDSET-3 linear_dodge_8_rv_BOUNDEDSET-4 pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2 row_vec_BOUNDEDSET-3 row_vec_BOUNDEDSET-4)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
