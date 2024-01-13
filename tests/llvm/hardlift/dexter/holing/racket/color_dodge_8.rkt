#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (selection_two_args x y select_two_args_arg) 
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (select_two_args_arg (list-ref-noerr x 0 ) (list-ref-noerr y 0 )) (selection_two_args (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) select_two_args_arg) ) )) 


 (define-bounded (matrix_selection_two_args matrix_x matrix_y select_two_args_arg) 
(if (or (< (list-list-length matrix_x ) 1 ) (! (equal? (list-list-length matrix_x ) (list-list-length matrix_y ) ) ) ) (list-list-empty ) (list-list-prepend (selection_two_args (list-list-ref-noerr matrix_x 0 ) (list-list-ref-noerr matrix_y 0 ) select_two_args_arg) (matrix_selection_two_args (list-list-tail-noerr matrix_x 1 ) (list-list-tail-noerr matrix_y 1 ) select_two_args_arg ) ) )) 

(define-grammar (color_dodge_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (>= (OUTER_LOOP_INDEX row col) 0 ) (<= (OUTER_LOOP_INDEX row col) (if (OUTER_LOOP_INDEX_FIRST) (list-list-length base ) (length (list-list-ref-noerr base 0 ) ) ) ) ) (equal? agg.result (matrix_selection_two_args (v0) (v0) select_two_args ) ) ))]
[v0 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v1) (OUTER_LOOP_INDEX row col) ) (list-list-col-slice-noerr (v1) 0 (OUTER_LOOP_INDEX row col) ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v1) (OUTER_LOOP_INDEX row col) ) (list-list-col-slice-noerr (v1) 0 (OUTER_LOOP_INDEX row col) ) ) ))]
[v1 (choose base active)]
) 

(define-grammar (color_dodge_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= (OUTER_LOOP_INDEX row col) 0 ) (< (OUTER_LOOP_INDEX row col) (if (OUTER_LOOP_INDEX_FIRST) (list-list-length base ) (length (list-list-ref-noerr base 0 ) ) ) ) ) (>= (INNER_LOOP_INDEX row col) 0 ) ) (<= (INNER_LOOP_INDEX row col) (if (OUTER_LOOP_INDEX_FIRST) (length (list-list-ref-noerr base 0 ) ) (list-list-length base ) ) ) ) (equal? row_vec (selection_two_args (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v0) (OUTER_LOOP_INDEX row col) ) (INNER_LOOP_INDEX row col) ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v0) (INNER_LOOP_INDEX row col) ) (OUTER_LOOP_INDEX row col) 1 ) ) 0 ) ) (if (OUTER_LOOP_INDEX_FIRST) (list-take-noerr (list-list-ref-noerr (v0) (OUTER_LOOP_INDEX row col) ) (INNER_LOOP_INDEX row col) ) (list-list-ref-noerr (matrix-transpose-noerr (list-list-col-slice-with-length-noerr (list-list-take-noerr (v0) (INNER_LOOP_INDEX row col) ) (OUTER_LOOP_INDEX row col) 1 ) ) 0 ) ) select_two_args) ) ) (equal? agg.result (matrix_selection_two_args (v1) (v1) select_two_args ) ) ))]
[v0 (choose base active)]
[v1 (choose (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v0) (OUTER_LOOP_INDEX row col) ) (list-list-col-slice-noerr (v0) 0 (OUTER_LOOP_INDEX row col) ) ) (matrix-transpose-noerr (if (OUTER_LOOP_INDEX_FIRST) (list-list-take-noerr (v0) (OUTER_LOOP_INDEX row col) ) (list-list-col-slice-noerr (v0) 0 (OUTER_LOOP_INDEX row col) ) ) ))]
) 

(define-grammar (color_dodge_8_ps_gram base active color_dodge_8_rv)
 [rv (choose (equal? color_dodge_8_rv (matrix_selection_two_args (v0) (v0) select_two_args ) ))]
[v0 (choose (v1) (matrix-transpose-noerr (v1) ))]
[v1 (choose base active)]
) 

(define-grammar (select_two_args_gram int_x int_y)
 [rv (choose (if (equal? (v0) (v1) ) (v1) (quotient-noerr (v0) (- (v1) (v0) ) ) ))]
[v0 (choose int_x int_y)]
[v1 (choose 32)]
) 

(define-grammar (OUTER_LOOP_INDEX_gram row col)
 [rv (choose (v0))]
[v0 (choose row col)]
) 

(define-grammar (INNER_LOOP_INDEX_gram row col)
 [rv (choose (v0))]
[v0 (choose row col)]
) 

(define-grammar (OUTER_LOOP_INDEX_FIRST_gram )
 [rv (choose (v0))]
[v0 (choose true false)]
) 

(define (color_dodge_8_inv0 active agg.result base col pixel row row_vec) (color_dodge_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (color_dodge_8_inv1 active base col pixel row_vec agg.result row) (color_dodge_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (color_dodge_8_ps base active color_dodge_8_rv) (color_dodge_8_ps_gram base active color_dodge_8_rv #:depth 10))

(define (OUTER_LOOP_INDEX row col) (OUTER_LOOP_INDEX_gram row col #:depth 10))
(define (INNER_LOOP_INDEX row col) (INNER_LOOP_INDEX_gram row col #:depth 10))
(define (OUTER_LOOP_INDEX_FIRST ) (OUTER_LOOP_INDEX_FIRST_gram  #:depth 10))
(define (select_two_args int_x int_y) (select_two_args_gram int_x int_y #:depth 10))

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
(define-symbolic color_dodge_8_rv_BOUNDEDSET-len integer?)
(define-symbolic color_dodge_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic color_dodge_8_rv_BOUNDEDSET-1 integer?)
(define color_dodge_8_rv (take (list color_dodge_8_rv_BOUNDEDSET-0 color_dodge_8_rv_BOUNDEDSET-1) color_dodge_8_rv_BOUNDEDSET-len))
(define-symbolic int_x integer?)
(define-symbolic int_y integer?)
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length base ) 1 ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active (list-list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (list-list-length base ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (color_dodge_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (equal? (list-ref-noerr (list-list-ref-noerr active row ) col ) 32 ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (color_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (&& (&& (&& (&& (&& (&& (&& (! (equal? (list-ref-noerr (list-list-ref-noerr active row ) col ) 32 ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (color_dodge_8_inv1 active base col pixel row_vec agg.result row) ) ) (color_dodge_8_inv1 active base (+ col 1 ) (if (&& (&& (&& (&& (&& (&& (&& (! (equal? (list-ref-noerr (list-list-ref-noerr active row ) col ) 32 ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (color_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (quotient-noerr (list-ref-noerr (list-list-ref-noerr base row ) col ) (- 32 (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) 32 ) (list-append row_vec (if (&& (&& (&& (&& (&& (&& (&& (! (equal? (list-ref-noerr (list-list-ref-noerr active row ) col ) 32 ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (color_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (quotient-noerr (list-ref-noerr (list-list-ref-noerr base row ) col ) (- 32 (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) 32 ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (color_dodge_8_inv1 active base col pixel row_vec agg.result row) ) (color_dodge_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length base ) ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (color_dodge_8_inv0 active agg.result base col pixel row row_vec) ) ) (color_dodge_8_ps base active agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 col color_dodge_8_rv_BOUNDEDSET-len color_dodge_8_rv_BOUNDEDSET-0 color_dodge_8_rv_BOUNDEDSET-1 int_x int_y pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
    