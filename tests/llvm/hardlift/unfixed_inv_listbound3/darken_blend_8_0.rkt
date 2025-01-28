#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/z3)
(current-solver (z3 #:options (hash ':random-seed 0)))



 (define-bounded (selection_two_args x y select_two_args_arg) 
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (select_two_args_arg (list-ref-noerr x 0 ) (list-ref-noerr y 0 )) (selection_two_args (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) select_two_args_arg) ) )) 


 (define-bounded (nested_selection_two_args nested_x nested_y select_two_args_arg) 
(if (or (< (length nested_x ) 1 ) (! (equal? (length nested_x ) (length nested_y ) ) ) ) (list-empty ) (list-prepend (selection_two_args (list-list-ref-noerr nested_x 0 ) (list-list-ref-noerr nested_y 0 ) select_two_args_arg) (nested_selection_two_args (list-tail-noerr nested_x 1 ) (list-tail-noerr nested_y 1 ) select_two_args_arg) ) )) 

(define-grammar (darken_blend_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (v0) (v2) ) (equal? agg.result (nested_selection_two_args (v4) (v4) select_two_args) ) ))]
[v0 (choose (>= row (v1) ) (> row (v1) ) (equal? row (v1) ) (< row (v1) ) (<= row (v1) ))]
[v1 (choose 0 1)]
[v2 (choose (>= row (v3) ) (> row (v3) ) (equal? row (v3) ) (< row (v3) ) (<= row (v3) ))]
[v3 (choose (length base ) (length (list-list-ref-noerr base 0 ) ))]
[v4 (choose base (list-take-noerr base row ) (list-take-noerr base col ) active (list-take-noerr active row ) (list-take-noerr active col ))]
) 

(define-grammar (darken_blend_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (v0) (v2) ) (v4) ) (v5) ) (equal? row_vec (selection_two_args (v6) (v6) select_two_args) ) ) (equal? agg.result (nested_selection_two_args (v7) (v7) select_two_args) ) ))]
[v0 (choose (>= row (v1) ) (> row (v1) ) (equal? row (v1) ) (< row (v1) ) (<= row (v1) ))]
[v1 (choose 0 1)]
[v2 (choose (>= row (v3) ) (> row (v3) ) (equal? row (v3) ) (< row (v3) ) (<= row (v3) ))]
[v3 (choose (length base ) (length (list-list-ref-noerr base 0 ) ))]
[v4 (choose (>= col (v1) ) (> col (v1) ) (equal? col (v1) ) (< col (v1) ) (<= col (v1) ))]
[v5 (choose (>= col (v3) ) (> col (v3) ) (equal? col (v3) ) (< col (v3) ) (<= col (v3) ))]
[v6 (choose (list-take-noerr (list-list-ref-noerr base 0 ) col ) (list-take-noerr (list-list-ref-noerr base row ) col ) (list-take-noerr (list-list-ref-noerr base col ) row ) (list-take-noerr (list-list-ref-noerr base 0 ) row ) (list-take-noerr (list-list-ref-noerr active 0 ) col ) (list-take-noerr (list-list-ref-noerr active row ) col ) (list-take-noerr (list-list-ref-noerr active col ) row ) (list-take-noerr (list-list-ref-noerr active 0 ) row ) row_vec)]
[v7 (choose base (list-take-noerr base row ) (list-take-noerr base col ) active (list-take-noerr active row ) (list-take-noerr active col ))]
) 

(define-grammar (darken_blend_8_ps_gram base active darken_blend_8_rv)
 [rv (choose (equal? darken_blend_8_rv (nested_selection_two_args (v0) (v0) select_two_args) ))]
[v0 (choose base active)]
) 

(define-grammar (select_two_args_gram int_x int_y)
 [rv (choose (if (v0) (v1) (v1) ))]
[v0 (choose (>= (v1) (v1) ) (> (v1) (v1) ) (equal? (v1) (v1) ) (< (v1) (v1) ) (<= (v1) (v1) ))]
[v1 (choose int_x int_y 0 2 128 255)]
) 

(define (darken_blend_8_inv0 active agg.result base col pixel row row_vec) (darken_blend_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (darken_blend_8_inv1 active base col pixel row_vec agg.result row) (darken_blend_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (darken_blend_8_ps base active darken_blend_8_rv) (darken_blend_8_ps_gram base active darken_blend_8_rv #:depth 10))

(define (select_two_args int_x int_y) (select_two_args_gram int_x int_y #:depth 10))

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
(define active (take (list (list active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2) (list active_BOUNDEDSET-3 active_BOUNDEDSET-4 active_BOUNDEDSET-5) (list active_BOUNDEDSET-6 active_BOUNDEDSET-7 active_BOUNDEDSET-8)) active_BOUNDEDSET-len))
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
(define agg.result (take (list (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2) (list agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5) (list agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8)) agg.result_BOUNDEDSET-len))
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
(define base (take (list (list base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2) (list base_BOUNDEDSET-3 base_BOUNDEDSET-4 base_BOUNDEDSET-5) (list base_BOUNDEDSET-6 base_BOUNDEDSET-7 base_BOUNDEDSET-8)) base_BOUNDEDSET-len))
(define-symbolic col integer?)
(define-symbolic darken_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic darken_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic darken_blend_8_rv_BOUNDEDSET-1 integer?)
(define-symbolic darken_blend_8_rv_BOUNDEDSET-2 integer?)
(define darken_blend_8_rv (take (list darken_blend_8_rv_BOUNDEDSET-0 darken_blend_8_rv_BOUNDEDSET-1 darken_blend_8_rv_BOUNDEDSET-2) darken_blend_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define-symbolic row_vec_BOUNDEDSET-2 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (length base ) 1 ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active (list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (length base ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (darken_blend_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (> (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (darken_blend_8_inv1 active base col pixel row_vec agg.result row) ) (&& (&& (&& (&& (&& (&& (&& (! (> (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (darken_blend_8_inv1 active base col pixel row_vec agg.result row) ) ) (darken_blend_8_inv1 active base (+ col 1 ) (if (&& (&& (&& (&& (&& (&& (&& (! (> (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (darken_blend_8_inv1 active base col pixel row_vec agg.result row) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) (list-list-append row_vec (if (&& (&& (&& (&& (&& (&& (&& (! (> (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (darken_blend_8_inv1 active base col pixel row_vec agg.result row) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (darken_blend_8_inv1 active base col pixel row_vec agg.result row) ) (darken_blend_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (length base ) ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (darken_blend_8_inv0 active agg.result base col pixel row row_vec) ) ) (darken_blend_8_ps base active agg.result) ) )))

(define sol
 (synthesize
 #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4 active_BOUNDEDSET-5 active_BOUNDEDSET-6 active_BOUNDEDSET-7 active_BOUNDEDSET-8 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4 base_BOUNDEDSET-5 base_BOUNDEDSET-6 base_BOUNDEDSET-7 base_BOUNDEDSET-8 col darken_blend_8_rv_BOUNDEDSET-len darken_blend_8_rv_BOUNDEDSET-0 darken_blend_8_rv_BOUNDEDSET-1 darken_blend_8_rv_BOUNDEDSET-2 pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
