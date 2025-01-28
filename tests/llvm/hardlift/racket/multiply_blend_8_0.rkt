#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)



 (define-bounded (nested_selection_two_args nested_x nested_y select_two_args) 
(if (or (< (list-list-length nested_x ) 1 ) (! (equal? (list-list-length nested_x ) (list-list-length nested_y ) ) ) ) (list-list-empty ) (list-list-prepend (selection_two_args (list-list-ref-noerr nested_x 0 ) (list-list-ref-noerr nested_y 0 ) select_two_args) (nested_selection_two_args (list-list-tail-noerr nested_x 1 ) (list-list-tail-noerr nested_y 1 ) select_two_args) ) )) 

(define-grammar (multiply_blend_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (v0) (v2) ) (equal? agg.result (nested_selection_two_args (v4) (v4) select_two_args) ) ))]
[v0 (choose (>= row (v1) ) (> row (v1) ) (equal? row (v1) ) (< row (v1) ) (<= row (v1) ))]
[v1 (choose (- 1 0 ) 0 1)]
[v2 (choose (>= row (v3) ) (> row (v3) ) (equal? row (v3) ) (< row (v3) ) (<= row (v3) ))]
[v3 (choose (list-list-length base ) (length (list-list-ref-noerr base 0 ) ))]
[v4 (choose base (list-list-take-noerr base row ) (list-list-take-noerr base col ) active (list-list-take-noerr active row ) (list-list-take-noerr active col ))]
) 

(define-grammar (multiply_blend_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (v0) (v2) ) (v4) ) (v5) ) (equal? row_vec (selection_two_args (v6) (v6) select_two_args) ) ) (equal? agg.result (nested_selection_two_args (v7) (v7) select_two_args) ) ))]
[v0 (choose (>= row (v1) ) (> row (v1) ) (equal? row (v1) ) (< row (v1) ) (<= row (v1) ))]
[v1 (choose (- 1 0 ) 0 1)]
[v2 (choose (>= row (v3) ) (> row (v3) ) (equal? row (v3) ) (< row (v3) ) (<= row (v3) ))]
[v3 (choose (list-list-length base ) (length (list-list-ref-noerr base 0 ) ))]
[v4 (choose (>= col (v1) ) (> col (v1) ) (equal? col (v1) ) (< col (v1) ) (<= col (v1) ))]
[v5 (choose (>= col (v3) ) (> col (v3) ) (equal? col (v3) ) (< col (v3) ) (<= col (v3) ))]
[v6 (choose (list-take-noerr (list-list-ref-noerr base 0 ) col ) (list-take-noerr (list-list-ref-noerr base row ) col ) (list-take-noerr (list-list-ref-noerr base col ) row ) (list-take-noerr (list-list-ref-noerr base 0 ) row ) (list-take-noerr (list-list-ref-noerr active 0 ) col ) (list-take-noerr (list-list-ref-noerr active row ) col ) (list-take-noerr (list-list-ref-noerr active col ) row ) (list-take-noerr (list-list-ref-noerr active 0 ) row ) row_vec)]
[v7 (choose base (list-list-take-noerr base row ) (list-list-take-noerr base col ) active (list-list-take-noerr active row ) (list-list-take-noerr active col ))]
) 

(define-grammar (multiply_blend_8_ps_gram base active multiply_blend_8_rv)
 [rv (choose (equal? multiply_blend_8_rv (nested_selection_two_args (v0) (v0) select_two_args) ))]
[v0 (choose base active)]
) 

(define-grammar (select_two_args_gram int_x int_y)
 [rv (choose (v0))]
[v0 (choose (quotient (* int_x int_y ) 255 ) (- (+ int_x int_y ) 255 ) (if (equal? int_y 0 ) 255 (- 255 (quotient (- 255 int_x ) int_y ) ) ) (if (< int_x int_y ) int_y int_x ) (- (+ int_x int_y ) (quotient (* int_x int_y ) 255 ) ) (+ int_x int_y ) (if (equal? int_y 255 ) 255 (quotient int_x (- 255 int_y ) ) ) (if (>= int_x 128 ) (- (- (+ (* 2 int_x ) int_x ) (quotient (* (* 2 int_x ) int_x ) 255 ) ) 255 ) (quotient (* (* 2 int_x ) int_x ) 255 ) ) (if (> int_x int_y ) int_y int_x ))]
) 

(define-grammar (selection_two_args_gram x y select_two_args)
 [rv (choose (if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (select_two_args (list-ref-noerr x 0 ) (list-ref-noerr y 0 )) (selection_two_args (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) select_two_args) ) ))]

) 

(define (multiply_blend_8_inv0 active agg.result base col pixel row row_vec) (multiply_blend_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (multiply_blend_8_inv1 active base col pixel row_vec agg.result row) (multiply_blend_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (multiply_blend_8_ps base active multiply_blend_8_rv) (multiply_blend_8_ps_gram base active multiply_blend_8_rv #:depth 10))

(define (select_two_args int_x int_y) (select_two_args_gram int_x int_y #:depth 10))
(define (selection_two_args x y select_two_args) (selection_two_args_gram x y select_two_args #:depth 10))

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
(define-symbolic multiply_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic multiply_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic multiply_blend_8_rv_BOUNDEDSET-1 integer?)
(define-symbolic multiply_blend_8_rv_BOUNDEDSET-2 integer?)
(define multiply_blend_8_rv (take (list multiply_blend_8_rv_BOUNDEDSET-0 multiply_blend_8_rv_BOUNDEDSET-1 multiply_blend_8_rv_BOUNDEDSET-2) multiply_blend_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define-symbolic row_vec_BOUNDEDSET-2 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (list-list-length base ) 1 ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (multiply_blend_8_inv0 active (list-list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (list-list-length base ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (multiply_blend_8_inv0 active agg.result base col pixel row row_vec) ) (multiply_blend_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (< col (length (list-list-ref-noerr base 0 ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (multiply_blend_8_inv0 active agg.result base col pixel row row_vec) ) (multiply_blend_8_inv1 active base col pixel row_vec agg.result row) ) (multiply_blend_8_inv1 active base (+ col 1 ) (quotient (* (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) 255 ) (list-list-append row_vec (quotient (* (list-ref-noerr (list-list-ref-noerr base row ) col ) (list-ref-noerr (list-list-ref-noerr active row ) col ) ) 255 ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (multiply_blend_8_inv0 active agg.result base col pixel row row_vec) ) (multiply_blend_8_inv1 active base col pixel row_vec agg.result row) ) (multiply_blend_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (list-list-length base ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (multiply_blend_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (list-list-length base ) ) ) ) (> (list-list-length base ) 1 ) ) (equal? (list-list-length base ) (list-list-length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (multiply_blend_8_inv0 active agg.result base col pixel row row_vec) ) ) (multiply_blend_8_ps base active agg.result) ) )))

(define sol
 (synthesize
 #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4 active_BOUNDEDSET-5 active_BOUNDEDSET-6 active_BOUNDEDSET-7 active_BOUNDEDSET-8 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4 base_BOUNDEDSET-5 base_BOUNDEDSET-6 base_BOUNDEDSET-7 base_BOUNDEDSET-8 col multiply_blend_8_rv_BOUNDEDSET-len multiply_blend_8_rv_BOUNDEDSET-0 multiply_blend_8_rv_BOUNDEDSET-1 multiply_blend_8_rv_BOUNDEDSET-2 pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
