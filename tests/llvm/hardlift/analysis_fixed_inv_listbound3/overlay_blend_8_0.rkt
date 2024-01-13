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

(define-grammar (overlay_blend_8_inv0_gram active agg.result base col pixel row row_vec)
 [rv (choose (&& (&& (>= row 0 ) (<= row (length base ) ) ) (equal? agg.result (nested_selection_two_args (list-take-noerr base row ) (list-take-noerr active row ) fixed_select_two_args) ) ))]

)

(define-grammar (overlay_blend_8_inv1_gram active base col pixel row_vec agg.result row)
 [rv (choose (&& (&& (&& (&& (&& (>= row 0 ) (< row (length base ) ) ) (>= col 0 ) ) (<= col (length (list-list-ref-noerr base 0 ) ) ) ) (equal? row_vec (selection_two_args (list-take-noerr (list-list-ref-noerr base row ) col ) (list-take-noerr (list-list-ref-noerr active row ) col ) fixed_select_two_args) ) ) (equal? agg.result (nested_selection_two_args (list-take-noerr base row ) (list-take-noerr active row ) fixed_select_two_args) ) ))]

)

(define-grammar (overlay_blend_8_ps_gram base active overlay_blend_8_rv)
 [rv (choose (equal? overlay_blend_8_rv (nested_selection_two_args (v0) (v0) select_two_args) ))]
[v0 (choose base active)]
)

(define-grammar (select_two_args_gram int_x int_y)
 [rv (choose (if (v0) (v1) (v1) ))]
[v0 (choose (>= (v1) (v1) ))]
[v1 (choose (v2) (+ (v2) (v2) ) (- (v2) (v2) ) (* (v2) (v2) ) (quotient-noerr (v2) (v2) ))]
[v2 (choose (v3) (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v3 (choose (v4) (+ (v4) (v4) ) (- (v4) (v4) ) (* (v4) (v4) ) (quotient-noerr (v4) (v4) ))]
[v4 (choose (v5) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v5 (choose (v6) (+ (v6) (v6) ) (- (v6) (v6) ) (* (v6) (v6) ) (quotient-noerr (v6) (v6) ))]
[v6 (choose int_x int_y 2 128 255)]
)

(define-grammar (fixed_select_two_args_gram int_x int_y)
 [rv (choose (if (>= int_x 128 ) (- (- (+ (* 2 int_x ) int_x ) (quotient-noerr (* (* 2 int_x ) int_x ) 255 ) ) 255 ) (quotient-noerr (* (* 2 int_x ) int_x ) 255 ) ))]

)

(define (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) (overlay_blend_8_inv0_gram active agg.result base col pixel row row_vec #:depth 10))
(define (overlay_blend_8_inv1 active base col pixel row_vec agg.result row) (overlay_blend_8_inv1_gram active base col pixel row_vec agg.result row #:depth 10))
(define (overlay_blend_8_ps base active overlay_blend_8_rv) (overlay_blend_8_ps_gram base active overlay_blend_8_rv #:depth 10))

(define (select_two_args int_x int_y) (select_two_args_gram int_x int_y #:depth 10))
(define (fixed_select_two_args int_x int_y) (fixed_select_two_args_gram int_x int_y #:depth 10))

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
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-1 integer?)
(define-symbolic overlay_blend_8_rv_BOUNDEDSET-2 integer?)
(define overlay_blend_8_rv (take (list overlay_blend_8_rv_BOUNDEDSET-0 overlay_blend_8_rv_BOUNDEDSET-1 overlay_blend_8_rv_BOUNDEDSET-2) overlay_blend_8_rv_BOUNDEDSET-len))
(define-symbolic pixel integer?)
(define-symbolic row integer?)
(define-symbolic row_vec_BOUNDEDSET-len integer?)
(define-symbolic row_vec_BOUNDEDSET-0 integer?)
(define-symbolic row_vec_BOUNDEDSET-1 integer?)
(define-symbolic row_vec_BOUNDEDSET-2 integer?)
(define row_vec (take (list row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2) row_vec_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (> (length base ) 1 ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active (list-empty ) base 0 0 0 (list-empty )) ) (=> (&& (&& (&& (&& (< row (length base ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (overlay_blend_8_inv1 active base 0 pixel (list-empty ) agg.result row) ) ) (=> (or (&& (&& (&& (&& (&& (&& (&& (>= (list-ref-noerr (list-list-ref-noerr base row ) col ) 128 ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (overlay_blend_8_inv1 active base col pixel row_vec agg.result row) ) (&& (&& (&& (&& (&& (&& (&& (! (>= (list-ref-noerr (list-list-ref-noerr base row ) col ) 128 ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (overlay_blend_8_inv1 active base col pixel row_vec agg.result row) ) ) (overlay_blend_8_inv1 active base (+ col 1 ) (if (&& (&& (&& (&& (&& (&& (&& (! (>= (list-ref-noerr (list-list-ref-noerr base row ) col ) 128 ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (overlay_blend_8_inv1 active base col pixel row_vec agg.result row) ) (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) ) 255 ) (- (- (+ (* 2 (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) ) 255 ) ) 255 ) ) (list-list-append row_vec (if (&& (&& (&& (&& (&& (&& (&& (! (>= (list-ref-noerr (list-list-ref-noerr base row ) col ) 128 ) ) (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (overlay_blend_8_inv1 active base col pixel row_vec agg.result row) ) (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) ) 255 ) (- (- (+ (* 2 (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (quotient-noerr (* (* 2 (list-ref-noerr (list-list-ref-noerr base row ) col ) ) (list-ref-noerr (list-list-ref-noerr base row ) col ) ) 255 ) ) 255 ) ) ) agg.result row) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< col (length (list-list-ref-noerr base 0 ) ) ) ) (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (overlay_blend_8_inv1 active base col pixel row_vec agg.result row) ) (overlay_blend_8_inv0 active (list-list-append agg.result row_vec ) base col pixel (+ row 1 ) row_vec) ) ) (=> (or (&& (&& (&& (&& (! (< row (length base ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) (&& (&& (&& (&& (&& (! true ) (! (< row (length base ) ) ) ) (> (length base ) 1 ) ) (equal? (length base ) (length active ) ) ) (equal? (length (list-list-ref-noerr base 0 ) ) (length (list-list-ref-noerr active 0 ) ) ) ) (overlay_blend_8_inv0 active agg.result base col pixel row row_vec) ) ) (overlay_blend_8_ps base active agg.result) ) )))

(define sol
 (synthesize
 #:forall (list active_BOUNDEDSET-len active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-2 active_BOUNDEDSET-3 active_BOUNDEDSET-4 active_BOUNDEDSET-5 active_BOUNDEDSET-6 active_BOUNDEDSET-7 active_BOUNDEDSET-8 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 agg.result_BOUNDEDSET-4 agg.result_BOUNDEDSET-5 agg.result_BOUNDEDSET-6 agg.result_BOUNDEDSET-7 agg.result_BOUNDEDSET-8 base_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-2 base_BOUNDEDSET-3 base_BOUNDEDSET-4 base_BOUNDEDSET-5 base_BOUNDEDSET-6 base_BOUNDEDSET-7 base_BOUNDEDSET-8 col overlay_blend_8_rv_BOUNDEDSET-len overlay_blend_8_rv_BOUNDEDSET-0 overlay_blend_8_rv_BOUNDEDSET-1 overlay_blend_8_rv_BOUNDEDSET-2 pixel row row_vec_BOUNDEDSET-len row_vec_BOUNDEDSET-0 row_vec_BOUNDEDSET-1 row_vec_BOUNDEDSET-2)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
