#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (firsts matrix) 
(if (< (matrix-length matrix ) 1 ) (list-empty ) (list-prepend (list-ref-noerr (matrix-ref-noerr matrix 0 ) 0 ) (firsts (matrix-tail-noerr matrix 1 )) ) )) 


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


 (define-bounded (matrix_selection_two_args matrix_x matrix_y select_two_args_arg) 
(if (or (< (matrix-length matrix_x ) 1 ) (! (equal? (matrix-length matrix_x ) (matrix-length matrix_y ) ) ) ) (matrix-empty ) (matrix-prepend (selection_two_args (matrix-ref-noerr matrix_x 0 ) (matrix-ref-noerr matrix_y 0 ) select_two_args_arg) (matrix_selection_two_args (matrix-tail-noerr matrix_x 1 ) (matrix-tail-noerr matrix_y 1 ) select_two_args_arg ) ) )) 


 (define-bounded (matrix_transpose matrix) 
(if (< (matrix-length matrix ) 1 ) (matrix-empty ) (matrix-prepend (firsts matrix) (matrix-transpose-noerr (rests matrix) ) ) )) 


 (define-bounded (matrix_vec_mul matrix_x x) 
(if (or (or (< (matrix-length matrix_x ) 1 ) (< (length (matrix-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (matrix-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) x)) (matrix_vec_mul (matrix-tail-noerr matrix_x 1 ) x ) ) )) 


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


 (define-bounded (selection_two_args x y select_two_args_arg) 
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (select_two_args_arg (list-ref-noerr x 0 ) (list-ref-noerr y 0 )) (selection_two_args (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) select_two_args_arg) ) )) 


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


 (define-bounded (normal_blend_8_ps active base opacity out) 
(equal? out (vec_elemwise_add (vec_scalar_mul opacity active) (vec_scalar_mul (- 32 opacity ) base)) )) 


 (define-bounded (normal_blend_8_inv0 active base i opacity out) 
(&& (>= i 0 ) (&& (<= i (length base ) ) (equal? out (vec_elemwise_add (vec_scalar_mul opacity (list-take-noerr active i )) (vec_scalar_mul (- 32 opacity ) (list-take-noerr base i ))) ) ) )) 

(define-symbolic active_BOUNDEDSET-len integer?)
(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define active (take (list active_BOUNDEDSET-0 active_BOUNDEDSET-1) active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-len integer?)
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define base (take (list base_BOUNDEDSET-0 base_BOUNDEDSET-1) base_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic normal_blend_8_rv_BOUNDEDSET-len integer?)
(define-symbolic normal_blend_8_rv_BOUNDEDSET-0 integer?)
(define-symbolic normal_blend_8_rv_BOUNDEDSET-1 integer?)
(define normal_blend_8_rv (take (list normal_blend_8_rv_BOUNDEDSET-0 normal_blend_8_rv_BOUNDEDSET-1) normal_blend_8_rv_BOUNDEDSET-len))
(define-symbolic opacity integer?)
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define vc (verify (assert (&& (&& (=> (&& (equal? (length base ) (length active ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active base 0 opacity (list-empty )) ) (=> (&& (&& (&& (< i (length base ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active base i opacity agg.result) ) (normal_blend_8_inv0 active base (+ i 1 ) opacity (list-append agg.result (+ (* opacity (list-ref-noerr active i ) ) (* (- 32 opacity ) (list-ref-noerr base i ) ) ) )) ) ) (=> (or (&& (&& (&& (! (< i (length base ) ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active base i opacity agg.result) ) (&& (&& (&& (&& (! true ) (! (< i (length base ) ) ) ) (equal? (length base ) (length active ) ) ) (> (length base ) 0 ) ) (normal_blend_8_inv0 active base i opacity agg.result) ) ) (normal_blend_8_ps active base opacity agg.result) ) ))))

vc
