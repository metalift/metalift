#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_sub x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_elemwise_div x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_div (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (vec_scalar_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) a ) (vec_scalar_sub a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (vec_scalar_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr (list-ref-noerr x 0 ) a ) (vec_scalar_div a (list-tail-noerr x 1 ) ) ) ))


 (define-bounded (scalar_vec_sub a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- a (list-ref-noerr x 0 ) ) (scalar_vec_sub a (list-tail-noerr x 1 )) ) ))


 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int ) ) ))


 (define-bounded (reduce_max x)
(if (<= (length x ) 1 ) (list-ref-noerr x 0 ) (if (> (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_mul x)
(if (< (length x ) 1 ) 1 (* (list-ref-noerr x 0 ) (reduce_mul (list-tail-noerr x 1 )) ) ))


 (define-bounded (matrix_vec_mul matrix_x x)
(if (or (or (< (matrix-length matrix_x ) 1 ) (< (length (matrix-ref-noerr matrix_x 0 ) ) 1 ) ) (! (equal? (length (matrix-ref-noerr matrix_x 0 ) ) (length x ) ) ) ) (list-empty ) (list-prepend (reduce_sum (vec_elemwise_mul (matrix-ref-noerr matrix_x 0 ) x )) (matrix_vec_mul (matrix-tail-noerr matrix_x 1 ) x ) ) ))

(define-grammar (mat1x3_inv0_gram N agg.result f h i sum x)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose N (- N 1 ) (+ N 1 ))]
[v2 (choose (v3))]
[v3 (choose (vec-slice-noerr x (v4) (v4) ) (matrix-ref-noerr (v7) (v4) ))]
[v4 (choose (v5))]
[v5 (choose (v6) (- (v6) 1 ) (+ (v6) 1 ))]
[v6 (choose 0 N i)]
[v7 (choose (v8) (matrix-transpose-noerr (v8) ))]
[v8 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr h (v4) (v4) ) (v4) (v4) ))]
)

(define-grammar (mat1x3_inv1_gram N f h sum x agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i (v0) ) (< i (v1) ) ) (>= f (v0) ) ) (<= f (v1) ) ) (equal? sum (v2) ) ) (equal? agg.result (v3) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose N (- N 1 ) (+ N 1 ))]
[v2 (choose (reduce_sum (v3)) (reduce_mul (v3)) (reduce_max (v3)))]
[v3 (choose (v4))]
[v4 (choose (vec-slice-noerr x (v5) (v5) ) (matrix-ref-noerr (v8) (v5) ))]
[v5 (choose (v6))]
[v6 (choose (v7) (- (v7) 1 ) (+ (v7) 1 ))]
[v7 (choose 0 N i f)]
[v8 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr h (v5) (v5) ) (v5) (v5) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr h (v5) (v5) ) (v5) (v5) ) ))]
)

(define-grammar (mat1x3_ps_gram N h x mat1x3_rv)
 [rv (choose (equal? mat1x3_rv (v0) ))]
[v0 (choose (v1))]
[v1 (choose (vec-slice-noerr x (v2) (v2) ) (matrix-ref-noerr (v5) (v2) ))]
[v2 (choose (v3))]
[v3 (choose (v4) (- (v4) 1 ) (+ (v4) 1 ))]
[v4 (choose 0 N)]
[v5 (choose (v6) (matrix-transpose-noerr (v6) ))]
[v6 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr h (v2) (v2) ) (v2) (v2) ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (mat1x3_inv0 N agg.result f h i sum x) (mat1x3_inv0_gram N agg.result f h i sum x #:depth 10))
(define (mat1x3_inv1 N f h sum x agg.result i) (mat1x3_inv1_gram N f h sum x agg.result i #:depth 10))
(define (mat1x3_ps N h x mat1x3_rv) (mat1x3_ps_gram N h x mat1x3_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic N integer?)
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic f integer?)
(define-symbolic h_BOUNDEDSET-len integer?)
(define-symbolic h_BOUNDEDSET-0 integer?)
(define-symbolic h_BOUNDEDSET-1 integer?)
(define-symbolic h_BOUNDEDSET-2 integer?)
(define-symbolic h_BOUNDEDSET-3 integer?)
(define h (take (list (list h_BOUNDEDSET-0 h_BOUNDEDSET-1) (list h_BOUNDEDSET-2 h_BOUNDEDSET-3)) h_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic mat1x3_rv_BOUNDEDSET-len integer?)
(define-symbolic mat1x3_rv_BOUNDEDSET-0 integer?)
(define-symbolic mat1x3_rv_BOUNDEDSET-1 integer?)
(define mat1x3_rv (take (list mat1x3_rv_BOUNDEDSET-0 mat1x3_rv_BOUNDEDSET-1) mat1x3_rv_BOUNDEDSET-len))
(define-symbolic sum integer?)
(define-symbolic x_BOUNDEDSET-len integer?)
(define-symbolic x_BOUNDEDSET-0 integer?)
(define-symbolic x_BOUNDEDSET-1 integer?)
(define x (take (list x_BOUNDEDSET-0 x_BOUNDEDSET-1) x_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (>= N 1 ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N (list-empty ) 0 h 0 0 x) ) (=> (&& (&& (&& (&& (&& (< i N ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (mat1x3_inv1 N 0 h 0 x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (< f N ) (< i N ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (mat1x3_inv1 N f h sum x agg.result i) ) (mat1x3_inv1 N (+ f 1 ) h (+ sum (* (list-ref-noerr (matrix-ref-noerr h i ) f ) (list-ref-noerr x f ) ) ) x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (! (< f N ) ) (< i N ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (mat1x3_inv1 N f h sum x agg.result i) ) (mat1x3_inv0 N (list-append agg.result sum ) f h (+ i 1 ) sum x) ) ) (=> (or (&& (&& (&& (&& (&& (! (< i N ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) (&& (&& (&& (&& (&& (&& (! true ) (! (< i N ) ) ) (>= N 1 ) ) (>= (matrix-length h ) N ) ) (>= (length (matrix-ref-noerr h 0 ) ) N ) ) (>= (length x ) N ) ) (mat1x3_inv0 N agg.result f h i sum x) ) ) (mat1x3_ps N h x agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list N agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 f h_BOUNDEDSET-len h_BOUNDEDSET-0 h_BOUNDEDSET-1 h_BOUNDEDSET-2 h_BOUNDEDSET-3 i mat1x3_rv_BOUNDEDSET-len mat1x3_rv_BOUNDEDSET-0 mat1x3_rv_BOUNDEDSET-1 sum x_BOUNDEDSET-len x_BOUNDEDSET-0 x_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
