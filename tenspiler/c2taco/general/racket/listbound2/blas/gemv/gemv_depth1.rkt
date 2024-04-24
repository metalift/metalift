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

(define-grammar (gemv_inv0_gram A M N agg.result i j sum x)
 [rv (choose (&& (&& (>= i 0 ) (<= i M ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (v1) (v7))]
[v1 (choose (vec-slice-noerr x (v2) (v2) ) (matrix-ref-noerr (v5) (v2) ))]
[v2 (choose (v3) (v4))]
[v3 (choose 0 M N i)]
[v4 (choose (integer-sqrt-noerr (v3) ) (integer-exp-noerr (v3) ) (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v5 (choose (v6) (matrix-transpose-noerr (v6) ))]
[v6 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr A (v2) (v2) ) (v2) (v2) ))]
[v7 (choose (v8) (vec_elemwise_add (v1) (v1) ) (vec_elemwise_sub (v1) (v1) ) (vec_elemwise_mul (v1) (v1) ) (vec_elemwise_div (v1) (v1) ) (vec_scalar_add (v3) (v1) ) (vec_scalar_sub (v3) (v1) ) (vec_scalar_mul (v3) (v1) ) (vec_scalar_div (v3) (v1) ) (scalar_vec_sub (v3) (v1)) (scalar_vec_div (v3) (v1)) (matrix_vec_mul (v5) (v1) ))]
[v8 (choose (vec_map (v1) map_int_to_int ))]
)

(define-grammar (gemv_inv1_gram A M N j sum x agg.result i)
 [rv (choose (&& (&& (&& (&& (&& (>= i 0 ) (< i M ) ) (>= j 0 ) ) (<= j N ) ) (equal? sum (v0) ) ) (equal? agg.result (v1) ) ))]
[v0 (choose (reduce_sum (v1)) (reduce_mul (v1)) (reduce_max (v1)))]
[v1 (choose (v2) (v7))]
[v2 (choose (vec-slice-noerr x (v3) (v3) ) (matrix-ref-noerr (v6) (v3) ))]
[v3 (choose (v4) (v5))]
[v4 (choose 0 M N i j)]
[v5 (choose (integer-sqrt-noerr (v4) ) (integer-exp-noerr (v4) ) (+ (v4) (v4) ) (- (v4) (v4) ) (* (v4) (v4) ) (quotient-noerr (v4) (v4) ))]
[v6 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr A (v3) (v3) ) (v3) (v3) ) (matrix-transpose-noerr (matrix-col-slice-noerr (matrix-row-slice-noerr A (v3) (v3) ) (v3) (v3) ) ))]
[v7 (choose (v8) (vec_elemwise_add (v2) (v2) ) (vec_elemwise_sub (v2) (v2) ) (vec_elemwise_mul (v2) (v2) ) (vec_elemwise_div (v2) (v2) ) (vec_scalar_add (v4) (v2) ) (vec_scalar_sub (v4) (v2) ) (vec_scalar_mul (v4) (v2) ) (vec_scalar_div (v4) (v2) ) (scalar_vec_sub (v4) (v2)) (scalar_vec_div (v4) (v2)) (matrix_vec_mul (v6) (v2) ))]
[v8 (choose (vec_map (v2) map_int_to_int ))]
)

(define-grammar (gemv_ps_gram M N A x gemv_rv)
 [rv (choose (equal? gemv_rv (v0) ))]
[v0 (choose (v1) (v7))]
[v1 (choose (vec-slice-noerr x (v2) (v2) ) (matrix-ref-noerr (v5) (v2) ))]
[v2 (choose (v3) (v4))]
[v3 (choose 0 M N)]
[v4 (choose (integer-sqrt-noerr (v3) ) (integer-exp-noerr (v3) ) (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v5 (choose (v6) (matrix-transpose-noerr (v6) ))]
[v6 (choose (matrix-col-slice-noerr (matrix-row-slice-noerr A (v2) (v2) ) (v2) (v2) ))]
[v7 (choose (v8) (vec_elemwise_add (v1) (v1) ) (vec_elemwise_sub (v1) (v1) ) (vec_elemwise_mul (v1) (v1) ) (vec_elemwise_div (v1) (v1) ) (vec_scalar_add (v3) (v1) ) (vec_scalar_sub (v3) (v1) ) (vec_scalar_mul (v3) (v1) ) (vec_scalar_div (v3) (v1) ) (scalar_vec_sub (v3) (v1)) (scalar_vec_div (v3) (v1)) (matrix_vec_mul (v5) (v1) ))]
[v8 (choose (vec_map (v1) map_int_to_int ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (gemv_inv0 A M N agg.result i j sum x) (gemv_inv0_gram A M N agg.result i j sum x #:depth 10))
(define (gemv_inv1 A M N j sum x agg.result i) (gemv_inv1_gram A M N j sum x agg.result i #:depth 10))
(define (gemv_ps M N A x gemv_rv) (gemv_ps_gram M N A x gemv_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic A_BOUNDEDSET-len integer?)
(define-symbolic A_BOUNDEDSET-0 integer?)
(define-symbolic A_BOUNDEDSET-1 integer?)
(define-symbolic A_BOUNDEDSET-2 integer?)
(define-symbolic A_BOUNDEDSET-3 integer?)
(define A (take (list (list A_BOUNDEDSET-0 A_BOUNDEDSET-1) (list A_BOUNDEDSET-2 A_BOUNDEDSET-3)) A_BOUNDEDSET-len))
(define-symbolic M integer?)
(define-symbolic N integer?)
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic gemv_rv_BOUNDEDSET-len integer?)
(define-symbolic gemv_rv_BOUNDEDSET-0 integer?)
(define-symbolic gemv_rv_BOUNDEDSET-1 integer?)
(define gemv_rv (take (list gemv_rv_BOUNDEDSET-0 gemv_rv_BOUNDEDSET-1) gemv_rv_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic j integer?)
(define-symbolic sum integer?)
(define-symbolic x_BOUNDEDSET-len integer?)
(define-symbolic x_BOUNDEDSET-0 integer?)
(define-symbolic x_BOUNDEDSET-1 integer?)
(define x (take (list x_BOUNDEDSET-0 x_BOUNDEDSET-1) x_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (&& (&& (=> (&& (&& (&& (&& (>= M 1 ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N (list-empty ) 0 0 0 x) ) (=> (&& (&& (&& (&& (&& (&& (< i M ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (gemv_inv1 A M N 0 0 x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (< j N ) (< i M ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (gemv_inv1 A M N j sum x agg.result i) ) (gemv_inv1 A M N (+ j 1 ) (+ sum (* (list-ref-noerr (matrix-ref-noerr A i ) j ) (list-ref-noerr x j ) ) ) x agg.result i) ) ) (=> (&& (&& (&& (&& (&& (&& (&& (&& (! (< j N ) ) (< i M ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (gemv_inv1 A M N j sum x agg.result i) ) (gemv_inv0 A M N (list-append agg.result sum ) (+ i 1 ) j sum x) ) ) (=> (or (&& (&& (&& (&& (&& (&& (! (< i M ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) (&& (&& (&& (&& (&& (&& (&& (! true ) (! (< i M ) ) ) (>= M 1 ) ) (>= N 1 ) ) (>= (matrix-length A ) M ) ) (>= (length (matrix-ref-noerr A 0 ) ) N ) ) (>= (length x ) N ) ) (gemv_inv0 A M N agg.result i j sum x) ) ) (gemv_ps M N A x agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list A_BOUNDEDSET-len A_BOUNDEDSET-0 A_BOUNDEDSET-1 A_BOUNDEDSET-2 A_BOUNDEDSET-3 M N agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 gemv_rv_BOUNDEDSET-len gemv_rv_BOUNDEDSET-0 gemv_rv_BOUNDEDSET-1 i j sum x_BOUNDEDSET-len x_BOUNDEDSET-0 x_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
