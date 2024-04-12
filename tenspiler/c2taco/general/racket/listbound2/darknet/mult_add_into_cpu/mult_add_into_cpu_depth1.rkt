#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


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

(define-grammar (mult_add_into_cpu_inv0_gram N X Y Z agg.result i ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i N ) ) (equal? agg.result (v0) ) ))]
[v0 (choose (vec-slice-noerr (v1) (v2) (v2) ) (v5))]
[v1 (choose X Y Z)]
[v2 (choose (v3) (v4))]
[v3 (choose 0 N i)]
[v4 (choose (integer-sqrt-noerr (v3) ) (integer-exp-noerr (v3) ) (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v5 (choose (v6) (vec_elemwise_add (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_elemwise_sub (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_elemwise_mul (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_elemwise_div (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_add (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_sub (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_mul (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_div (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (scalar_vec_sub (v3) (vec-slice-noerr (v1) (v2) (v2) )) (scalar_vec_div (v3) (vec-slice-noerr (v1) (v2) (v2) )))]
[v6 (choose (vec_map (vec-slice-noerr (v1) (v2) (v2) ) map_int_to_int ))]
)

(define-grammar (mult_add_into_cpu_ps_gram N X Y Z mult_add_into_cpu_rv)
 [rv (choose (equal? mult_add_into_cpu_rv (v0) ))]
[v0 (choose (vec-slice-noerr (v1) (v2) (v2) ) (v5))]
[v1 (choose X Y Z)]
[v2 (choose (v3) (v4))]
[v3 (choose 0 N)]
[v4 (choose (integer-sqrt-noerr (v3) ) (integer-exp-noerr (v3) ) (+ (v3) (v3) ) (- (v3) (v3) ) (* (v3) (v3) ) (quotient-noerr (v3) (v3) ))]
[v5 (choose (v6) (vec_elemwise_add (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_elemwise_sub (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_elemwise_mul (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_elemwise_div (vec-slice-noerr (v1) (v2) (v2) ) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_add (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_sub (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_mul (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (vec_scalar_div (v3) (vec-slice-noerr (v1) (v2) (v2) ) ) (scalar_vec_sub (v3) (vec-slice-noerr (v1) (v2) (v2) )) (scalar_vec_div (v3) (vec-slice-noerr (v1) (v2) (v2) )))]
[v6 (choose (vec_map (vec-slice-noerr (v1) (v2) (v2) ) map_int_to_int ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (mult_add_into_cpu_inv0 N X Y Z agg.result i ref.tmp) (mult_add_into_cpu_inv0_gram N X Y Z agg.result i ref.tmp #:depth 10))
(define (mult_add_into_cpu_ps N X Y Z mult_add_into_cpu_rv) (mult_add_into_cpu_ps_gram N X Y Z mult_add_into_cpu_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic N integer?)
(define-symbolic X_BOUNDEDSET-len integer?)
(define-symbolic X_BOUNDEDSET-0 integer?)
(define-symbolic X_BOUNDEDSET-1 integer?)
(define X (take (list X_BOUNDEDSET-0 X_BOUNDEDSET-1) X_BOUNDEDSET-len))
(define-symbolic Y_BOUNDEDSET-len integer?)
(define-symbolic Y_BOUNDEDSET-0 integer?)
(define-symbolic Y_BOUNDEDSET-1 integer?)
(define Y (take (list Y_BOUNDEDSET-0 Y_BOUNDEDSET-1) Y_BOUNDEDSET-len))
(define-symbolic Z_BOUNDEDSET-len integer?)
(define-symbolic Z_BOUNDEDSET-0 integer?)
(define-symbolic Z_BOUNDEDSET-1 integer?)
(define Z (take (list Z_BOUNDEDSET-0 Z_BOUNDEDSET-1) Z_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic mult_add_into_cpu_rv_BOUNDEDSET-len integer?)
(define-symbolic mult_add_into_cpu_rv_BOUNDEDSET-0 integer?)
(define-symbolic mult_add_into_cpu_rv_BOUNDEDSET-1 integer?)
(define mult_add_into_cpu_rv (take (list mult_add_into_cpu_rv_BOUNDEDSET-0 mult_add_into_cpu_rv_BOUNDEDSET-1) mult_add_into_cpu_rv_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (&& (>= N 1 ) (>= (length X ) N ) ) (>= (length Y ) N ) ) (>= (length Z ) N ) ) (mult_add_into_cpu_inv0 N X Y Z (list-empty ) 0 0) ) (=> (&& (&& (&& (&& (&& (< i N ) (>= N 1 ) ) (>= (length X ) N ) ) (>= (length Y ) N ) ) (>= (length Z ) N ) ) (mult_add_into_cpu_inv0 N X Y Z agg.result i ref.tmp) ) (mult_add_into_cpu_inv0 N X Y Z (list-append agg.result (+ (list-ref-noerr Z i ) (* (list-ref-noerr X i ) (list-ref-noerr Y i ) ) ) ) (+ i 1 ) (+ (list-ref-noerr Z i ) (* (list-ref-noerr X i ) (list-ref-noerr Y i ) ) )) ) ) (=> (or (&& (&& (&& (&& (&& (! (< i N ) ) (>= N 1 ) ) (>= (length X ) N ) ) (>= (length Y ) N ) ) (>= (length Z ) N ) ) (mult_add_into_cpu_inv0 N X Y Z agg.result i ref.tmp) ) (&& (&& (&& (&& (&& (&& (! true ) (! (< i N ) ) ) (>= N 1 ) ) (>= (length X ) N ) ) (>= (length Y ) N ) ) (>= (length Z ) N ) ) (mult_add_into_cpu_inv0 N X Y Z agg.result i ref.tmp) ) ) (mult_add_into_cpu_ps N X Y Z agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list N X_BOUNDEDSET-len X_BOUNDEDSET-0 X_BOUNDEDSET-1 Y_BOUNDEDSET-len Y_BOUNDEDSET-0 Y_BOUNDEDSET-1 Z_BOUNDEDSET-len Z_BOUNDEDSET-0 Z_BOUNDEDSET-1 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 i mult_add_into_cpu_rv_BOUNDEDSET-len mult_add_into_cpu_rv_BOUNDEDSET-0 mult_add_into_cpu_rv_BOUNDEDSET-1 ref.tmp)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
