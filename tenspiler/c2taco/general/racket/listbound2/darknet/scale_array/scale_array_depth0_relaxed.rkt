#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/sahilbhatia/Documents/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


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

(define-grammar (scale_array_inv0_gram a agg.result i n ref.tmp s)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose n (- n 1 ) (+ n 1 ))]
[v2 (choose (vec-slice-noerr a (v3) (v3) ))]
[v3 (choose (v4))]
[v4 (choose (v5) (- (v5) 1 ) (+ (v5) 1 ))]
[v5 (choose 0 n i s)]
)

(define-grammar (scale_array_ps_gram a n s scale_array_rv)
 [rv (choose (equal? scale_array_rv (v0) ))]
[v0 (choose (vec-slice-noerr a (v1) (v1) ))]
[v1 (choose (v2))]
[v2 (choose (v3) (- (v3) 1 ) (+ (v3) 1 ))]
[v3 (choose 0 n s)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (scale_array_inv0 a agg.result i n ref.tmp s) (scale_array_inv0_gram a agg.result i n ref.tmp s #:depth 10))
(define (scale_array_ps a n s scale_array_rv) (scale_array_ps_gram a n s scale_array_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1) a_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic s integer?)
(define-symbolic scale_array_rv_BOUNDEDSET-len integer?)
(define-symbolic scale_array_rv_BOUNDEDSET-0 integer?)
(define-symbolic scale_array_rv_BOUNDEDSET-1 integer?)
(define scale_array_rv (take (list scale_array_rv_BOUNDEDSET-0 scale_array_rv_BOUNDEDSET-1) scale_array_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length a ) n ) ) (scale_array_inv0 a (list-empty ) 0 n 0 s) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length a ) n ) ) (scale_array_inv0 a agg.result i n ref.tmp s) ) (scale_array_inv0 a (list-append agg.result (* (list-ref-noerr a i ) s ) ) (+ i 1 ) n (* (list-ref-noerr a i ) s ) s) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length a ) n ) ) (scale_array_inv0 a agg.result i n ref.tmp s) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length a ) n ) ) (scale_array_inv0 a agg.result i n ref.tmp s) ) ) (scale_array_ps a n s agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 i n ref.tmp s scale_array_rv_BOUNDEDSET-len scale_array_rv_BOUNDEDSET-0 scale_array_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)