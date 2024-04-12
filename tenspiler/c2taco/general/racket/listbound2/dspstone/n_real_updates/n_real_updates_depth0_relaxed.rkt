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

(define-grammar (n_real_updates_inv0_gram A B C N agg.result curr i)
 [rv (choose (&& (&& (>= i (v0) ) (<= i (v1) ) ) (equal? agg.result (v2) ) ))]
[v0 (choose 0 (- 0 1 ) (+ 0 1 ))]
[v1 (choose N (- N 1 ) (+ N 1 ))]
[v2 (choose (vec-slice-noerr (v3) (v4) (v4) ))]
[v3 (choose A B C)]
[v4 (choose (v5))]
[v5 (choose (v6) (- (v6) 1 ) (+ (v6) 1 ))]
[v6 (choose 0 N i)]
)

(define-grammar (n_real_updates_ps_gram N A B C n_real_updates_rv)
 [rv (choose (equal? n_real_updates_rv (v0) ))]
[v0 (choose (vec-slice-noerr (v1) (v2) (v2) ))]
[v1 (choose A B C)]
[v2 (choose (v3))]
[v3 (choose (v4) (- (v4) 1 ) (+ (v4) 1 ))]
[v4 (choose 0 N)]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (n_real_updates_inv0 A B C N agg.result curr i) (n_real_updates_inv0_gram A B C N agg.result curr i #:depth 10))
(define (n_real_updates_ps N A B C n_real_updates_rv) (n_real_updates_ps_gram N A B C n_real_updates_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic A_BOUNDEDSET-len integer?)
(define-symbolic A_BOUNDEDSET-0 integer?)
(define-symbolic A_BOUNDEDSET-1 integer?)
(define A (take (list A_BOUNDEDSET-0 A_BOUNDEDSET-1) A_BOUNDEDSET-len))
(define-symbolic B_BOUNDEDSET-len integer?)
(define-symbolic B_BOUNDEDSET-0 integer?)
(define-symbolic B_BOUNDEDSET-1 integer?)
(define B (take (list B_BOUNDEDSET-0 B_BOUNDEDSET-1) B_BOUNDEDSET-len))
(define-symbolic C_BOUNDEDSET-len integer?)
(define-symbolic C_BOUNDEDSET-0 integer?)
(define-symbolic C_BOUNDEDSET-1 integer?)
(define C (take (list C_BOUNDEDSET-0 C_BOUNDEDSET-1) C_BOUNDEDSET-len))
(define-symbolic N integer?)
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic curr integer?)
(define-symbolic i integer?)
(define-symbolic n_real_updates_rv_BOUNDEDSET-len integer?)
(define-symbolic n_real_updates_rv_BOUNDEDSET-0 integer?)
(define-symbolic n_real_updates_rv_BOUNDEDSET-1 integer?)
(define n_real_updates_rv (take (list n_real_updates_rv_BOUNDEDSET-0 n_real_updates_rv_BOUNDEDSET-1) n_real_updates_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (&& (>= N 1 ) (>= (length A ) N ) ) (>= (length B ) N ) ) (>= (length C ) N ) ) (n_real_updates_inv0 A B C N (list-empty ) 0 0) ) (=> (&& (&& (&& (&& (&& (< i N ) (>= N 1 ) ) (>= (length A ) N ) ) (>= (length B ) N ) ) (>= (length C ) N ) ) (n_real_updates_inv0 A B C N agg.result curr i) ) (n_real_updates_inv0 A B C N (list-append agg.result (+ (list-ref-noerr C i ) (* (list-ref-noerr A i ) (list-ref-noerr B i ) ) ) ) (+ (list-ref-noerr C i ) (* (list-ref-noerr A i ) (list-ref-noerr B i ) ) ) (+ i 1 )) ) ) (=> (or (&& (&& (&& (&& (&& (! (< i N ) ) (>= N 1 ) ) (>= (length A ) N ) ) (>= (length B ) N ) ) (>= (length C ) N ) ) (n_real_updates_inv0 A B C N agg.result curr i) ) (&& (&& (&& (&& (&& (&& (! true ) (! (< i N ) ) ) (>= N 1 ) ) (>= (length A ) N ) ) (>= (length B ) N ) ) (>= (length C ) N ) ) (n_real_updates_inv0 A B C N agg.result curr i) ) ) (n_real_updates_ps N A B C agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list A_BOUNDEDSET-len A_BOUNDEDSET-0 A_BOUNDEDSET-1 B_BOUNDEDSET-len B_BOUNDEDSET-0 B_BOUNDEDSET-1 C_BOUNDEDSET-len C_BOUNDEDSET-0 C_BOUNDEDSET-1 N agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 curr i n_real_updates_rv_BOUNDEDSET-len n_real_updates_rv_BOUNDEDSET-0 n_real_updates_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
