#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (rmsnorm_part2_inv0_gram agg.result i input ref.tmp ss weight)
 [rv (choose (&& (&& (>= i 0 ) (<= i (length input ) ) ) (equal? agg.result (vec_scalar_mul (quotient-noerr (v0) (integer-sqrt-noerr (+ (quotient-noerr (v1) (v1) ) (v0) ) ) ) (vec_elemwise_mul (v2) (v2))) ) ))]
[v0 (choose 1)]
[v1 (choose ss (length input ))]
[v2 (choose (list-take-noerr input i ) (list-take-noerr weight i ))]
)

(define-grammar (rmsnorm_part2_ps_gram input weight ss rmsnorm_part2_rv)
 [rv (choose (equal? rmsnorm_part2_rv (vec_scalar_mul (quotient-noerr (v0) (integer-sqrt-noerr (+ (quotient-noerr (v1) (v1) ) (v0) ) ) ) (vec_elemwise_mul (v2) (v2))) ))]
[v0 (choose 1)]
[v1 (choose ss (length input ))]
[v2 (choose input weight)]
)

(define (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) (rmsnorm_part2_inv0_gram agg.result i input ref.tmp ss weight #:depth 10))
(define (rmsnorm_part2_ps input weight ss rmsnorm_part2_rv) (rmsnorm_part2_ps_gram input weight ss rmsnorm_part2_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) agg.result_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define-symbolic input_BOUNDEDSET-2 integer?)
(define-symbolic input_BOUNDEDSET-3 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3) input_BOUNDEDSET-len))
(define-symbolic ref.tmp integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-len integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-0 integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-1 integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-2 integer?)
(define-symbolic rmsnorm_part2_rv_BOUNDEDSET-3 integer?)
(define rmsnorm_part2_rv (take (list rmsnorm_part2_rv_BOUNDEDSET-0 rmsnorm_part2_rv_BOUNDEDSET-1 rmsnorm_part2_rv_BOUNDEDSET-2 rmsnorm_part2_rv_BOUNDEDSET-3) rmsnorm_part2_rv_BOUNDEDSET-len))
(define-symbolic ss integer?)
(define-symbolic weight_BOUNDEDSET-len integer?)
(define-symbolic weight_BOUNDEDSET-0 integer?)
(define-symbolic weight_BOUNDEDSET-1 integer?)
(define-symbolic weight_BOUNDEDSET-2 integer?)
(define-symbolic weight_BOUNDEDSET-3 integer?)
(define weight (take (list weight_BOUNDEDSET-0 weight_BOUNDEDSET-1 weight_BOUNDEDSET-2 weight_BOUNDEDSET-3) weight_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (equal? (length input ) (length weight ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 (list-empty ) 0 input 0 ss weight) ) (=> (&& (&& (&& (< i (length input ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) ) (rmsnorm_part2_inv0 (list-append agg.result (* (* (quotient-noerr 1 (integer-sqrt-noerr (+ (quotient-noerr ss (length input ) ) 1 ) ) ) (list-ref-noerr input i ) ) (list-ref-noerr weight i ) ) ) (+ i 1 ) input (* (* (quotient-noerr 1 (integer-sqrt-noerr (+ (quotient-noerr ss (length input ) ) 1 ) ) ) (list-ref-noerr input i ) ) (list-ref-noerr weight i ) ) ss weight) ) ) (=> (or (&& (&& (&& (! (< i (length input ) ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) ) (&& (&& (&& (&& (! true ) (! (< i (length input ) ) ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part2_inv0 agg.result i input ref.tmp ss weight) ) ) (rmsnorm_part2_ps input weight ss agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3 ref.tmp rmsnorm_part2_rv_BOUNDEDSET-len rmsnorm_part2_rv_BOUNDEDSET-0 rmsnorm_part2_rv_BOUNDEDSET-1 rmsnorm_part2_rv_BOUNDEDSET-2 rmsnorm_part2_rv_BOUNDEDSET-3 ss weight_BOUNDEDSET-len weight_BOUNDEDSET-0 weight_BOUNDEDSET-1 weight_BOUNDEDSET-2 weight_BOUNDEDSET-3)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
