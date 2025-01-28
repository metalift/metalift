#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))

(define-grammar (rmsnorm_part1_inv0_gram i input ss weight)
 [rv (choose (&& (&& (>= i 0 ) (<= i (length input ) ) ) (equal? ss (reduce_sum (vec_elemwise_mul (v0) (v0))) ) ))]
[v0 (choose (list-take-noerr input i ) (list-take-noerr weight i ))]
)

(define-grammar (rmsnorm_part1_ps_gram input weight rmsnorm_part1_rv)
 [rv (choose (equal? rmsnorm_part1_rv (reduce_sum (vec_elemwise_mul (v0) (v0))) ))]
[v0 (choose input weight)]
)

(define (rmsnorm_part1_inv0 i input ss weight) (rmsnorm_part1_inv0_gram i input ss weight #:depth 10))
(define (rmsnorm_part1_ps input weight rmsnorm_part1_rv) (rmsnorm_part1_ps_gram input weight rmsnorm_part1_rv #:depth 10))

(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define-symbolic input_BOUNDEDSET-2 integer?)
(define-symbolic input_BOUNDEDSET-3 integer?)
(define-symbolic input_BOUNDEDSET-4 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3 input_BOUNDEDSET-4) input_BOUNDEDSET-len))
(define-symbolic rmsnorm_part1_rv integer?)
(define-symbolic ss integer?)
(define-symbolic weight_BOUNDEDSET-len integer?)
(define-symbolic weight_BOUNDEDSET-0 integer?)
(define-symbolic weight_BOUNDEDSET-1 integer?)
(define-symbolic weight_BOUNDEDSET-2 integer?)
(define-symbolic weight_BOUNDEDSET-3 integer?)
(define-symbolic weight_BOUNDEDSET-4 integer?)
(define weight (take (list weight_BOUNDEDSET-0 weight_BOUNDEDSET-1 weight_BOUNDEDSET-2 weight_BOUNDEDSET-3 weight_BOUNDEDSET-4) weight_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (equal? (length input ) (length weight ) ) (> (length input ) 0 ) ) (rmsnorm_part1_inv0 0 input 0 weight) ) (=> (&& (&& (&& (< i (length input ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part1_inv0 i input ss weight) ) (rmsnorm_part1_inv0 (+ i 1 ) input (+ ss (* (list-ref-noerr input i ) (list-ref-noerr input i ) ) ) weight) ) ) (=> (&& (&& (&& (! (< i (length input ) ) ) (equal? (length input ) (length weight ) ) ) (> (length input ) 0 ) ) (rmsnorm_part1_inv0 i input ss weight) ) (rmsnorm_part1_ps input weight ss) ) )))


    (define sol0
        (synthesize
            #:forall (list i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3 input_BOUNDEDSET-4 rmsnorm_part1_rv ss weight_BOUNDEDSET-len weight_BOUNDEDSET-0 weight_BOUNDEDSET-1 weight_BOUNDEDSET-2 weight_BOUNDEDSET-3 weight_BOUNDEDSET-4)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
