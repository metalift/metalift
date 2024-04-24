#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 ) ) ) ))

(define-grammar (fir_small_inv0_gram NTAPS coefficient i input sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i NTAPS ) ) (equal? sum (reduce_sum (vec_elemwise_mul (v0) (v0) )) ) ))]
[v0 (choose (list-take-noerr input i ) (list-take-noerr coefficient i ))]
)

(define-grammar (fir_small_ps_gram NTAPS input coefficient fir_small_rv)
 [rv (choose (equal? fir_small_rv (reduce_sum (vec_elemwise_mul (v0) (v0) )) ))]
[v0 (choose (list-take-noerr input NTAPS ) (list-take-noerr coefficient NTAPS ))]
)

(define (fir_small_inv0 NTAPS coefficient i input sum) (fir_small_inv0_gram NTAPS coefficient i input sum #:depth 10))
(define (fir_small_ps NTAPS input coefficient fir_small_rv) (fir_small_ps_gram NTAPS input coefficient fir_small_rv #:depth 10))

(define-symbolic NTAPS integer?)
(define-symbolic coefficient_BOUNDEDSET-len integer?)
(define-symbolic coefficient_BOUNDEDSET-0 integer?)
(define-symbolic coefficient_BOUNDEDSET-1 integer?)
(define-symbolic coefficient_BOUNDEDSET-2 integer?)
(define-symbolic coefficient_BOUNDEDSET-3 integer?)
(define coefficient (take (list coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 coefficient_BOUNDEDSET-2 coefficient_BOUNDEDSET-3) coefficient_BOUNDEDSET-len))
(define-symbolic fir_small_rv integer?)
(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define-symbolic input_BOUNDEDSET-2 integer?)
(define-symbolic input_BOUNDEDSET-3 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3) input_BOUNDEDSET-len))
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= NTAPS 1 ) (>= (length input ) NTAPS ) ) (>= (length coefficient ) NTAPS ) ) (fir_small_inv0 NTAPS coefficient 0 input 0) ) (=> (&& (&& (&& (&& (< i NTAPS ) (>= NTAPS 1 ) ) (>= (length input ) NTAPS ) ) (>= (length coefficient ) NTAPS ) ) (fir_small_inv0 NTAPS coefficient i input sum) ) (fir_small_inv0 NTAPS coefficient (+ i 1 ) input (+ sum (* (list-ref-noerr input i ) (list-ref-noerr coefficient i ) ) )) ) ) (=> (&& (&& (&& (&& (! (< i NTAPS ) ) (>= NTAPS 1 ) ) (>= (length input ) NTAPS ) ) (>= (length coefficient ) NTAPS ) ) (fir_small_inv0 NTAPS coefficient i input sum) ) (fir_small_ps NTAPS input coefficient sum) ) )))


    (define sol0
        (synthesize
            #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 coefficient_BOUNDEDSET-2 coefficient_BOUNDEDSET-3 fir_small_rv i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 input_BOUNDEDSET-2 input_BOUNDEDSET-3 sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
