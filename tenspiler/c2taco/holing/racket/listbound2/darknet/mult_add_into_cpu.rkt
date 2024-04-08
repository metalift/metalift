#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (mult_add_into_cpu_inv0_gram N X Y Z agg.result i ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i N ) ) (equal? agg.result (vec_elemwise_add (v0) (vec_elemwise_mul (v0) (v0))) ) ))]
[v0 (choose (list-take-noerr X i ) (list-take-noerr Y i ) (list-take-noerr Z i ))]
)

(define-grammar (mult_add_into_cpu_ps_gram N X Y Z mult_add_into_cpu_rv)
 [rv (choose (equal? mult_add_into_cpu_rv (vec_elemwise_add (v0) (vec_elemwise_mul (v0) (v0))) ))]
[v0 (choose (list-take-noerr X N ) (list-take-noerr Y N ) (list-take-noerr Z N ))]
)

(define (mult_add_into_cpu_inv0 N X Y Z agg.result i ref.tmp) (mult_add_into_cpu_inv0_gram N X Y Z agg.result i ref.tmp #:depth 10))
(define (mult_add_into_cpu_ps N X Y Z mult_add_into_cpu_rv) (mult_add_into_cpu_ps_gram N X Y Z mult_add_into_cpu_rv #:depth 10))

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
