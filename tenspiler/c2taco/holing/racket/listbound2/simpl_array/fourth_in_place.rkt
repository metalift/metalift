#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (fourth_in_place_inv0_gram agg.result arr fourth i n sq)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_elemwise_mul (v0) (v0)) ) ))]
[v0 (choose (list-take-noerr arr i ) (vec_elemwise_mul (list-take-noerr arr i ) (list-take-noerr arr i )))]
)

(define-grammar (fourth_in_place_ps_gram arr n fourth_in_place_rv)
 [rv (choose (equal? fourth_in_place_rv (vec_elemwise_mul (v0) (v0)) ))]
[v0 (choose (list-take-noerr arr n ) (vec_elemwise_mul (list-take-noerr arr n ) (list-take-noerr arr n )))]
)

(define (fourth_in_place_inv0 agg.result arr fourth i n sq) (fourth_in_place_inv0_gram agg.result arr fourth i n sq #:depth 10))
(define (fourth_in_place_ps arr n fourth_in_place_rv) (fourth_in_place_ps_gram arr n fourth_in_place_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic arr_BOUNDEDSET-len integer?)
(define-symbolic arr_BOUNDEDSET-0 integer?)
(define-symbolic arr_BOUNDEDSET-1 integer?)
(define arr (take (list arr_BOUNDEDSET-0 arr_BOUNDEDSET-1) arr_BOUNDEDSET-len))
(define-symbolic fourth integer?)
(define-symbolic fourth_in_place_rv_BOUNDEDSET-len integer?)
(define-symbolic fourth_in_place_rv_BOUNDEDSET-0 integer?)
(define-symbolic fourth_in_place_rv_BOUNDEDSET-1 integer?)
(define fourth_in_place_rv (take (list fourth_in_place_rv_BOUNDEDSET-0 fourth_in_place_rv_BOUNDEDSET-1) fourth_in_place_rv_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic sq integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length arr ) n ) ) (fourth_in_place_inv0 (list-empty ) arr 0 0 n 0) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length arr ) n ) ) (fourth_in_place_inv0 agg.result arr fourth i n sq) ) (fourth_in_place_inv0 (list-append agg.result (* (* (list-ref-noerr arr i ) (list-ref-noerr arr i ) ) (* (list-ref-noerr arr i ) (list-ref-noerr arr i ) ) ) ) arr (* (* (list-ref-noerr arr i ) (list-ref-noerr arr i ) ) (* (list-ref-noerr arr i ) (list-ref-noerr arr i ) ) ) (+ i 1 ) n (* (list-ref-noerr arr i ) (list-ref-noerr arr i ) )) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (fourth_in_place_inv0 agg.result arr fourth i n sq) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (fourth_in_place_inv0 agg.result arr fourth i n sq) ) ) (fourth_in_place_ps arr n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 arr_BOUNDEDSET-len arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 fourth fourth_in_place_rv_BOUNDEDSET-len fourth_in_place_rv_BOUNDEDSET-0 fourth_in_place_rv_BOUNDEDSET-1 i n sq)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
