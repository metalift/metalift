#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


 (define-bounded (vec_scalar_add a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ a (list-ref-noerr x 0 ) ) (vec_scalar_add a (list-tail-noerr x 1 ) ) ) ))

(define-grammar (array_inc_inv0_gram agg.result arr i n ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_scalar_add 1 (v0) ) ) ))]
[v0 (choose (list-take-noerr arr i ))]
)

(define-grammar (array_inc_ps_gram arr n array_inc_rv)
 [rv (choose (equal? array_inc_rv (vec_scalar_add 1 (v0) ) ))]
[v0 (choose (list-take-noerr arr n ))]
)

(define (array_inc_inv0 agg.result arr i n ref.tmp) (array_inc_inv0_gram agg.result arr i n ref.tmp #:depth 10))
(define (array_inc_ps arr n array_inc_rv) (array_inc_ps_gram arr n array_inc_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-2 integer?)
(define-symbolic agg.result_BOUNDEDSET-3 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3) agg.result_BOUNDEDSET-len))
(define-symbolic arr_BOUNDEDSET-len integer?)
(define-symbolic arr_BOUNDEDSET-0 integer?)
(define-symbolic arr_BOUNDEDSET-1 integer?)
(define-symbolic arr_BOUNDEDSET-2 integer?)
(define-symbolic arr_BOUNDEDSET-3 integer?)
(define arr (take (list arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 arr_BOUNDEDSET-2 arr_BOUNDEDSET-3) arr_BOUNDEDSET-len))
(define-symbolic array_inc_rv_BOUNDEDSET-len integer?)
(define-symbolic array_inc_rv_BOUNDEDSET-0 integer?)
(define-symbolic array_inc_rv_BOUNDEDSET-1 integer?)
(define-symbolic array_inc_rv_BOUNDEDSET-2 integer?)
(define-symbolic array_inc_rv_BOUNDEDSET-3 integer?)
(define array_inc_rv (take (list array_inc_rv_BOUNDEDSET-0 array_inc_rv_BOUNDEDSET-1 array_inc_rv_BOUNDEDSET-2 array_inc_rv_BOUNDEDSET-3) array_inc_rv_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length arr ) n ) ) (array_inc_inv0 (list-empty ) arr 0 n 0) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length arr ) n ) ) (array_inc_inv0 agg.result arr i n ref.tmp) ) (array_inc_inv0 (list-append agg.result (+ (list-ref-noerr arr i ) 1 ) ) arr (+ i 1 ) n (+ (list-ref-noerr arr i ) 1 )) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (array_inc_inv0 agg.result arr i n ref.tmp) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (array_inc_inv0 agg.result arr i n ref.tmp) ) ) (array_inc_ps arr n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-2 agg.result_BOUNDEDSET-3 arr_BOUNDEDSET-len arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 arr_BOUNDEDSET-2 arr_BOUNDEDSET-3 array_inc_rv_BOUNDEDSET-len array_inc_rv_BOUNDEDSET-0 array_inc_rv_BOUNDEDSET-1 array_inc_rv_BOUNDEDSET-2 array_inc_rv_BOUNDEDSET-3 i n ref.tmp)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
