#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (scalar_vec_div a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (quotient-noerr a (list-ref-noerr x 0 ) ) (scalar_vec_div a (list-tail-noerr x 1 )) ) ))

(define-grammar (vrecip_inv0_gram agg.result arr i n ref.tmp)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (scalar_vec_div 1 (v0)) ) ))]
[v0 (choose (list-take-noerr arr i ))]
)

(define-grammar (vrecip_ps_gram arr n vrecip_rv)
 [rv (choose (equal? vrecip_rv (scalar_vec_div 1 (v0)) ))]
[v0 (choose (list-take-noerr arr n ))]
)

(define (vrecip_inv0 agg.result arr i n ref.tmp) (vrecip_inv0_gram agg.result arr i n ref.tmp #:depth 10))
(define (vrecip_ps arr n vrecip_rv) (vrecip_ps_gram arr n vrecip_rv #:depth 10))

(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic arr_BOUNDEDSET-len integer?)
(define-symbolic arr_BOUNDEDSET-0 integer?)
(define-symbolic arr_BOUNDEDSET-1 integer?)
(define arr (take (list arr_BOUNDEDSET-0 arr_BOUNDEDSET-1) arr_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic vrecip_rv_BOUNDEDSET-len integer?)
(define-symbolic vrecip_rv_BOUNDEDSET-0 integer?)
(define-symbolic vrecip_rv_BOUNDEDSET-1 integer?)
(define vrecip_rv (take (list vrecip_rv_BOUNDEDSET-0 vrecip_rv_BOUNDEDSET-1) vrecip_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length arr ) n ) ) (vrecip_inv0 (list-empty ) arr 0 n 0) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length arr ) n ) ) (vrecip_inv0 agg.result arr i n ref.tmp) ) (vrecip_inv0 (list-append agg.result (quotient-noerr 1 (list-ref-noerr arr i ) ) ) arr (+ i 1 ) n (quotient-noerr 1 (list-ref-noerr arr i ) )) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (vrecip_inv0 agg.result arr i n ref.tmp) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (vrecip_inv0 agg.result arr i n ref.tmp) ) ) (vrecip_ps arr n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 arr_BOUNDEDSET-len arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 i n ref.tmp vrecip_rv_BOUNDEDSET-len vrecip_rv_BOUNDEDSET-0 vrecip_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
