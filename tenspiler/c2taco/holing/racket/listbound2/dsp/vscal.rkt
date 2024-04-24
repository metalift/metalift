#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_scalar_mul a x)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (vec_scalar_mul a (list-tail-noerr x 1 )) ) ))

(define-grammar (vscal_inv0_gram agg.result arr i n ref.tmp v)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? agg.result (vec_scalar_mul (v0) (v1)) ) ))]
[v0 (choose v)]
[v1 (choose (list-take-noerr arr i ))]
)

(define-grammar (vscal_ps_gram arr v n vscal_rv)
 [rv (choose (equal? vscal_rv (vec_scalar_mul (v0) (v1)) ))]
[v0 (choose v)]
[v1 (choose (list-take-noerr arr n ))]
)

(define (vscal_inv0 agg.result arr i n ref.tmp v) (vscal_inv0_gram agg.result arr i n ref.tmp v #:depth 10))
(define (vscal_ps arr v n vscal_rv) (vscal_ps_gram arr v n vscal_rv #:depth 10))

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
(define-symbolic v integer?)
(define-symbolic vscal_rv_BOUNDEDSET-len integer?)
(define-symbolic vscal_rv_BOUNDEDSET-0 integer?)
(define-symbolic vscal_rv_BOUNDEDSET-1 integer?)
(define vscal_rv (take (list vscal_rv_BOUNDEDSET-0 vscal_rv_BOUNDEDSET-1) vscal_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (>= n 1 ) (>= (length arr ) n ) ) (vscal_inv0 (list-empty ) arr 0 n 0 v) ) (=> (&& (&& (&& (< i n ) (>= n 1 ) ) (>= (length arr ) n ) ) (vscal_inv0 agg.result arr i n ref.tmp v) ) (vscal_inv0 (list-append agg.result (* v (list-ref-noerr arr i ) ) ) arr (+ i 1 ) n (* v (list-ref-noerr arr i ) ) v) ) ) (=> (or (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (vscal_inv0 agg.result arr i n ref.tmp v) ) (&& (&& (&& (&& (! true ) (! (< i n ) ) ) (>= n 1 ) ) (>= (length arr ) n ) ) (vscal_inv0 agg.result arr i n ref.tmp v) ) ) (vscal_ps arr v n agg.result) ) )))


    (define sol0
        (synthesize
            #:forall (list agg.result_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 arr_BOUNDEDSET-len arr_BOUNDEDSET-0 arr_BOUNDEDSET-1 i n ref.tmp v vscal_rv_BOUNDEDSET-len vscal_rv_BOUNDEDSET-0 vscal_rv_BOUNDEDSET-1)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)
