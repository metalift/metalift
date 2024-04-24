#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))



 (define-bounded (vec_elemwise_add x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))


 (define-bounded (vec_elemwise_mul x y)
(if (or (< (length x ) 1 ) (! (equal? (length x ) (length y ) ) ) ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vec_elemwise_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) ))

(define-grammar (n_real_updates_inv0_gram A B C N agg.result curr i)
 [rv (choose (&& (&& (>= i 0 ) (<= i N ) ) (equal? agg.result (vec_elemwise_add (v0) (vec_elemwise_mul (v0) (v0))) ) ))]
[v0 (choose (list-take-noerr A i ) (list-take-noerr B i ) (list-take-noerr C i ))]
)

(define-grammar (n_real_updates_ps_gram N A B C n_real_updates_rv)
 [rv (choose (equal? n_real_updates_rv (vec_elemwise_add (vec_elemwise_mul (v0) (v0)) (v0)) ))]
[v0 (choose (list-take-noerr A N ) (list-take-noerr B N ) (list-take-noerr C N ))]
)

(define (n_real_updates_inv0 A B C N agg.result curr i) (n_real_updates_inv0_gram A B C N agg.result curr i #:depth 10))
(define (n_real_updates_ps N A B C n_real_updates_rv) (n_real_updates_ps_gram N A B C n_real_updates_rv #:depth 10))

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
