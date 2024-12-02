#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


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


 (define-bounded (reduce_max x)
(if (<= (length x ) 1 ) (list-ref-noerr x 0 ) (if (> (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) (list-ref-noerr x 0 ) (reduce_max (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_sum x)
(if (< (length x ) 1 ) 0 (+ (list-ref-noerr x 0 ) (reduce_sum (list-tail-noerr x 1 )) ) ))


 (define-bounded (reduce_mul x)
(if (< (length x ) 1 ) 1 (* (list-ref-noerr x 0 ) (reduce_mul (list-tail-noerr x 1 )) ) ))


 (define-bounded (vec_map x map_int_to_int)
(if (< (length x ) 1 ) (list-empty ) (list-prepend (map_int_to_int (list-ref-noerr x 0 )) (vec_map (list-tail-noerr x 1 ) map_int_to_int ) ) ))


 (define (vec_slice lst start end)
(list-tail-noerr (list-take-noerr lst end ) start ))

(define-grammar (lmsfir1_inv0_gram NTAPS coefficient i input sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i NTAPS ) ) (equal? sum (v0) ) ))]
[v0 (choose (reduce_sum (v1)) (reduce_mul (v1)) (reduce_max (v1)))]
[v1 (choose (v2) (v7))]
[v2 (choose (vec-slice-noerr (v3) (v4) (v4) ))]
[v3 (choose input coefficient)]
[v4 (choose (v5) (v6))]
[v5 (choose 0 NTAPS i)]
[v6 (choose (integer-sqrt-noerr (v5) ) (integer-exp-noerr (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v7 (choose (v8) (vec_elemwise_add (v2) (v2) ) (vec_elemwise_sub (v2) (v2) ) (vec_elemwise_mul (v2) (v2) ) (vec_elemwise_div (v2) (v2) ) (vec_scalar_add (v5) (v2) ) (vec_scalar_sub (v5) (v2) ) (vec_scalar_mul (v5) (v2) ) (vec_scalar_div (v5) (v2) ) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v8 (choose (vec_map (v2) map_int_to_int ))]
)

(define-grammar (lmsfir1_ps_gram NTAPS input coefficient lmsfir1_rv)
 [rv (choose (equal? lmsfir1_rv (v0) ))]
[v0 (choose (reduce_sum (v1)) (reduce_mul (v1)) (reduce_max (v1)))]
[v1 (choose (v2) (v7))]
[v2 (choose (vec-slice-noerr (v3) (v4) (v4) ))]
[v3 (choose input coefficient)]
[v4 (choose (v5) (v6))]
[v5 (choose 0 NTAPS)]
[v6 (choose (integer-sqrt-noerr (v5) ) (integer-exp-noerr (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v7 (choose (v8) (vec_elemwise_add (v2) (v2) ) (vec_elemwise_sub (v2) (v2) ) (vec_elemwise_mul (v2) (v2) ) (vec_elemwise_div (v2) (v2) ) (vec_scalar_add (v5) (v2) ) (vec_scalar_sub (v5) (v2) ) (vec_scalar_mul (v5) (v2) ) (vec_scalar_div (v5) (v2) ) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v8 (choose (vec_map (v2) map_int_to_int ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (lmsfir1_inv0 NTAPS coefficient i input sum) (lmsfir1_inv0_gram NTAPS coefficient i input sum #:depth 10))
(define (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (lmsfir1_ps_gram NTAPS input coefficient lmsfir1_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic NTAPS integer?)
(define-symbolic coefficient_BOUNDEDSET-len integer?)
(define-symbolic coefficient_BOUNDEDSET-0 integer?)
(define-symbolic coefficient_BOUNDEDSET-1 integer?)
(define coefficient (take (list coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1) coefficient_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic input_BOUNDEDSET-len integer?)
(define-symbolic input_BOUNDEDSET-0 integer?)
(define-symbolic input_BOUNDEDSET-1 integer?)
(define input (take (list input_BOUNDEDSET-0 input_BOUNDEDSET-1) input_BOUNDEDSET-len))
(define-symbolic lmsfir1_rv integer?)
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (>= NTAPS 1 ) (>= (length input ) NTAPS ) ) (>= (length coefficient ) NTAPS ) ) (lmsfir1_inv0 NTAPS coefficient 0 input 0) ) (=> (&& (&& (&& (&& (< i NTAPS ) (>= NTAPS 1 ) ) (>= (length input ) NTAPS ) ) (>= (length coefficient ) NTAPS ) ) (lmsfir1_inv0 NTAPS coefficient i input sum) ) (lmsfir1_inv0 NTAPS coefficient (+ i 1 ) input (+ sum (* (list-ref-noerr input i ) (list-ref-noerr coefficient i ) ) )) ) ) (=> (&& (&& (&& (&& (! (< i NTAPS ) ) (>= NTAPS 1 ) ) (>= (length input ) NTAPS ) ) (>= (length coefficient ) NTAPS ) ) (lmsfir1_inv0 NTAPS coefficient i input sum) ) (lmsfir1_ps NTAPS input coefficient sum) ) )))


    (define sol0
        (synthesize
            #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)


        (define sol1
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0)))))
                    (assertions)
                )
            )
        )
        (sat? sol1)
        (print-forms sol1)


        (define sol2
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1)))))
                    (assertions)
                )
            )
        )
        (sat? sol2)
        (print-forms sol2)


        (define sol3
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2)))))
                    (assertions)
                )
            )
        )
        (sat? sol3)
        (print-forms sol3)


        (define sol4
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol3))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol3)))))
                    (assertions)
                )
            )
        )
        (sat? sol4)
        (print-forms sol4)


        (define sol5
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol3))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol3))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol4))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol4)))))
                    (assertions)
                )
            )
        )
        (sat? sol5)
        (print-forms sol5)


        (define sol6
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol3))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol3))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol4))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol4))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol5))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol5)))))
                    (assertions)
                )
            )
        )
        (sat? sol6)
        (print-forms sol6)


        (define sol7
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol3))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol3))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol4))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol4))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol5))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol5))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol6))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol6)))))
                    (assertions)
                )
            )
        )
        (sat? sol7)
        (print-forms sol7)


        (define sol8
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol3))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol3))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol4))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol4))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol5))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol5))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol6))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol6))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol7))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol7)))))
                    (assertions)
                )
            )
        )
        (sat? sol8)
        (print-forms sol8)


        (define sol9
            (synthesize
                #:forall (list NTAPS coefficient_BOUNDEDSET-len coefficient_BOUNDEDSET-0 coefficient_BOUNDEDSET-1 i input_BOUNDEDSET-len input_BOUNDEDSET-0 input_BOUNDEDSET-1 lmsfir1_rv sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol0))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol0))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol1))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol1))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol2))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol2))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol3))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol3))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol4))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol4))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol5))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol5))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol6))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol6))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol7))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol7))))) (assume (|| (! (eq? (lmsfir1_inv0 NTAPS coefficient i input sum) (evaluate (lmsfir1_inv0 NTAPS coefficient i input sum) sol8))) (! (eq? (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) (evaluate (lmsfir1_ps NTAPS input coefficient lmsfir1_rv) sol8)))))
                    (assertions)
                )
            )
        )
        (sat? sol9)
        (print-forms sol9)
