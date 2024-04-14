#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(require rosette/solver/smt/bitwuzla)
(current-solver (bitwuzla #:path "/Users/sahilbhatia/Documents/bitwuzla/build/src/main/bitwuzla" #:options (hash ':seed 0)))


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

(define-grammar (dot_inv0_gram a b i n sum)
 [rv (choose (&& (&& (>= i 0 ) (<= i n ) ) (equal? sum (v0) ) ))]
[v0 (choose (reduce_sum (v1)) (reduce_mul (v1)) (reduce_max (v1)))]
[v1 (choose (v2) (v7))]
[v2 (choose (vec-slice-noerr (v3) (v4) (v4) ))]
[v3 (choose a b)]
[v4 (choose (v5) (v6))]
[v5 (choose 0 n i)]
[v6 (choose (integer-sqrt-noerr (v5) ) (integer-exp-noerr (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v7 (choose (v8) (vec_elemwise_add (v2) (v2) ) (vec_elemwise_sub (v2) (v2) ) (vec_elemwise_mul (v2) (v2) ) (vec_elemwise_div (v2) (v2) ) (vec_scalar_add (v5) (v2) ) (vec_scalar_sub (v5) (v2) ) (vec_scalar_mul (v5) (v2) ) (vec_scalar_div (v5) (v2) ) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v8 (choose (vec_map (v2) map_int_to_int ))]
)

(define-grammar (dot_ps_gram a b n dot_rv)
 [rv (choose (equal? dot_rv (v0) ))]
[v0 (choose (reduce_sum (v1)) (reduce_mul (v1)) (reduce_max (v1)))]
[v1 (choose (v2) (v7))]
[v2 (choose (vec-slice-noerr (v3) (v4) (v4) ))]
[v3 (choose a b)]
[v4 (choose (v5) (v6))]
[v5 (choose 0 n)]
[v6 (choose (integer-sqrt-noerr (v5) ) (integer-exp-noerr (v5) ) (+ (v5) (v5) ) (- (v5) (v5) ) (* (v5) (v5) ) (quotient-noerr (v5) (v5) ))]
[v7 (choose (v8) (vec_elemwise_add (v2) (v2) ) (vec_elemwise_sub (v2) (v2) ) (vec_elemwise_mul (v2) (v2) ) (vec_elemwise_div (v2) (v2) ) (vec_scalar_add (v5) (v2) ) (vec_scalar_sub (v5) (v2) ) (vec_scalar_mul (v5) (v2) ) (vec_scalar_div (v5) (v2) ) (scalar_vec_sub (v5) (v2)) (scalar_vec_div (v5) (v2)))]
[v8 (choose (vec_map (v2) map_int_to_int ))]
)

(define-grammar (map_int_to_int_gram int_x)
 [rv (choose (v0))]
[v0 (choose (integer-exp-noerr int_x ) (integer-sqrt-noerr int_x ))]
)

(define (dot_inv0 a b i n sum) (dot_inv0_gram a b i n sum #:depth 10))
(define (dot_ps a b n dot_rv) (dot_ps_gram a b n dot_rv #:depth 10))

(define (map_int_to_int int_x) (map_int_to_int_gram int_x #:depth 10))

(define-symbolic a_BOUNDEDSET-len integer?)
(define-symbolic a_BOUNDEDSET-0 integer?)
(define-symbolic a_BOUNDEDSET-1 integer?)
(define a (take (list a_BOUNDEDSET-0 a_BOUNDEDSET-1) a_BOUNDEDSET-len))
(define-symbolic b_BOUNDEDSET-len integer?)
(define-symbolic b_BOUNDEDSET-0 integer?)
(define-symbolic b_BOUNDEDSET-1 integer?)
(define b (take (list b_BOUNDEDSET-0 b_BOUNDEDSET-1) b_BOUNDEDSET-len))
(define-symbolic dot_rv integer?)
(define-symbolic i integer?)
(define-symbolic n integer?)
(define-symbolic sum integer?)
(current-bitwidth 6)
(define (assertions)
 (assert (&& (&& (=> (&& (&& (&& (&& (>= n 1 ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (> (length b ) 0 ) ) (>= (length b ) n ) ) (dot_inv0 a b 0 n 0) ) (=> (&& (&& (&& (&& (&& (&& (< i n ) (>= n 1 ) ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (> (length b ) 0 ) ) (>= (length b ) n ) ) (dot_inv0 a b i n sum) ) (dot_inv0 a b (+ i 1 ) n (+ sum (* (list-ref-noerr a i ) (list-ref-noerr b i ) ) )) ) ) (=> (&& (&& (&& (&& (&& (&& (! (< i n ) ) (>= n 1 ) ) (> (length a ) 0 ) ) (>= (length a ) n ) ) (> (length b ) 0 ) ) (>= (length b ) n ) ) (dot_inv0 a b i n sum) ) (dot_ps a b n sum) ) )))


    (define sol0
        (synthesize
            #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
            #:guarantee (assertions)
        )
    )
    (sat? sol0)
    (print-forms sol0)


        (define sol1
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0)))))
                    (assertions)
                )
            )
        )
        (sat? sol1)
        (print-forms sol1)


        (define sol2
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1)))))
                    (assertions)
                )
            )
        )
        (sat? sol2)
        (print-forms sol2)


        (define sol3
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2)))))
                    (assertions)
                )
            )
        )
        (sat? sol3)
        (print-forms sol3)


        (define sol4
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol3))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol3)))))
                    (assertions)
                )
            )
        )
        (sat? sol4)
        (print-forms sol4)


        (define sol5
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol3))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol3))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol4))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol4)))))
                    (assertions)
                )
            )
        )
        (sat? sol5)
        (print-forms sol5)


        (define sol6
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol3))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol3))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol4))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol4))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol5))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol5)))))
                    (assertions)
                )
            )
        )
        (sat? sol6)
        (print-forms sol6)


        (define sol7
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol3))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol3))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol4))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol4))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol5))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol5))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol6))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol6)))))
                    (assertions)
                )
            )
        )
        (sat? sol7)
        (print-forms sol7)


        (define sol8
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol3))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol3))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol4))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol4))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol5))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol5))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol6))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol6))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol7))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol7)))))
                    (assertions)
                )
            )
        )
        (sat? sol8)
        (print-forms sol8)


        (define sol9
            (synthesize
                #:forall (list a_BOUNDEDSET-len a_BOUNDEDSET-0 a_BOUNDEDSET-1 b_BOUNDEDSET-len b_BOUNDEDSET-0 b_BOUNDEDSET-1 dot_rv i n sum)
                #:guarantee (begin
                    (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol0))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol0))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol1))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol1))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol2))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol2))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol3))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol3))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol4))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol4))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol5))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol5))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol6))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol6))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol7))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol7))))) (assume (|| (! (eq? (dot_inv0 a b i n sum) (evaluate (dot_inv0 a b i n sum) sol8))) (! (eq? (dot_ps a b n dot_rv) (evaluate (dot_ps a b n dot_rv) sol8)))))
                    (assertions)
                )
            )
        )
        (sat? sol9)
        (print-forms sol9)
