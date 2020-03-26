#lang rosette

; contains the correct invariant and post condition for simple_loop

(require rosette/lib/synthax)

(define-symbolic sum_1 integer?)
(define-symbolic n integer?)
(define-symbolic end integer?)
(define-symbolic i_0 integer?)
(define-symbolic rv integer?)
(define-symbolic sum integer?)
(define-symbolic i integer?)

(define-symbolic my_sum (~> integer? integer?))
(assert (forall (list end)

(begin (if (> end 0)
           (begin (eq? (my_sum end) (+ 1 (my_sum (- end 1)))))
           (begin (eq? (my_sum end) 0))))))


(define-symbolic vctest_ps (~> integer? integer? integer? integer? boolean?))
(assert (forall (list n sum i rv)
(begin    
  (eq? (vctest_ps n sum i rv) (if (<= 0 n)
                                  (and (eq? sum (my_sum n)) (eq? sum rv))
                                  (and (eq? sum 0) (eq? sum rv)))))))

; this also works
;(define (vctest_ps n sum i rv)
;  (if (<= 0 n)
;      (and (eq? sum (my_sum n) (eq? sum rv))
;      (and (eq? sum 0) (eq? sum rv)))


(define (inv_0 n sum i)
  (if (and (<= n i) (<= n 0))
      (eq? sum 0)
      (and (>= i 0) (<= i n) (eq? sum (my_sum i))))
)


(assert (not (forall (list sum_1 n i_0)
  (and
   (inv_0 n 0 0)

   (or (not (and (inv_0 n sum_1 i_0) (< i_0 n))) (inv_0 n (+ sum_1 1) (+ i_0 1)))
   
   (or (not (and (inv_0 n sum_1 i_0) (not (< i_0 n)))) (vctest_ps n sum_1 i_0 sum_1))

    ))))

(solve (void))