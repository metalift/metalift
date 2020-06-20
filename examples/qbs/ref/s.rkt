#lang rosette
(require (file "/Users/akcheung/proj/metalift/racket/utils.rkt"))
(require rosette/lib/synthax)



(define (Select data f) 
(begin (if (eq? (length data) 0) (begin (list )) (begin (if (f (list-ref data 0)) (begin (append (list (list-ref data 0)) (Select (list-tail data 1) f))) (begin (Select (list-tail data 1) f)))))))

(define (input_ps l rv i out) 
(begin (eq? out (Select l select_p))))

(define (inv_0 l i out) 
(begin (and (>= i 0) (<= i (length l)) (eq? (append out (Select (list-tail l i) select_p)) (Select l select_p)))))

(define (select_p n) 
(begin (eq? n 2)))


(define binding
  (solve (for ([l (genlist 4)] [i_0 (range 4)] [out_1 (genlist 4)]) 
           (and (assert (inv_0 l 0 (list ))) (assert (or (not (and (inv_0 l i_0 out_1) (< i_0 (length l)))) (inv_0 l (+ i_0 1) (if (eq? (list-ref l i_0) 2) (append out_1 (list (list-ref l i_0))) out_1)))) (assert (or (not (and (inv_0 l i_0 out_1) (not (< i_0 (length l))))) (input_ps l out_1 i_0 out_1)))))))
binding