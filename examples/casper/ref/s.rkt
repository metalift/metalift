#lang rosette
(require (file "/Users/akcheung/proj/metalift/racket/utils.rkt"))
(require rosette/lib/synthax)
(define (choose0_fn e0 e1) 
  (cond 
   [(= choose0 0) e0]
   [(= choose0 1) e1]
   [else (assert false)]))

(define-symbolic choose0 integer?)

(define (mapper data f) 
(begin (if (eq? (length data) 0) (begin (list )) (begin (append (list (f (list-ref data 0))) (mapper (list-tail data 1) f))))))

(define (reducer data f init) 
(begin (if (eq? (length data) 0) (begin init) (begin (f (list-ref data 0) (reducer (list-tail data 1) f init))))))

(define (input_ps i sum l rv) 
(begin (and (eq? sum (reducer (mapper l lambda_mapper) lambda_reducer 0)) (eq? rv sum))))

(define (inv_0 i sum l) 
(begin (and (>= i 0) (<= i (length l)) (eq? (choose0_fn (+ i 1) sum) (reducer (mapper (take l i) lambda_mapper) lambda_reducer 0)))))

(define (lambda_mapper n) 
(begin (* n 2)))

(define (lambda_reducer v1 v2) 
(begin (+ v1 v2)))


(define binding
  (solve (for ([l (genlist 4)] [i_1 (range 4)] [sum_0 (range 4)]) 
           (and (assert (inv_0 0 0 l)) (assert (or (not (and (inv_0 i_1 sum_0 l) (< i_1 (length l)))) (inv_0 (+ i_1 1) (+ sum_0 (* (list-ref l i_1) 2)) l))) (assert (or (not (and (inv_0 i_1 sum_0 l) (not (< i_1 (length l))))) (input_ps i_1 sum_0 l sum_0)))))))
binding