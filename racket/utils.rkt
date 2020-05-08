#lang racket

(define (randlist n mx)
  (for/list ((i n))
    (random mx)))

(define (genlist n)
  (for/list ([i n])
    (randlist i 100)))

(provide genlist randlist)
