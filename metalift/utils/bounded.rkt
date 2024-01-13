#lang rosette
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)
(provide (all-defined-out))
(define fuel (make-parameter 64))

(define-syntax-rule
  (define-bounded (id param ...) body ...)
  (define (id param ...)
    (assert (> (fuel) 0) "Out of fuel.")
    (parameterize ([fuel (sub1 (fuel))])
      body ...)))
