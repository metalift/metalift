#lang racket
(define (list-ref-noerr l i)
  (if (and  (>= i 0) (< i (length l))) (list-ref l i)
      0))

(define (tupleGet t i)
  (list-ref-noerr t i))

(define (supportedCommand supported_synthState supported_arg_0 supported_arg_1)
(and
  (not
    (< supported_arg_1 (tupleGet (tupleGet supported_synthState 0) 0))
  ) ; clock must not be before max time in state
  (or
    (>
      supported_arg_1
      (tupleGet (tupleGet supported_synthState 0) 0)
    ) ; either we are causally after and can do anything or
    ; we are concurrent
    (if (= supported_arg_0 1) ; we are enabling
      true
      (equal? false (tupleGet (tupleGet supported_synthState 0) 1)) ; we are disabling and must not have enabled
    )
  )
))

(supportedCommand (list (list 2 #t) #f) 0 2)