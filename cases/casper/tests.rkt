#lang metalift

(define (sum data)
  ; Right now ML expects the output variable to be explicitly named
  (-> (listof integer?) (val integer?))

  ; out = 0
  (set! val 0)

  ; i=0
  (define i integer? 0)

  ; Add all values in data to sum
  (while (< i (length data))
         (set! val (+ val (list-ref data i)))
         (set! i (+ i 1))
         )

  ; Returning the output variable is implict
  )

; Test code
(define size integer? 10)

; for/list is currently not supported inside code to be lifted, but works for driver code like below
(define data (listof integer?) (for/list ([i size])  (random 100)))

;(sum data)
;(apply + data)