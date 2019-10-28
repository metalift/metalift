#lang metalift

(define (blur-1x3 in width height)
  ; right now ML expects the output variable to be explicitly named
  (-> (listof (listof integer?)) integer? integer? (out (listof (listof integer?))))

  ; out = [ [0,0,0], [0,0,0], [0,0,0] ]
  (set! out (list (list 0 0 0) (list 0 0 0) (list 0 0 0)))
  (define i integer? 0)

  (ml-while (< i width)
          (define j integer? 0)
          (ml-while (< j height)
                  ; v1 = in[i][j]
                  (define v1 integer? (list-ref (list-ref in i) j))
                  (define v2 integer? 0)
                  (define v3 integer? 0)

                  ; v2 = in[i][j+1] if within bounds
                  (if (< (+ j 1) height)
                      (set! v2 (list-ref (list-ref in i) (+ j 1)))
                      (set! v2 0))

                  ; v3 = in[i][j-1] if within bounds
                  (if (>= (- j 1) 0)
                      (set! v3 (list-ref (list-ref in i) (- j 1)))
                      (set! v3 0))

                  ; out[i][j] = (v1+v2+v3)/3
                  (set! out (list-set out i (list-set (list-ref out i) j  (/ (+ (+ v1 v2) v3) 3.0))))
                  
                  (set! j (+ j 1))
                  )
          (set! i (+ i 1))
          )

  ; returning the output variable is implict
)

; test code below
(define width integer? 3)
(define height integer? 3)

; in = [ [1,1,1], [1,1,1], [1,1,1] ]
; for/list is currently not supported inside code to be lifted, but works for driver code like below
(define in (listof (listof integer?)) (for/list ([x width]) (for/list ([y height]) 1)))

(blur-1x3 in 3 3)