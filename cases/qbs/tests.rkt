#lang metalift

; out = select * from in
; name of the return variable is explicitly stated in the function type declaration
; return variable is automatically returned at the end of the program, no need to explicitly return it
(define (select-*-test in) (-> (listof integer?) (out (listof integer?)))
  
  (define i integer? 0) ; int i = 0;  

  (set! out (empty integer?)) ; List<Int> out = new ArrayList();

  ; same as select * from in
  (ml-for (< i (length in))
          (set! out (ml-append out (list-ref in i)))
          ; out = concat(out, in[i]);
          (set! i (+ i 1))) 
)

; example run
; (select-*-test (list 1 2 3))  ==> (list 1 2 3)

(define (select-test in) (-> (listof integer?) (out (listof integer?)))

  (define i integer? 0) ; int i = 0;  

  (set! out (empty integer?))

  ; same as select * from in where in = 42
  (ml-for (< i (length in))
          (if (= (list-ref in i) 42)
              (set! out (ml-append out (list-ref in i)))
              (set! out out)) ; racket 'if' must have both clauses
          (set! i (+ i 1)))   
)

; example run
; (select-* (list 1 2 42))  ==> (list 42)