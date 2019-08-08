#lang metalift

(define (select-*-test in) (-> (listof integer?) (listof integer?))
  
  (define i integer? 0) ; int i = 0;  

  ; XXX using special variable name to indicate return value
  (define select-*-test-ret-val (listof integer?) (empty integer?))

  ; same as select * from in
  (ml-for (< i (length in))
          (set! select-*-test-ret-val (ml-append select-*-test-ret-val (list-ref in i)))
          (set! i (+ i 1)))   
  
  select-*-test-ret-val
  )