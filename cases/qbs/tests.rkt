#lang metalift

; select-*-test-ret-val = select * from in
(define (select-*-test in) (-> (listof integer?) (listof integer?))
  
  (define i integer? 0) ; int i = 0;  

  ; XXX using special variable name to indicate return value
  (define select-*-test-ret-val (listof integer?) (empty integer?)) ; List<Int> select-*-test-ret-val = new ArrayList();

  ; same as select * from in
  (ml-for (< i (length in))
          (set! select-*-test-ret-val (ml-append select-*-test-ret-val (list-ref in i)))
          ; select-*-test-ret-val = concat(select-*-test-ret-val, in[i]);
          (set! i (+ i 1)))   
  
  select-*-test-ret-val
  )