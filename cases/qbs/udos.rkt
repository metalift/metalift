#lang metalift

(define-udo (my-select-* in)
  (-> (listof integer?) (listof integer?))

  (if (= (length in) 0) (empty (listof integer?))
         (cons (list-ref in 0) (my-select-* (list-tail in 1)))))

; if (in.length == 0) return []
; else return concat(in[0], select-*(tail(in, 1)));

;(axiom (= (my-select-* (my-select-* in f1) f2)
;          (my-select-* (my-select-* in f2) f1)))

(provide my-select-*)