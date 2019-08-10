#lang metalift

(define-udo (my-select-* in)
  (-> (listof integer?) (listof integer?))

  (if (= (length in) 0) (empty (listof integer?))
         (cons (list-ref in 0) (my-select-* (list-tail in 1)))))

; if (in.length == 0) return []
; else return concat(in[0], select-*(tail(in, 1)));

(define-axiom (v l) (-> integer? (listof integer?))
 (list-equal (my-select-* (ml-append l v))
             (ml-append (my-select-* l) v)))

(provide my-select-*)