#lang metalift

(define-udo (my-select-* in)
  (-> (listof integer?) (listof integer?))

  (if (= (length in) 0) (empty (listof integer?))
         (cons (list-ref in 0) (my-select-* (list-tail in 1)))))

; if (in.length == 0) return []
; else return concat(in[0], select-*(tail(in, 1)));


(define-axiom (v l) (integer? (listof integer?))
 (list-equal (my-select-* (ml-append l v))
             (ml-append (my-select-* l) v)))


;(define-udo (my-select in)
;  (-> (listof integer?) (listof integer?))
;
;  (if (= (length in) 0) (empty (listof integer?))
;      (if (= (list-ref in 0) 42)
;          (cons (list-ref in 0) (my-select (list-tail in 1)))
;          (my-select (list-tail in 1)))))
;
;(define-axiom (v l) (integer? (listof integer?))
;  (if (= v 42)
;      (list-equal (my-select (ml-append l v)) (ml-append (my-select l) v))
;      (list-equal (my-select (ml-append l v)) (my-select l))))

;(define-udo (my-select in pred)
;  (-> (listof integer?) (-> integer? boolean?) (listof integer?))
;
;  (if (= (length in) 0) (empty (listof integer?))
;      (if (pred (list-ref in 0))
;          (cons (list-ref in 0) (my-select (list-tail in 1) pred))
;          (my-select (list-tail in 1) pred))))
;
;(define-axiom (v l pred) (integer? (listof integer?) (-> integer? boolean?))
;  (if (= (pred v) #t)
;      (list-equal (my-select (ml-append l v) pred) (ml-append (my-select l pred) v))
;      (list-equal (my-select (ml-append l v) pred) (my-select l))))
;
;(define-udo (p v) (-> integer? boolean?)
;  (= v 42))

(provide my-select-*); my-select)