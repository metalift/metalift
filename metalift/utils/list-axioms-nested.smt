
(declare-fun list_list_length ( (MLList (MLList Int) ) ) Int)
(assert (= (list_list_length (as nil (MLList (MLList Int) ))) 0))
(assert (forall ( (val (MLList Int) ) (l (MLList (MLList Int) )) )
                (= (list_list_length (cons val l)) (+ 1 (list_list_length l)))))
(assert (forall ( (l (MLList (MLList Int) )) )
                (<= 0 (list_list_length l))))

;end of list length

(define-fun list_list_prepend ( (val (MLList Int) ) (l (MLList (MLList Int) ) )) (MLList (MLList Int) ) (cons val l))
; end of list prepend
            

(declare-fun list_list_append ( (MLList (MLList Int)  ) (MLList Int) ) (MLList (MLList Int) ))
(assert (forall ( (val (MLList Int)) )
                (= (list_list_append (as nil (MLList (MLList Int))) val) (cons val (as nil (MLList (MLList Int)))))))
(assert (forall ( (h (MLList Int)) (t (MLList (MLList Int))) (val (MLList Int)) )
                (= (list_list_append (cons h t) val) (cons h (list_list_append t val)))))
;end of list append

(declare-fun list_list_get_helper ( (MLList (MLList Int) ) Int ) (MLList Int) )
(define-fun list_list_get ( (l (MLList (MLList Int) )) (i Int) ) (MLList Int) (list_list_get_helper l i))
(assert (forall ( (h (MLList Int) ) (t (MLList (MLList Int) )) (i Int) )
                (ite (<= i 0)
                     (= (list_list_get_helper (cons h t) i) h)
                     (= (list_list_get_helper (cons h t) i) (list_list_get_helper t (- i 1))))))
;end of list get

(define-fun list_list_empty ( ) (MLList (MLList Int)) (as nil (MLList (MLList Int) )))
;end of empty list



(define-fun-rec list_list_tail ((l (MLList (MLList Int) ) ) (n Int)) (MLList (MLList Int) ) 
  (ite (<= n 0)  l (list_list_tail (tail l) (- n 1))))
(assert (forall ( (start Int) (h (MLList Int) ) (t (MLList (MLList Int) )) )
                (ite (<= start 0)
                     (= (list_list_tail (cons h t) start) (cons h t))
                     (= (list_list_tail (cons h t) start) (list_list_tail t (- start 1))))))
(assert (forall ( (start Int) )
                (= (list_list_tail (as nil (MLList (MLList Int) )) start) (as nil (MLList (MLList Int)) ))))
(assert (forall ( (start Int) (l (MLList (MLList Int) )) )
                (=> (>= start (list_list_length l))
                    (= (list_list_tail l start) (as nil (MLList (MLList Int) ))))))

; end of list tail

(declare-fun list_list_take ( (MLList (MLList Int)) Int ) (MLList (MLList Int)))

(assert (forall ( (end Int) (h (MLList Int)) (t (MLList (MLList Int))) )
                (ite (<= end 0)
                     (= (list_list_take (cons h t) end) (as nil (MLList (MLList Int))))
                     (= (list_list_take (cons h t) end) (cons h (list_list_take t (- end 1)))))))
(assert (forall ( (end Int) )
                (= (list_list_take (as nil (MLList (MLList Int))) end) (as nil (MLList (MLList Int))))))
(assert (forall ( (end Int) (l (MLList (MLList Int))) )
                (=> (>= end (list_list_length l))
                    (= (list_list_take l end) l))))

(assert (forall ( (l (MLList (MLList Int))) ) (= (list_list_take l 0) (as nil (MLList (MLList Int))))))
; end of list take 
