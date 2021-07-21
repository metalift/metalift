(declare-const b0 Bool)
(declare-const b4 Bool)
(declare-const b7 Bool)
(declare-const b13 Bool)

(declare-const r0 Int)
(declare-const r1 Int)
(declare-const r2 Int)
(declare-const r2_1 Int)
(declare-const r2_2 Int)
(declare-const r3 Int)
(declare-const r3_1 Int)
(declare-const r3_2 Int)
(declare-const r4 Int)
(declare-const r5 Int)
(declare-const r6 Bool)
(declare-const r8 Int)
(declare-const r9 Int)
(declare-const r9_p Int)
(declare-const r10 Int)
(declare-const r11 Int)
(declare-const r12 Int)
(declare-const r14 Int)

(define-fun iff ( (c1 Bool) (c2 Bool) ) (Bool) (and (=> c1 c2) (=> c2 c1)))

(define-fun-rec sum_n ((x Int)) Int
                  (ite (>= x 1)
                       (+ x (sum_n (- x 1)))
                       0))


; ps : x = sum_n(y-1)
; x = r2, y = r3
(define-fun ps ( (r2 Int) (r3 Int) ) (Bool) 
  (= r2 (sum_n (- r3 1))))

; invariant : (x = sum_n(y-1) and y>=1)
(define-fun inv ( (r2 Int) (r3 Int) ) (Bool)
  (and (= r2 (sum_n (- r3 1))) (>= r3 1)))


; vc
(assert (not (=> 

	(and 
	(iff b0 (=> (and (= r1 0) (= r2 0) (= r3 1)) b4))

	; loop head
	; havoc r2, r3
	; assume inv(x1, y1)

	(iff b4 (=> (and (inv r2_1 r3_1) (= r5 r3_1) (= r6 (<= r5 3))) (and b7 b13)))

	; loop body
	; assume loop guard
	; assume x2 = x1 + y1
	; assume y2 = y1 + 1
	; assert inv(x2, y2)

	(iff b7 (=> (and 
									 r6 ; assume loop guard
									 (= r8 r2_1)
									 (= r9 r3_1)
									 (= r10 (+ r8 r9)) 
									 (= r2_2 r10)
									 (= r11 r3_1)
									 (= r12 (+ r11 1))
									 (= r3_2 r12))
							(inv r2_2 r3_2)))

	; after
	(iff b13 (=> (and 
									 (not r6) ; assume not loop guard
									 (= r14 r2_1))
								(ps r14 r3_1)))
	)

b0)))


(check-sat)
(get-model)
