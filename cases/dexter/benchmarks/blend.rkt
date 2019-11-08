#lang metalift

;; Utility Functions
(define (Mul8x8Div255 a b)
  (->  uint8_t?  uint8_t? (out  uint8_t?))
  (/ (* a b) 255))

(define (Screen8x8 a b)
  (->  uint8_t?  uint8_t? (out  uint8_t?))
  (- (+ a b) (Mul8x8Div255 a b)))

;; Normal blend for float types
(define (normalBlendf base active opacity pixels)
  (-> (listof floatnum?) (listof floatnum?) floatnum? integer? (out (list floatnum?)))

  ; Init output with 0s
  (set! out (for/list ([i pixels]) 0.0))

  ; Compute blend
  (define pixel integer? 0)
  (while (< pixel pixels)
         (define v1 floatnum? (* opacity (list-ref active pixel)))
         (define v2 floatnum? (* (- 1.0 opacity) (list-ref base pixel)))
         (set! out (list-set out pixel (+ v1 v2)))
         (set! pixel (+ pixel 1))
         )
  )

;; Normal blend for uint8_t types
(define (normalBlend8 base active opacity pixels)
  (-> (listof uint8_t?) (listof uint8_t?) uint8_t? integer? (out (list uint8_t?)))

  ; Init output with 0s
  (set! out (for/list ([i pixels]) 0))

  ; Compute blend
  (define pixel integer? 0)
  (while (< pixel pixels)
         (define v1 uint8_t? (Mul8x8Div255 opacity (list-ref active pixel)))
         (define v2 uint8_t? (Mul8x8Div255 (- 255 opacity) (list-ref base pixel)))
         (set! out (list-set out pixel (+ v1 v2)))
         (set! pixel (+ pixel 1))
         )
  )

;; Test code below
(define width integer? 3)
(define height integer? 3)
(define pixels integer? 9)

(define basef (listof integer?) (for/list ([x pixels]) 1.0))
(define activef (listof integer?) (for/list ([x pixels]) 2.0))
(define opacityf integer? 0.5)

(define base8 (listof integer?) (for/list ([x pixels]) 100))
(define active8 (listof integer?) (for/list ([x pixels]) 200))
(define opacity8 integer? 128)

(normalBlendf basef activef opacityf pixels)
(normalBlend8 base8 active8 opacity8 pixels)
(Mul8x8Div255 128 100)

;(define (bitwise-ops i) (-> integer? (out integer?))
 ; (set! out (bitwise-not (arithmetic-shift (bitwise-ior i (bitwise-and i i)) 2))))

;(bitwise-ops 1) ; ~( ((1&1) | 1) << 2 ) = -5