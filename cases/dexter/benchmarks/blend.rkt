#lang metalift

;; Utility Functions (Function calls currently not supported)
(define (Mul8x8Div255 a b)
  (->  uint8_t?  uint8_t? (out uint8_t?))
  (set! out (/ (* a b) 255)))

(define (Screen8x8 a b)
  (->  uint8_t?  uint8_t? (out  uint8_t?))
  (- (+ a b) (Mul8x8Div255 a b)))

;; Normal blend for float types
(define (normalBlendf base active blended opacity pixels)
  (-> (listof flonum?) (listof flonum?) (listof flonum?) flonum? integer? (out (listof flonum?)))

  ; Init output with 0s
  (set! out blended)

  ; Compute blend
  (define pixel integer? 0)
  (while (< pixel pixels)
         (define v1 flonum? (* opacity (list-ref active pixel)))
         (define v2 flonum? (* (- 1.0 opacity) (list-ref base pixel)))
         (set! out (list-set out pixel (+ v1 v2)))
         (set! pixel (+ pixel 1))
         )
  )

;; Normal blend for uint8_t types
(define (normalBlend8 base active blended opacity pixels)
  (-> (listof uint8_t?) (listof uint8_t?) (listof uint8_t?) uint8_t? integer? (out (listof uint8_t?)))

  ; Init output with 0s
  (set! out blended)

  ; Compute blend
  (define pixel integer? 0)
  (while (< pixel pixels)
         (define v1 uint8_t? (Mul8x8Div255 opacity (list-ref active pixel)))
         (define v2 uint8_t? (Mul8x8Div255 (- 255 opacity) (list-ref base pixel)))
         (set! out (list-set out pixel (+ v1 v2)))
         (set! pixel (+ pixel 1))
         )
  )

;; Darken blend (lists interpreted as 2D buffers + contains conditionals)
(define (darkenBlend8 base active blended width height)
  (-> (listof uint8_t?) (listof uint8_t?) (listof uint8_t?) integer? integer? (out (listof uint8_t?)))

  ; Init output with 0s
  (set! out blended)

  ; Compute blend
  (define row integer? 0)
  (while (< row height)
         (define col integer? 0)
         (while (< col width)
                (define a uint8_t? (list-ref active (+ (* row width) col)))
                (define b uint8_t? (list-ref base (+ (* row width) col)))
                (set! out (list-set out (+ (* row width) col) (if (< a b) a b)))
                (set! col (+ col 1))
                )
         (set! row (+ row 1))
         )
  )

;; Test code below
(define width integer? 3)
(define height integer? 3)
(define pixels integer? 9)

(define basef (listof flonum?) (for/list ([x pixels]) 1.0))
(define activef (listof flonum?) (for/list ([x pixels]) 2.0))
(define outf (listof flonum?) (for/list ([x pixels]) 0.0))
(define opacityf flonum? 0.5)

(define base8 (listof uint8_t?) (for/list ([x pixels]) 100))
(define active8 (listof uint8_t?) (for/list ([x pixels]) 200))
(define out8 (listof uint8_t?) (for/list ([x pixels]) 0))
(define opacity8 uint8_t? 128)

(define base8_2d (listof uint8_t?) (for/list ([x (* width height)]) 100))
(define active8_2d (listof uint8_t?) (for/list ([x (* width height)]) 200))
(define out8_2d (listof uint8_t?) (for/list ([x (* width height)]) 0))

;(normalBlendf basef activef outf opacityf pixels)
;(normalBlend8 base8 active8 out8 opacity8 pixels)
;(darkenBlend8 base8_2d active8_2d out8_2d width height)

;(define (bitwise-ops i) (-> integer? (out integer?))
 ; (set! out (bitwise-not (arithmetic-shift (bitwise-ior i (bitwise-and i i)) 2))))

;(bitwise-ops 1) ; ~( ((1&1) | 1) << 2 ) = -5