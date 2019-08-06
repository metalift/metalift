#lang racket

(require "sketch.rkt")
;(require "z3.rkt")
(require "../lang/ir.rkt")

; replace the body of each pc or inv decl in prog by calling the user defined fn
(define (define-space ast vc inv-space-fn pc-space-fn)
  (let ([space-defined (for/list ([d (ml-prog-decls vc)])
                         (cond [(equal? (ml-decl-name d) "pc")
                                (ml-decl (ml-decl-name d) (ml-decl-formals d) (list (pc-space-fn ast (ml-decl-formals d))) (ml-decl-ret-type d))]
                               [(equal? (ml-decl-name d) "inv")
                                (ml-decl (ml-decl-name d) (ml-decl-formals d) (list (inv-space-fn ast (ml-decl-formals d))) (ml-decl-ret-type d))]
                               [else (error (format "unknown decl: ~a" ml-decl-name d))]))])
    (ml-prog space-defined (ml-prog-asserts vc))))


(define (resolve-choose prog)
  ;(to-sk prog)
  ; temporary hack that always choose the first expr in choose
  (define (resolve expr)
    (printf "resolving ~a~n" expr)
    (match expr
      [(list es ...) (for/list ([e es]) (resolve e))]
      [(ml-and t es) (ml-and t (for/list ([e es]) (resolve e)))]
      [(ml-choose t (list e ...)) (first e)]
      [(ml-eq t e1 e2) (ml-eq t (resolve e1) (resolve e2))]
      [(ml-if t c e1 e2) (ml-if t (resolve c) (resolve e1) (resolve e2))]
      [(ml-not t e) (ml-not t (resolve e))]
      [(ml-< t e1 e2) (ml-< t (resolve e1) (resolve e2))]
      [(ml-> t e1 e2) (ml-< t (resolve e1) (resolve e2))]
      [(ml-<= t e1 e2) (ml-<= t (resolve e1) (resolve e2))]
      [(ml->= t e1 e2) (ml->= t (resolve e1) (resolve e2))]
      [(ml-- t e1 e2) (ml-- t (resolve e1) (resolve e2))]
      [(ml-+ t e1 e2) (ml-+ t (resolve e1) (resolve e2))]
      [(ml-call t name args) (ml-call t name (for/list ([a args]) (resolve a)))]


      [(ml-list t es) (ml-list t (for/list ([e es]) (resolve e)))]
      [(ml-list-append t l e) (ml-list-append t (resolve l) (resolve e))]
      [(ml-list-equal t l1 l2) (ml-list-equal t (resolve l1) (resolve l2))]
      [(ml-list-length t l) (ml-list-length t (resolve l))]
      [(ml-list-prepend t l e) (ml-list-prepend t (resolve l) (resolve e))]
      [(ml-list-ref t l e) (ml-list-ref t (resolve l) (resolve e))]      
      [(ml-list-tail t l e) (ml-list-tail t (resolve l) (resolve e))]
      [(ml-list-take t l e) (ml-list-take t (resolve l) (resolve e))]

      [(or (? ml-var? e) (? ml-lit? e) (? procedure? e)) e]))
  
  (let ([choose-resolved (for/list ([d (ml-prog-decls prog)])
                           (ml-decl (ml-decl-name d) (ml-decl-formals d) (resolve (ml-decl-body d)) (ml-decl-ret-type d)))])
    (ml-prog choose-resolved (ml-prog-asserts prog))))

(provide define-space
         resolve-choose
         ;to-z3
         to-sk
         )