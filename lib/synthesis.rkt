#lang racket

(require "sketch.rkt"
         "../lang/ir.rkt")

(define debug #f)

(define (debug-synthesis (v boolean?))
  (set! debug v))

(define (debug-printf . args)
  (cond [debug (apply printf (first args) (list-tail args 1))]))

; build a hash table so that user function can look up the variables by name
(define (build-vars-map decl)
  (define h (hash))
  (for/list ([f (cons (ml-decl-ret-var decl) (ml-decl-formals decl))] #:when (ml-var? f)) (set! h (hash-set h (ml-var-name f) f)))
  h)

(define (build-varstypes-map decl)
  (define h (hash))
  (for/list ([f (cons (ml-decl-ret-var decl) (ml-decl-formals decl))] #:when (ml-var? f)) (set! h (hash-set h (ml-var-name f) (ml-expr-type f))))
  h)

; replace the body of each pc or inv decl in prog by calling the user defined fn
(define (define-space ast vc inv-space-fn pc-space-fn)

  
  (let ([space-defined (for/list ([d (ml-prog-decls vc)])
                                                                           
                         (cond [(equal? (ml-decl-name d) "pc")                                                                                        
                                (ml-decl (ml-expr-type d) (ml-decl-name d) (ml-decl-formals d) (ml-decl-ret-var d)
                                         (let ([body (pc-space-fn ast (build-vars-map d) (build-varstypes-map d))])
                                           (match body
                                             [(ml-block t es) (ml-block t es)]
                                             [e (ml-block void? (list e))])))]

                               [(and (string? (ml-decl-name d)) (string-prefix? (ml-decl-name d) "inv"))
                                (ml-decl (ml-expr-type d) (ml-decl-name d) (ml-decl-formals d) (ml-decl-ret-var d)
                                         (ml-block void? (list (inv-space-fn ast (build-vars-map d) (build-varstypes-map d)))))]
                               
                               [else d]))]) ; udos
    
    (ml-prog space-defined (ml-prog-asserts vc) (ml-prog-axioms vc))))

(define (resolve-choose prog [filename "metalift_skParse.txt"])

  ; chosen contains mapping of chooseFn number to the chosen value
  (define chosen
    (for/hash ([line (file->lines filename)])
      (debug-printf "read sk output: ~a~n" line)
      (define m (regexp-match #px"(\\d+):(\\d+)" line)) ; match on \d+ : \d+
      (values (string->number (second m)) (string->number (third m)))))
  
  (define choose-num 0)
  
  (define (resolve expr)    
    
    (match expr
      [(list es ...) (for/list ([e es]) (resolve e))]
      [(ml-block t es) (ml-block t (for/list ([e es]) (resolve e)))]
      [(ml-and t es) (ml-and t (for/list ([e es]) (resolve e)))]

      [(ml-choose t (list e ...))
       (debug-printf "resolve: ~a to ~a~n" choose-num (hash-ref chosen choose-num))
       (set! choose-num (+ 1 choose-num))
       (list-ref e (hash-ref chosen (- choose-num 1)))]
      
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
                           (ml-decl (ml-expr-type d) (ml-decl-name d) (ml-decl-formals d) (ml-decl-ret-var d)
                                    (resolve (ml-decl-body d))))])
    (ml-prog choose-resolved (ml-prog-asserts prog) (ml-prog-axioms prog))))

(provide define-space
         resolve-choose
         to-sk
         debug-sk-codegen
         )