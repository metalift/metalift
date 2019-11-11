#lang racket
(require "../../lang/ir-ctor.rkt"
         "../../lang/ir.rkt")


(define (interpret-arith op lhs rhs)
  (if (and (number? lhs) (number? rhs))
      (apply op (list lhs rhs))
      (format "(~a ~a ~a)" op lhs rhs)))

(define (interpret-body ast env)
  ;; returns (ret-val . updated-env)

  (println "===============")
  (display "ast: ")
  (println ast)
  (display "env: ")
  (println env)
  (match ast
    ;; if a single-element block, return the value of the statement
    [(ml-block type (list stmt)) (interpret-body stmt env)]
    [(ml-block type body) (let ([ret (interpret-body (first body) env)])
                            (interpret-body (ml-block type (rest body)) (cdr ret)))]
    ;; this is assuming we're only updating a whole array?
    [(ml-set! _ lhs rhs) (begin (hash-set! env (ml-var-name lhs) 
                                            (car (interpret-body rhs env)))
                                   (cons 'void env))]
    [(ml-var _ name) (cons (hash-ref env name) env)]
    [(ml-define _ lhs rhs) (begin (hash-set! env (ml-var-name lhs)
                                                (car (interpret-body rhs env)))
                                      (cons 'void env))]
    [(ml-lit _ val) (cons val env)]
    ;; a bit hacky: if test is true, we run an iteration of the loop and recurse
    ;; with the same ast.  If it's false, we return
    [(ml-while _ test body) (if (car (interpret-body test env))
                                   (let ([new-env (cdr (interpret-body body env))])
                                     (interpret-body ast new-env))
                                   (cons 'void env))]
    [(ml-list-ref _ lst ref) (cons (list-ref (car (interpret-body lst env))
                                             (car (interpret-body ref env)))
                                   env)]
    [(ml-list-set _ lst idx val) (let ([the-list (car (interpret-body lst env))]
                                       [the-idx (car (interpret-body idx env))]
                                       [the-val (car (interpret-body val env))])
                                   (cons (list-set the-list the-idx the-val)
                                         env))]
    [(ml-< _ lhs rhs) (cons (interpret-arith < (car (interpret-body lhs env))
                                             (car (interpret-body rhs env)))
                            env)]
    [(ml-+ _ lhs rhs) (cons (interpret-arith + (car (interpret-body lhs env))
                                             (car (interpret-body rhs env)))
                            env)]
    [(ml-- _ lhs rhs) (cons (interpret-arith - (car (interpret-body lhs env))
                                             (car (interpret-body rhs env)))
                            env)]
    [(ml-* _ lhs rhs) (cons (interpret-arith * (car (interpret-body lhs env))
                                             (car (interpret-body rhs env)))
                            env)]
    [_ (cons #f env)])
)

(define (initial-env formals ret-var)
  (let ([env (make-hash)])
    (for ([i (append formals (list ret-var))])
      (hash-set! env (ml-var-name i) (if (ml-listof? (ml-expr-type i)) (make-list 27 (string->symbol (format "~a" (ml-var-name i)))) (random 11)))
      (println i))
    env)
)

(define (interpret ast)
  ;; ast must be a ml-decl
  (let ([env (initial-env (ml-decl-formals ast) (ml-decl-ret-var ast))])
    (interpret-body (ml-decl-body ast) env)))

(provide interpret)
