#lang racket

(require "../lang/ir.rkt"
         "../lib/util.rkt")

(define (to-z3 p axioms-path)
  (printf "**** Converting to z3~n~n")
  
  (define out (open-output-string))            

  (define ml-axioms (file->string axioms-path))
  
  (define-values (decl-names decl-bodies) (for/fold ([ns empty] [bs empty]) ([d (ml-prog-decls p)])
                                            (let-values ([(name body) (z3/decl d)])
                                              (values (cons name ns) (cons body bs)))))

  ; variables used in the asserts are declared as constants
  (define harness-args (z3/arg-list (for/fold ([vars (set)]) ([a (ml-prog-asserts p)]) (set-union vars (used-vars a)))
                                    #t #:prefix "declare-const "))

  (define user-axioms (for/list ([a (ml-prog-axioms p)]) (format "~a~n~n" (z3/axiom a))))
  
  ; asserts: each one is negated assertion
  (define asserts (for/list ([a (ml-prog-asserts p)]) (format "(push)~n(assert (not ~a))~n(check-sat)~n(pop)~n" (z3/expr (ml-assert-e a)))))  

  
  ; generate output

  (fprintf out ";;; ML axioms~n~n")
  (fprintf out ml-axioms)
  
  (fprintf out "~n~n;;; Function declarations~n~n")
  (fprintf out (format "(define-funs-rec~n(~n~a~n)~n(~n~a~n)~n)~n~n" (string-join decl-names "~n") (string-join decl-bodies "~n")))

  (fprintf out "~n~n;;; User axioms~n")
  (fprintf out (format "~n~a~n" (string-join user-axioms "~n")))
  
  (fprintf out "~n~n;;; Constants~n")
  (fprintf out (string-join harness-args "~n"))

  (fprintf out "~n~n;;; Assertions~n")
  (fprintf out (format "~n~a~n" (string-join asserts "~n")))
        
  (get-output-string out)
  )

(define (z3/axiom axiom)
  (define formals (z3/arg-list (ml-axiom-formals axiom) #t))
  (format "(assert (forall ( ~a ) ~n ~a ))~n" (string-join formals " ") (z3/expr (ml-axiom-body axiom))))


(define (z3/arg-list args need-type [has-type #t] #:prefix [prefix ""])
  
  (define params (for/list ([a args])            
                   (if need-type
                       (format "(~a~a ~a)" prefix (z3/name (ml-var-name a)) (z3/type (ml-expr-type a)))
                       (format "~a" (z3/expr a)))))
    params)

 
(define (z3/decl decl)
  (printf "translating decl ~a~n" decl)
  
  (match decl
    [(ml-decl type name formals ret-var body)
     
     (values (format "(~a ~a ~a)" (z3/name name) (z3/arg-list formals #t) (z3/type (ml-decl-ret-type decl)))
             (format "~a" (z3/expr body)))]))


(define (z3/expr e)

  (printf "parsing z3: ~a~n" e)
  (match e
       
    [(ml-and _ es) (format "(and ~a)" (string-join (for/list ([e es]) (z3/expr e)) " "))]

    [(ml-eq _ e1 e2) (format "(= ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-block _ es) (string-join (for/list ([e es]) (z3/expr e)) "~n")]

    [(ml-call _ name args) (format "(~a ~a)" (z3/name name) (string-join (z3/arg-list args #f #f) " "))]

    [(ml-implies _ e1 e2) (format "(=> ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-if _ c e1 e2) (format "(ite ~a ~a ~a)" (z3/expr c) (z3/expr e1) (z3/expr e2))]

    [(ml-not _ e) (format "(not ~a)" (z3/expr e))]
    
    [(ml-+ _ e1 e2) (format "(+ ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-- _ e1 e2) (format "(- ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-< _ e1 e2) (format "(< ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-<= _ e1 e2) (format "(<= ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml->= _ e1 e2) (format "(>= ~a ~a)" (z3/expr e1) (z3/expr e2))]

    
    ; list functions   
    [(ml-list-append type l e) (format "(list_append ~a ~a)" (z3/expr l) (z3/expr e))]
    [(ml-list-equal type l1 l2) (format "(list_equal ~a ~a)" (z3/expr l1) (z3/expr l2))]
    [(ml-list-length type e) (format "(list_length ~a)" (z3/expr e))]
    [(ml-list-prepend type e l) (format "(list_prepend ~a ~a)" (z3/expr e) (z3/expr l))]
    [(ml-list-ref type l e) (format "(list_get ~a ~a)" (z3/expr l) (z3/expr e))]
    [(ml-list-tail type l e) (format "(list_tail ~a ~a)" (z3/expr l) (z3/expr e))]
    [(ml-list-take type l e) (format "(list_take ~a ~a)" (z3/expr l) (z3/expr e))]    
    [(ml-list type es)  (if (= (length es) 0) "list_empty"
                            (error "NYI"))]
                            ;(format "make_MLList(~a, ~a)" (length es) (sk/arg-list es #f #f)))]

        
    [(ml-var _ name) (format "~a" (z3/name name))]
    [(ml-lit t v) (match t
                    [(== integer?) (format "~a" v)]
                    [(== boolean?) (if (equal? v #t) "true" "false")]
                    [_ (error (format "unknown literal type: ~a~n" e))])]

    [e (error (format "z3 NYI: ~a" e))]

    ;[(? boolean? n) (if (equal? n #t) "true" "false")]
    ))


(define (z3/type t)  
  (match t
    ['integer? "Int"]
    ['boolean? "Bool"]
    [(== boolean?) "Bool"] ; vc.rkt uses boolean? explicitly
    [(== integer?) "Int"] ; vc.rkt uses boolean? explicitly
    [(ml-listof type) (format "(MLList ~a)" (z3/type type))]
    ))

; escape sketch's reserved characters for names
(define (z3/name n)
  (let ([name (string-replace (string-replace (format "~a" n) "-" "_") "*" "_star")])
    ; procedure is printed as #<procedure:[name]>
    (if (procedure? n) (second (regexp-match #rx"procedure:(.*)>" name)) name)))



(provide to-z3)