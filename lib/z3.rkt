#lang racket

(require "../lang/ir.rkt")

(define (to-z3 p)
  (printf "converting to z3~n")
  (let* ([out (open-output-string)]
        
         [ds (for/list ([d (ml-prog-decls p)]) (z3/decl d))]
         [decl-names (for/list ([d ds]) (car d))]
         [decl-bodies (for/list ([d ds]) (cdr d))]
         [harness-args (z3/arg-list (append (ml-prog-out-vars p) (ml-prog-in-vars p)) #t #:prefix "declare-const ")]
                                 
         ;[asserts (for/list ([a (ml-prog-asserts p)]) (format "~a" (z3/expr a)))]
         [asserts (for/list ([a (ml-prog-asserts p)]) (format "(push)~n(assert (not ~a))~n(check-sat) (pop)~n" (z3/expr a)))]
        )
    
    ; decls
    (fprintf out (format "(define-funs-rec~n(~n~a~n)~n(~n~a~n)~n)~n~n" (string-join decl-names "~n") (string-join decl-bodies "~n")))
   
    ; harness
    (fprintf out (string-join harness-args "~n"))
    ;(fprintf out (format "~n~n(define-fun main () Bool~n  (and ~a~n))~n" (string-join asserts "~n")))
    ;(fprintf out (format "(assert (not main))~n(check-sat)"))

    (fprintf out (format "~n~a~n" (string-join asserts "~n")))
    
    
    ;(fprintf out (format "harness void main(~a) {~n~a ~n}" harness-args (string-join asserts "~n")))
    
    (get-output-string out)
    (with-output-to-file "/tmp/t.z3" #:exists 'replace (lambda () (printf (get-output-string out))))
    ))

(define (z3/arg-list args need-type [has-type #t] #:prefix [prefix ""])
  (let ([params (for/list ([a args])            
                  (if need-type
                      (format "(~a~a ~a)" prefix (z3/expr (car a)) (z3/type (cdr a)))
                      (if has-type
                          (format "~a" (z3/expr (car a)))
                          (format "~a" (z3/expr a))
                          )))])
    ;(string-join params "~n")))
    params))

 
(define (z3/decl decl)
  (printf "translating decl ~a~n" decl)
  ;(struct ml-decl (name formals body ret-type) #:transparent)
  (match decl
    [(ml-decl name formals body rtype)
     ;(printf "rtype for ~a ~a" name (sk/type rtype))
     (cons (format "(~a ~a ~a)" (z3/name name) (z3/arg-list formals #t) (z3/type rtype))
           (format "~a" (z3/expr body)))]))
     ;(format "(define-fun ~a ~a ~a ~n  ~a~n)~n~n" (z3/name name) (z3/arg-list formals #t) (z3/type rtype) 
             ;(z3/expr body))]))

(define (z3/expr e)

  (printf "parsing z3: ~a~n" e)
  (match e
       
    [(ml-and type e1 e2) (format "(and ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-eq type e1 e2) (format "(= ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-call type name args) (format "(~a ~a)" (z3/name name) (string-join (z3/arg-list args #f #f) " "))]

    [(ml-implies type e1 e2) (format "(=> ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-if type c e1 e2) (format "(ite ~a ~a ~a)" (z3/expr c) (z3/expr e1) (z3/expr e2))]

    [(ml-not type e) (format "(not ~a)" (z3/expr e))]
    
    [(ml-+ type e1 e2) (format "(+ ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-- type e1 e2) (format "(- ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-< type e1 e2) (format "(< ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml-<= type e1 e2) (format "(<= ~a ~a)" (z3/expr e1) (z3/expr e2))]

    [(ml->= type e1 e2) (format "(>= ~a ~a)" (z3/expr e1) (z3/expr e2))]

    
    ; list functions   
    [(ml-list-append type l e) (format "(list_append ~a ~a)" (z3/expr l) (z3/expr e))]
    [(ml-list-equal type l1 l2) (format "(list_equal ~a ~a)" (z3/expr l1) (z3/expr l2))]
    [(ml-list-length type e) (format "(list_length ~a)" (z3/expr e))]
    [(ml-list-prepend type e l) (format "(list_prepend ~a ~a)" (z3/expr e) (z3/expr l))]
    [(ml-list-ref type l e) (format "(list_get ~a ~a)" (z3/expr l) (z3/expr e))]
    [(ml-list-tail type l e) (format "(list_tail ~a  ~a)" (z3/expr l) (z3/expr e))]
    [(ml-list-take type l e) (format "(list_take ~a  ~a)" (z3/expr l) (z3/expr e))]    
    [(ml-list type es)  (if (= (length es) 0) "list_empty"
                            (error "NYI"))]
                            ;(format "make_MLList(~a, ~a)" (length es) (sk/arg-list es #f #f)))]

    
    [(? symbol? sym) (format "~a" (z3/name sym))]
    [(? number? n) (format "~a" n)]
    [(? boolean? n) (if (equal? n #t) "true" "false")]
    ))


(define (z3/type t)  
  (match t
    ['integer? "Int"]
    ['boolean? "Bool"]
    [(== boolean?) "Bool"] ; vc.rkt uses boolean? explicitly
    [(== integer?) "Int"] ; vc.rkt uses boolean? explicitly
    [(list 'listof 'integer?) "(MLList Int)"]
    ))

; escape sketch's reserved characters for names
(define (z3/name n)
  (let ([name (string-replace (format "~a" n) "-" "_")])
    ; procedure is printed as #<procedure:[name]>
    (if (procedure? n) (second (regexp-match #rx"procedure:(.*)>" name)) name)))



(provide to-z3)