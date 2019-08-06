#lang racket

; translates ML IR to Sketch

(require (except-in "../lang/ir.rkt" expr))

(define (to-sk p)
  (printf "converting to sketch~n")
  (let* ([out (open-output-string)]
        
         [decls (for/list ([d (ml-prog-decls p)]) (sk/decl d))]
         ;[harness-args (sk/arg-list (append (ml-prog-out-vars p) (ml-prog-in-vars p)) #t)]
         [harness (parse-harness (list (cons 'i integer?) (cons 'in (ml-listof integer?)) (cons 'out (ml-listof integer?))))]
                  ;(append (ml-prog-out-vars p) (ml-prog-in-vars p)))]
         
         [harness-args (car harness)]
         [harness-inits (cdr harness)]
         ;(string-join (for/list ([a (append (ml-prog-out-vars p) (ml-prog-in-vars p))])
         ;                            (format "int ~a" (sk/expr a))) ", ")]
                                 
        [asserts (for/list ([a (ml-prog-asserts p)]) (format "  ~a; ~n" (sk/expr a)))]
        )
    
    ; includes
    (fprintf out "include \"/Users/akcheung/proj/metalift/metalift/sketch/mllist.sk\";~n~n")

    ; decls
    (fprintf out (string-join decls "~n"))

    ; chooses
    (fprintf out (string-join (sk/choose-impls) "~n"))
    
    ; harness
    
    (fprintf out (format "harness void main(~a) {~n~a~n~a ~n}" harness-args harness-inits (string-join asserts "~n")))
    
    (get-output-string out)
    (with-output-to-file "/tmp/t.sk" #:exists 'replace (lambda () (printf (get-output-string out))))
    ))

(define (parse-harness vars)
  
  (define (init-decl v)
    (let ([name (car v)] [type (cdr v)])
      (match type
        ; XXX get rid of 'integer?
        [(or (== integer?) (== boolean?) (== 'integer?) (== 'boolean?)) (format "~a ~a" (sk/type type) (sk/name name))]
        [(ml-listof integer?) 
        ;[(list 'listof 'integer?)
         (let ([size (format "~a_sz" (sk/name name))]
               [vals (format "~a_vals" (sk/name name))])
           (format "int ~a, int[~a] ~a" size size vals))]
      )))
  
  (define (init-expr v)
    (let ([name (car v)] [type (cdr v)])
      (match type
        ; XXX get rid of 'integer?
        [(or (== integer?) (== boolean?) (== 'integer?) (== 'boolean?)) ""]
        [(ml-listof integer?) 
        ;[(list 'listof 'integer?)
         (format "  ~a ~a = make_MLList(~a_sz, ~a_vals);" (sk/type type) (sk/name name) (sk/name name) (sk/name name))]
      )))
  
  (let ([decls empty] [inits empty])    
    (for ([v vars])
      (let ([name (car v)] [type (cdr v)])
        (set! decls (cons (init-decl v) decls))
        (set! inits (cons (init-expr v) inits))
        ))
               
    ;(cons (sk/arg-list revised-vars #t) "")))
    (cons (string-join decls ", ") (string-join inits "~n"))))
    

(define (sk/decl decl)
  (printf "translating decl ~a~n" decl)
  ;(struct ml-decl (name formals body ret-type) #:transparent)
  (match decl
    [(ml-decl name formals body rtype)
     ;(printf "rtype for ~a ~a" name (sk/type rtype))
     
     (let ([translated-body (open-output-string)])
       (for ([e body])
         (write-string (sk/expr e) translated-body))
       (format "~a ~a (~a) { ~a ~a; }~n~n" (sk/type rtype) (sk/name name) (sk/arg-list formals #t)
               (if (equal? rtype void?) "" "return")
               (get-output-string translated-body)))]))


(define choose-fns empty)

(define (sk/choose-impls)
  (define template #<<eos
~a choose~a (~a) {
  int chosen~a = ??(~a);
  if (chosen~a == 0) return v0;
~a
  else assert false;
}


eos
)
  (for/list ([fn choose-fns] [n (in-naturals)])
    (let* ([type (first fn)] [num-args (second fn)] [arg-str (third fn)]
           [arg-str (string-join (for/list ([n (in-range num-args)]) (format "~a v~a" (sk/type type) n)) ", ")])
      (format template (sk/type type) n arg-str n (exact-ceiling (log num-args 2)) n
              (string-join (for/list ([m (in-range 1 num-args)])
                             (format "  else if (chosen~a == ~a) return v~a;~n" n m m)) "~n")))))
 

(define (sk/expr e)

  (printf "parsing sk: ~a~n" e)
  (match e

    [(ml-assert type e) (format "assert(~a)" (sk/expr e))]
    [(ml-call type name args) (format "~a(~a)" (sk/name name) (sk/arg-list args #f #f))]    
    [(ml-choose type (list es ...)) (sk/choose type es)]        
    [(ml-implies type e1 e2) (format "(!(~a) || (~a))" (sk/expr e1) (sk/expr e2))]
    [(ml-if type c e1 e2) (format "(~a) ? ~a : ~a" (sk/expr c) (sk/expr e1) (sk/expr e2))]

    [(ml-and type es) (string-join (for/list ([e es]) (format "~a" (sk/expr e))) " && "
                                   #:before-first "( "
                                   #:after-last " )")]
                        
    
    [(ml-eq type e1 e2) (format "~a == ~a" (sk/expr e1) (sk/expr e2))]
    [(ml-not type e) (format "!(~a)" (sk/expr e))]
    [(ml-< type e1 e2) (format "(~a < ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-> type e1 e2) (format "(~a > ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-<= type e1 e2) (format "(~a <= ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml->= type e1 e2) (format "(~a >= ~a)" (sk/expr e1) (sk/expr e2))]

    [(ml-+ type e1 e2) (format "(~a + ~a)" (sk/expr e1) (sk/expr e2))]
    [(ml-- type e1 e2) (format "(~a - ~a)" (sk/expr e1) (sk/expr e2))]    

    ; list functions   
    [(ml-list-append type l e) (format "list_append(~a, ~a)" (sk/expr l) (sk/expr e))]
    [(ml-list-equal type l1 l2) (format "list_equal(~a, ~a)" (sk/expr l1) (sk/expr l2))]
    [(ml-list-length type e) (format "list_length(~a)" (sk/expr e))]
    [(ml-list-prepend type e l) (format "list_prepend(~a, ~a)" (sk/expr e) (sk/expr l))]
    [(ml-list-ref type l e) (format "list_get(~a, ~a)" (sk/expr l) (sk/expr e))]
    [(ml-list-tail type l e) (format "list_tail(~a, ~a)" (sk/expr l) (sk/expr e))]
    [(ml-list-take type l e) (format "list_take(~a, ~a)" (sk/expr l) (sk/expr e))]    
    [(ml-list type es)  (if (= (length es) 0) "list_empty()"     
                            (format "make_MLList(~a, ~a)" (length es) (sk/arg-list es #f #f)))]
    
    ;[(? symbol? sym) (format "~a" (sk/name sym))]
    ;[(? number? n) (format "~a" n)]
    ;[(? boolean? n) (if (equal? n #t) "true" "false")]
    [e #:when (ml-var? e) (format "~a" (sk/name (ml-var-name e)))]
    [e #:when (and (ml-lit? e) (equal? integer? (expr-type e))) (ml-lit-val e)]
    [e #:when (and (ml-lit? e) (equal? boolean? (expr-type e))) (if (equal? (ml-lit-val e) #t) "true" "false")]
    
    [(? procedure? n) (sk/name (second (regexp-match #rx"procedure:(.*)>" (format "~a" n))))]
    ;[e #:when (ml-user? e) (sk/udo e)]
    ))


(define (sk/choose type as)
  (let ([num (length choose-fns)]
        [args (sk/arg-list as #f #f)])
    (set! choose-fns (append (list (list type (length as) args)) choose-fns))
    (format "choose~a(~a)" num args)))

(define (sk/udo e)
  (printf "parse udo: ~a ~n" (struct->vector e))
  (match (struct->vector e)
    [(vector name type es ...) (format "~a(~a)" (sk/name (second (regexp-match #rx"struct:(.*)" (format "~a" name))))
                                       (sk/arg-list es #f))]))


(define (sk/arg-list args need-type [has-type #t])
  (let ([params (for/list ([a args])
                  (if need-type
                      (format "~a ~a" (sk/type (expr-type a)) (sk/name (ml-var-name a)))
                      (if has-type
                          (format "~a" (sk/expr (ml-var-name a)))
                          (format "~a" (sk/expr a))
                          )))])
    (string-join params ", ")))


(require syntax/parse)
(define (sk/type t)
  (match t
    ['integer? "int"]
    ['boolean? "bit"]
    [(== boolean?) "bit"] ; vc.rkt uses boolean? explicitly
    [(== integer?) "int"] ; vc.rkt uses boolean? explicitly
    [(ml-listof type) (format "MLList<~a>" (sk/type type))]
    ;[(list 'listof 'integer?) "MLList<int>"]
    ;[(list 'listof type) (printf "MLList<~a>" (sk/type type))]
    [(list '-> args ...) "fun"]
    ))
  
;  (match t
;    [(== boolean?) "bit"]
;    [(== integer?) "int"]    
;    [flat-contract?
;     (let [(n (datum->syntax #f t))]
;       (printf "n is ~a and ~a~n" (flat-contract-predicate t) n)
;       (syntax-parse n
;         #:datum-literals (listof flat-contract)
;         [(flat-contract (listof e)) (format "got ~a" #'e)]))]     
;    ))

; escape sketch's reserved characters for names
(define (sk/name n)
  (let ([name (string-replace (format "~a" n) "-" "_")])
    ; procedure is printed as #<procedure:[name]>
    (if (procedure? n) (second (regexp-match #rx"procedure:(.*)>" name)) name)))



(provide to-sk)