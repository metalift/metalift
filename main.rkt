#lang racket

; entry point of metalift

; we don'g need to redefine module-begin as we current don't need whole program info
;(define-syntax (@#%module-begin stx) 
;  (syntax-case stx ()
;
;    ; right now we just return the input stx as-is. later on we might want to optimize the input code    
;    [(a forms ...)     
;     (let* ([core (local-expand #'(#%plain-module-begin forms ...) 'module-begin (list #'module*))]
;            ;[vc (compute-vc core)]
;            ;([core (local-expand #'(#%plain-module-begin forms ...) 'expression (list #'for))] ;#'module* ))]
;            ;([core #`(#%module-begin #,@(local-expand #'(forms ...) 'expression (list #'for)))] ;#'module* ))]
;            ;[vars (find-mutated-vars core)]
;            )
;           ; [transformed (box-mutated-vars core vars)])
;             
;       ;core
;              
;       #'(#%module-begin
;          forms ...
;          )
;     )]
;    ))

(require "lang/base.rkt")

(provide
 ;(rename-out [@#%module-begin #%module-begin])
 quote #%module-begin
 quote #%datum
 quote #%app
 quote #%top-interaction
 
 (all-from-out "lang/base.rkt")
 )