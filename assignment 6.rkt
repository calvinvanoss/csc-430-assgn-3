#lang typed/racket

(require typed/rackunit)

(struct bind ([name : Symbol][val : Value]) #:transparent)
(define-type Env (Listof bind))

(define-type ExprC (U numC idC appC lamC strC condC seqC))
(struct numC ([n : Real]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct lamC ([args : (Listof Symbol)][body : ExprC]) #:transparent)
(struct appC ([fun : ExprC][args : (Listof ExprC)]) #:transparent)
(struct strC ([s : String]) #:transparent)
(struct condC ([i : ExprC][t : ExprC][e : ExprC]) #:transparent)
(struct seqC ([exprs : (Listof ExprC)]) #:transparent)

(define-type Value (U numV closV Boolean primV String))
(struct numV ([n : Real]) #:transparent)
(struct closV ([args : (Listof Symbol)][body : ExprC][env : Env]) #:transparent)
(struct primV ([op : Symbol]) #:transparent)

(define top-env (list
                 (bind 'true #t)
                 (bind 'false #f)
                 (bind '+ (primV '+))
                 (bind '- (primV '-))
                 (bind '* (primV '*))
                 (bind '/ (primV '/))
                 (bind '<= (primV '<=))
                 (bind 'equal? (primV 'equal?))
                 (bind 'error (primV 'error))
                 (bind 'println (primV 'println))
                 (bind 'read-num (primV 'readnum))
                 (bind '++ (primV '++))))

; add 2 Values
(: primop+ (-> Value Value Value))
(define (primop+ l r)
  (cond
    [(and (numV? l) (numV? r))
     (numV (+ (numV-n l) (numV-n r)))]
    [else
     (error "OAZO + one argument was not a number")]))

(check-exn (regexp (regexp-quote "OAZO + one argument was not a number"))
           (lambda () (primop+ #f #t)))

; subtract 2 Values
(: primop- (-> Value Value Value))
(define (primop- l r)
  (cond
    [(and (numV? l) (numV? r))
     (numV (- (numV-n l) (numV-n r)))]
    [else
     (error "OAZO - one argument was not a number")]))

(check-exn (regexp (regexp-quote "OAZO - one argument was not a number"))
           (lambda () (primop- #f #t)))

; multiply 2 Values
(: primop* (-> Value Value Value))
(define (primop* l r)
  (cond
    [(and (numV? l) (numV? r))
     (numV (* (numV-n l) (numV-n r)))]
    [else
     (error "OAZO * one argument was not a number")]))

(check-exn (regexp (regexp-quote "OAZO * one argument was not a number"))
           (lambda () (primop* #f #t)))

; divide 2 Values
(: primop/ (-> Value Value Value))
(define (primop/ l r)
  (cond
    [(and (numV? r) (equal? (numV-n r) 0)) (error "OAZO divide by 0")]
    [(and (numV? l) (numV? r))
     (numV (/ (numV-n l) (numV-n r)))]
    [else
     (error "OAZO / one argument was not a number")]))

(check-exn (regexp (regexp-quote "OAZO / one argument was not a number"))
           (lambda () (primop/ #f #t)))
(check-exn (regexp (regexp-quote "OAZO divide by 0"))
           (lambda () (primop/ (numV 1) (numV 0))))

; less than or equal to
(: primop<= (-> Value Value Value))
(define (primop<= l r)
  (cond
    [(and (numV? l) (numV? r))
     (<= (numV-n l) (numV-n r))]
    [else
     (error "OAZO <= one argument was not a number")]))

(check-exn (regexp (regexp-quote "OAZO <= one argument was not a number"))
           (lambda () (primop<= #f #t)))

; checks equality
(: primopEqual? (-> Value Value Value))
(define (primopEqual? l r)
  (cond
    [(and (numV? l) (numV? r)) (equal? (numV-n l) (numV-n r))]
    [(and (boolean? l) (boolean? r)) (equal? l r)]
    [(and (string? l) (string? r)) (equal? l r)]
    [else #f]))

; prints string and then newline
(: primopPrintln (-> Value Boolean))
(define (primopPrintln str)
  (if (string? str) (displayln str) (error "OAZO println expects a string"))
  #t)

; prompts user and then records number input
(: primopRead-num (-> numV))
(define (primopRead-num)
  (write ">")
  (let ([input (read-line)])
    (if (string? input)
        (let ([convert (string->number (cast input String))])
          (if (real? convert) (numV convert) (error "OAZO read-num invalid input")))
        (numV -1))))

; concatenates values into a string
(: primop++ (-> (Listof Value) String))
(define (primop++ l)
  (match l
    [(cons f r) (match f
                  [(numV n) (string-append (number->string n) (primop++ r))]
                  [string (string-append (cast f String) (primop++ r))])]
    ['() ""]))

; desugar local variable names
(: desugar-ids (-> Sexp Symbol))
(define (desugar-ids l)
  (match l
    [(list id '<- _) (if (or
                          (equal? id 'if)
                          (equal? id 'then)
                          (equal? id 'else)
                          (equal? id '<-)
                          (equal? id 'anon)
                          (equal? id ':))
                         (error "OAZO invalid local assignment")
                         (cast id Symbol))]))

; desugar local variable values
(: desugar-exprs (-> Sexp ExprC))
(define (desugar-exprs l)
  (match l
    [(list _ '<- exp) (parse exp)]))


; parse Sexp to ExprC
(: parse (-> Sexp ExprC))
(define (parse exp)
  (match exp
    [(list 'let vars ... body) (let ([ids (map (lambda (i) (desugar-ids (cast i Sexp))) vars)]
                                     [exprs (map (lambda (e) (desugar-exprs (cast e Sexp))) vars)])
                                 (if (check-duplicates ids)
                                     (error "OAZO duplicate local assignment")
                                     (appC (lamC ids (parse body)) exprs)))]
    [(list 'seq exprs ...) (seqC (map parse exprs))]
    [(? real? n) (numC n)]
    [(? symbol? s) (if (or
                        (equal? s 'if)
                        (equal? s 'then)
                        (equal? s 'else)
                        (equal? s '<-)
                        (equal? s 'anon)
                        (equal? s ':))
                       (error "OAZO parse known symbol")
                       (idC s))]
    [(list 'if i 'then t 'else e) (condC (parse i) (parse t) (parse e))]
    [(list 'anon (list (? symbol? args) ...) ': body) (if (check-duplicates args)
                                                          (error "OAZO duplicate args")
                                                          (lamC (cast args (Listof Symbol)) (parse body)))]
    [(list fun args ...) (appC (parse fun) (map (lambda (arg) (parse arg)) args))]
    [(? string? s) (strC s)]))


(check-exn (regexp (regexp-quote "OAZO parse known symbol"))
           (lambda () (parse '{if})))
(check-exn (regexp (regexp-quote "OAZO duplicate args"))
           (lambda () (parse '{anon {x x} : 1})))

; lookup env variable
(: lookup (-> Symbol Env Value))
(define (lookup for env)
  (cond
    [(empty? env) (error "OAZO lookup: name not found")]
    [else (cond
            [(eq? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(check-exn (regexp (regexp-quote "OAZO lookup: name not found"))
           (lambda () (lookup 'a '())))


; interprets exprC to return Value
(: interp (-> ExprC Env Value))
(define (interp exprc env)
  (match exprc
    [(numC n) (numV n)]
    [(strC s) s]
    [(idC n) (lookup n env)]
    [(lamC args body) (closV args body env)]
    [(condC i t e) (let ([res (interp i env)])
                     (cond
                       [(equal? res #t) (interp t env)]
                       [(equal? res #f)(interp e env)]
                       [else (error "OAZO non boolean conditional")]))]
    [(seqC exprs) (match exprs
                    [(list end) (interp end env)]
                    [(cons f r) (let ([execute: (interp f env)]) (interp (seqC r) env))])]
    [(appC fun params) (let ([fd (interp fun env)])
                         (match fd
                           [(numV n) (error "OAZO invalid appC")]
                           [(closV args body e)
                            (if (eq? (length args) (length params))
                                (interp body (append (map (lambda (arg param)
                                                            (bind (cast arg Symbol)
                                                                  (interp (cast param ExprC) env))) args params) e))
                                (error "OAZO incorrect number of arguments"))]
                           [(primV op) (match op
                                         ['+ (primop+ (interp (first params) env) (interp (first (rest params)) env))]
                                         ['- (primop- (interp (first params) env) (interp (first (rest params)) env))]
                                         ['* (primop* (interp (first params) env) (interp (first (rest params)) env))]
                                         ['/ (primop/ (interp (first params) env) (interp (first (rest params)) env))]
                                         ['<= (primop<= (interp (first params) env) (interp (first (rest params)) env))]
                                         ['equal? (primopEqual?
                                                   (interp (first params) env)
                                                   (interp (first (rest params)) env))]
                                         ['println (primopPrintln (interp (first params) env))]
                                         ['readnum (primopRead-num)]
                                         ['++ (primop++ (map (lambda (param) (interp (cast param ExprC) env)) params))]
                                         ['error (error "OAZO user-error"
                                                        (serialize (interp (first params) env)))])]))]))


; serialize Value into output string
(: serialize (-> Value String))
(define (serialize value)
  (match value
    [(numV n) (~v n)]
    [(? string? s) (~v s)]
    [#t "true"]
    [#f "false"]
    [(closV args body env) "#<procedure>"]
    [(primV op) "#<primop>"]))

; top interp takes OAZO input and returns serialized output
(: top-interp (-> Sexp String))
(define (top-interp s)
  (serialize (interp (parse s) top-env)))

(check-equal? (parse '{anon {z} : z}) (lamC '(z) (idC 'z)))
(check-equal? (parse '{+ 3 4}) (appC (idC '+) (list (numC 3) (numC 4))))
(check-equal? (parse '{{anon {z} : z} 1}) (appC (lamC '(z) (idC 'z)) (list (numC 1))))
(check-equal? (parse '{{anon {z y} : {+ z y}}
                       23 98})
              (appC (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y)))) (list (numC 23) (numC 98))))
(check-equal? (top-interp '{+ 3 4}) "7")
(check-equal? (top-interp 'false) "false")
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp '{anon {z} : {z}}) "#<procedure>")
(check-equal? (top-interp '{anon {z} : {+ z 10}}) "#<procedure>")
(check-equal? (top-interp '{{anon {z} : z} 1}) "1")
(check-equal? (top-interp '{* 3 4}) "12")
(check-equal? (top-interp '{{anon {z y} : {+ z y}} {+ 9 14} 98}) "121")
(check-equal? (top-interp '{- 2 1}) "1")
(check-equal? (top-interp '{/ 4 2}) "2")
(check-equal? (top-interp '{<= 4 2}) "false")
(check-equal? (top-interp '{<= 2 4}) "true")
(check-equal? (top-interp '3) "3")
(check-equal? (top-interp '"abcd") "\"abcd\"")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '{equal? 1 2}) "false")
(check-equal? (top-interp '{equal? {anon {a} : 1} {anon {a} : 1}}) "false")
(check-equal? (top-interp '{equal? 1 1}) "true")
(check-equal? (top-interp '{equal? "abc" "abc"}) "true")
(check-equal? (top-interp '{equal? false false}) "true")
(check-equal? (top-interp '{if true then 3 else 4}) "3")
(check-equal? (top-interp '{if false then 3 else 4}) "4")
(check-equal? (top-interp '{let
                               {z <- {+ 9 14}}
                             {y <- 98}
                             {+ z y}}) "121")
(check-exn (regexp (regexp-quote "OAZO incorrect number of arguments"))
           (lambda () (top-interp '{{anon {a b} : 1} 1})))
(check-exn (regexp (regexp-quote "OAZO non boolean conditional"))
           (lambda () (top-interp '{if 3 then 4 else 5})))
(check-exn (regexp (regexp-quote "OAZO invalid appC"))
           (lambda () (top-interp '(3 4 5))))
(check-exn (regexp (regexp-quote "OAZO duplicate local assignment"))
           (lambda () (parse '(let (z <- (anon () : 3)) (z <- 9) (z)))))
(check-exn (regexp (regexp-quote "OAZO user-error \"\\\"1234\\\"\""))
           (lambda () (top-interp '(+ 4 (error "1234")))))
(check-exn (regexp (regexp-quote "OAZO invalid local assignment"))
           (lambda () (parse '(let (: <- "") "World"))))
(check-equal? (top-interp '{println "abc"}) "true")
(check-exn (regexp (regexp-quote "OAZO println expects a string"))
           (lambda () (top-interp '{println 1})))
(check-equal? (top-interp '{read-num}) "1")
(check-exn (regexp (regexp-quote "OAZO read-num invalid input"))
           (lambda () (top-interp '{read-num})))
(check-equal? (top-interp '{read-num}) "-1")
(check-equal? (top-interp '{++ "a" 1 2 "b"}) "\"a12b\"")
(check-equal? (top-interp '{seq {+ 1 2} {+ 3 4} {+ 5 6}}) "11")


; example program - simple calculator
(top-interp '{seq
              {println "enter a number"}
              {let {x <- {read-num}}
                {seq
                 {println "enter operation:"}
                 {println "0 for +"}
                 {println "1 for -"}
                 {println "2 for *"}
                 {println "3 for /"}
                 {let {op <- {read-num}}
                   {seq
                    {println "enter another number"}
                    {let {y <- {read-num}}
                      {seq
                       {println "result:"}
                       {if {equal? op 0} then {+ x y}
                           else {if {equal? op 1} then {- x y}
                                    else {if {equal? op 2} then {* x y}
                                             else {if {equal? op 3} then {/ x y}
                                                      else "error invalid operator"}}}}}}}}}}})

