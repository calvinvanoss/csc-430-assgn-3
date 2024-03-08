#lang typed/racket

(require typed/rackunit)

(struct bind ([name : Symbol][val : Real]) #:transparent)
(define-type Env (Listof bind))

(struct storage ([loc : Real][val : Value]) #:transparent)
(define-type Store (Listof storage))

(struct result ([v : Value][s : Store]) #:transparent)

(define-type ExprC (U numC idC appC lamC strC condC seqC walrusC))
(struct numC ([n : Real]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct lamC ([args : (Listof Symbol)][body : ExprC]) #:transparent)
(struct appC ([fun : ExprC][args : (Listof ExprC)]) #:transparent)
(struct strC ([s : String]) #:transparent)
(struct condC ([i : ExprC][t : ExprC][e : ExprC]) #:transparent)
(struct seqC ([exprs : (Listof ExprC)]) #:transparent)
(struct walrusC ([s : Symbol][val : ExprC]) #:transparent)

(define-type Value (U numV closV Boolean primV String arrV nullV))
(struct numV ([n : Real]) #:transparent)
(struct closV ([args : (Listof Symbol)][body : ExprC][env : Env]) #:transparent)
(struct arrV ([loc : Real][len : Real]) #:transparent)
(struct primV ([op : Symbol]) #:transparent)
(define-type nullV '())

(define top-env (list
                 (bind 'true 0)
                 (bind 'false 1)
                 (bind '+ 2)
                 (bind '- 3)
                 (bind '* 4)
                 (bind '/ 5)
                 (bind '<= 6)
                 (bind 'error 7)
                 (bind 'println 8)
                 (bind 'read-num 9)
                 (bind '++ 10)
                 (bind 'num-eq? 11)
                 (bind 'str-eq? 12)
                 (bind 'arr-eq? 13)
                 (bind 'arr 14)
                 (bind 'aref 15)
                 (bind 'aset! 16)
                 (bind 'alen 17)
                 (bind 'substring 18)))

(define top-store (list
                   (storage 0 #t)
                   (storage 1 #f)
                   (storage 2 (primV '+))
                   (storage 3 (primV '-))
                   (storage 4 (primV '*))
                   (storage 5 (primV '/))
                   (storage 6 (primV '<=))
                   (storage 7 (primV 'error))
                   (storage 8 (primV 'println))
                   (storage 9 (primV 'readnum))
                   (storage 10 (primV '++))
                   (storage 11 (primV 'num-eq?))
                   (storage 12 (primV 'str-eq?))
                   (storage 13 (primV 'arr-eq?))
                   (storage 14 (primV 'arr))
                   (storage 15 (primV 'aref))
                   (storage 16 (primV 'aset!))
                   (storage 17 (primV 'alen))
                   (storage 18 (primV 'substring))))

; mutates a store at a given index to a given value
(: mutate (-> Store Real Value Store))
(define (mutate sto idx val)
  (match sto
    ['() (error "OAZO mutate: out of bounds index")]
    [(cons f r) (if (eq? idx (storage-loc f))
                    (cons (storage idx val) r)
                    (cons f (mutate r idx val)))]))

(check-equal? (mutate (list (storage 0 #t) (storage 1 #t) (storage 2 #t)) 1 #f) (list (storage 0 #t) (storage 1 #f) (storage 2 #t)))

; gets the next location in the store
(: next-loc (-> Store Real))
(define (next-loc sto)
  (match sto
    ['() 0]
    [else (+ (storage-loc (last sto)) 1)]))

(check-equal? (next-loc '()) 0)

; allocate new locations in the store
(: allocate (-> Store Real Value result))
(define (allocate sto n val)
  (let ([start (next-loc sto)]) (result (arrV start n) (append sto (map (lambda (idx) (storage (cast idx Real) val)) (range start (+ start n)))))))

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

; checks number equality
(: primopNum-eq? (-> Value Value Value))
(define (primopNum-eq? l r)
  (if (and (numV? l) (numV? r))
      (equal? (numV-n l) (numV-n r))
      (error "OAZO num-eq invalid input")))

; checks string equality
(: primopStr-eq? (-> Value Value Value))
(define (primopStr-eq? l r)
  (if (and (string? l) (string? r))
      (equal? l r)
      (error "OAZO str-eq invalid input")))

; checks array equality
(: primopArr-eq? (-> Value Value Value))
(define (primopArr-eq? l r)
  (if (and (arrV? l) (arrV? r))
      (equal? (arrV-loc l) (arrV-loc r))
      (error "OAZO arr-eq invalid input")))

#|
; prints string and then newline
(: primopPrintln (-> Value nullV))
(define (primopPrintln str)
  (if (string? str) (displayln str) (error "OAZO println expects a string"))
  '())

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
|#

; initializes an array of given length to a given default value
(: primopArr (-> Value Value Store result))
(define (primopArr size default sto)
  (if (and (numV? size) (numV? default))
      (allocate sto (numV-n size) default)
      (error "OAZO arr invalid arg")))

; return value in given array at given index
(: primopAref (-> Value Value Store result))
(define (primopAref arr idx sto)
  (if (and (arrV? arr) (numV? idx))
      (result (fetch (+ (arrV-loc arr) (numV-n idx)) sto) sto)
      (error "OAZO aref invalid arg")))

; sets the value at the given index of an array
(: primopAset! (-> Value Value Value Store result))
(define (primopAset! arr idx newval sto)
  (if (and (arrV? arr) (numV? idx))
      (result '() (mutate sto (+ (arrV-loc arr) (numV-n idx)) newval))
      (error "OAZO aset invalid arg")))

; returns length of array
(: primopAlen (-> Value Value))
(define (primopAlen arr)
  (if (arrV? arr)
      (numV (arrV-len arr))
      (error "OAZO alen invalid arg")))

; creates a substring
(: primopSubstring (-> Value Value Value Value))
(define (primopSubstring str start end)
  (if (and (string? str) (numV? start) (numV? end))
      (substring str (cast (numV-n start) Integer) (cast (numV-n end) Integer))
      (error "OAZO substring invalid arg")))

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
    [(list (? symbol? s) ':= val) (walrusC s (parse val))]
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

; lookup env variable and return its location
(: lookup (-> Symbol Env Real))
(define (lookup for env)
  (cond
    [(empty? env) (error "OAZO lookup: name not found")]
    [else (cond
            [(eq? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(check-exn (regexp (regexp-quote "OAZO lookup: name not found"))
           (lambda () (lookup 'a '())))

; fetch store value
(: fetch (-> Real Store Value))
(define (fetch loc sto)
  (match sto
    ['() (error "OAZO fetch: out of bounds index")]
    [(cons f r) (if (eq? loc (storage-loc f)) (storage-val f) (fetch loc r))]))

; interprets exprC to return Value
(: interp (-> ExprC Env Store result))
(define (interp exprc env sto)
  (match exprc
    [(numC n) (result (numV n) sto)]
    [(strC s) (result s sto)]
    [(idC n) (result (fetch (lookup n env) sto) sto)]
    [(lamC args body) (result (closV args body env) sto)]
    [(walrusC s val) (let ([res (interp val env sto)]) (result '() (mutate (result-s res) (lookup s env) (result-v res))))]
    [(condC i t e) (let* ([res (interp i env sto)][v (result-v res)][s (result-s res)])
                     (cond
                       [(equal? v #t) (interp t env s)]
                       [(equal? v #f) (interp e env s)]
                       [else (error "OAZO non boolean conditional")]))]
    [(seqC exprs) (match exprs
                    [(list end) (interp end env sto)]
                    [(cons f r) (let ([res (interp f env sto)]) (interp (seqC r) env (result-s res)))])]
    [(appC fun params) (let ([fd (interp fun env sto)])
                         (match (result-v fd)
                           [(numV n) (error "OAZO invalid appC")]
                           [(closV args body e)
                            (if (eq? (length args) (length params))
                                (let* ([param-results (foldl (lambda (param thread) (let ([res (interp (cast param ExprC) e (cast (rest (cast thread (Listof Any))) Store))])
                                                                                     (cons (append (cast (first (cast thread (Listof Any))) (Listof Any)) (cast (list (result-v res)) (Listof Any))) (result-s res))))
                                                            (cons '() sto)
                                                            params)]
                                       [extend-env (foldl (lambda (arg val thread) (let ([res (allocate (cast (rest (cast thread (Listof Any))) Store) 1 (cast val Value))])
                                                                                     (cons (append (cast (first (cast thread (Listof Any))) (Listof Any)) (cast (list (bind (cast arg Symbol) (arrV-loc (cast (result-v res) arrV)))) (Listof Any))) (result-s res))))
                                                   (cons '() (rest param-results))
                                                   args
                                                   (cast (first param-results) (Listof Any)))])
                                  (interp body (append e (cast (first extend-env) Env)) (cast (rest (cast extend-env (Listof Any))) Store)))
                                (error "OAZO incorrect number of arguments"))]
                           [(primV op) (match op
                                         ['+ (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primop+ (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['- (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primop- (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['* (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primop* (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['/ (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primop/ (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['<= (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primop<= (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['num-eq? (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primopNum-eq? (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['str-eq? (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primopStr-eq? (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['arr-eq? (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (result (primopArr-eq? (result-v r1) (result-v r2)) (result-s r2)))]
                                         ['error (error "OAZO user-error" (serialize (interp (first params) env sto)))]
                                         ['arr (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (primopArr (result-v r1) (result-v r2) (result-s r2)))]
                                         ['aref (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))]) (primopAref (result-v r1) (result-v r2) (result-s r2)))]
                                         ['aset! (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))][r3 (interp (first (rest (rest params))) env (result-s r2))]) (primopAset! (result-v r1) (result-v r2) (result-v r3) (result-s r3)))]
                                         ['alen (let ([res (interp (first params) env sto)]) (result (primopAlen (result-v res)) (result-s res)))]
                                         ['substring (let* ([r1 (interp (first params) env sto)][r2 (interp (first (rest params)) env (result-s r1))][r3 (interp (first (rest (rest params))) env (result-s r2))]) (result (primopSubstring (result-v r1) (result-v r2) (result-v r3)) (result-s r3)))])]))]))


; serialize Value into output string
(: serialize (-> result String))
(define (serialize res)
  (match (result-v res)
    [(numV n) (~v n)]
    [(? string? s) (~v s)]
    [#t "true"]
    [#f "false"]
    [(closV args body env) "#<procedure>"]
    [(primV op) "#<primop>"]
    [(arrV loc len) "#<array>"]
    ['() "null"]))

; top interp takes OAZO input and returns serialized output
(: top-interp (-> Sexp String))
(define (top-interp s)
  (serialize (interp (parse s) top-env top-store)))


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
(check-equal? (top-interp '{num-eq? 1 2}) "false")
(check-equal? (top-interp '{num-eq? 1 1}) "true")
(check-equal? (top-interp '{str-eq? "abc" "abc"}) "true")
(check-equal? (top-interp '{let
                               {x <- {arr 2 0}}
                             {arr-eq? x x}}) "true")
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
(check-equal? (top-interp '{seq {+ 1 2} {+ 3 4} {+ 5 6}}) "11")
#|
(check-equal? (top-interp '{println "abc"}) "null")
(check-exn (regexp (regexp-quote "OAZO println expects a string"))
           (lambda () (top-interp '{println 1})))
(check-equal? (top-interp '{read-num}) "1")
(check-exn (regexp (regexp-quote "OAZO read-num invalid input"))
           (lambda () (top-interp '{read-num})))
(check-equal? (top-interp '{read-num}) "-1")
(check-equal? (top-interp '{++ "a" 1 2 "b"}) "\"a12b\"")
|#

(check-equal? (top-interp '{arr 34 0}) "#<array>")
(check-equal? (top-interp '{let {x <- {arr 2 1}}
                             {aref x 1}}) "1")
(check-equal? (top-interp '{let {x <- {arr 2 1}}
                             {aset! x 1 false}}) "null")
(check-equal? (top-interp '{let {x <- {arr 2 1}}
                             {alen x}}) "2")
(check-equal? (top-interp '{let {x <- {arr 2 1}}
                             {seq
                              {aset! x 1 true}
                              {aref x 1}}}) "true")
(check-equal? (top-interp '{substring "abcdefg" 2 4}) "\"cd\"")
(check-equal? (top-interp '{let {x <- 1}
                             {seq
                              {x := 2}
                              x}}) "2")
