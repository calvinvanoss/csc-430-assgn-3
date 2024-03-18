#lang typed/racket

(require typed/rackunit)

(struct bind ([name : Symbol][val : Real]) #:transparent)
(define-type Env (Listof bind))

(struct storage ([loc : Real][val : Value]) #:transparent)
(define-type Store (Listof storage))

(struct result ([v : Value][s : Store]) #:transparent)

(define-type ExprC (U numC idC appC lamC strC condC seqC walrusC Type))
(struct numC ([n : Real]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct lamC ([args : (Listof Symbol)][argsT : (Listof Type)][body : ExprC]) #:transparent)
(struct appC ([fun : ExprC][args : (Listof ExprC)]) #:transparent)
(struct strC ([s : String]) #:transparent)
(struct condC ([i : ExprC][t : ExprC][e : ExprC]) #:transparent)
(struct seqC ([exprs : (Listof ExprC)]) #:transparent)
(struct walrusC ([s : Symbol][val : ExprC]) #:transparent)

(define-type Type (U numT boolT strT voidT funT arrT))
(struct numT () #:transparent)
(struct boolT () #:transparent)
(struct strT () #:transparent)
(struct voidT () #:transparent)
(struct funT ([argsT : (Listof Type)][retT : Type]) #:transparent)
(struct arrT () #:transparent)

(define-type Value (U numV closV Boolean primV String arrV voidV))
(struct numV ([n : Real]) #:transparent)
(struct closV ([args : (Listof Symbol)][body : ExprC][env : Env]) #:transparent)
(struct arrV ([loc : Real][len : Real]) #:transparent)
(struct primV ([op : Symbol]) #:transparent)
(struct voidV () #:transparent)

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
                 (bind 'aset 16)
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
                   (storage 16 (primV 'aset))
                   (storage 17 (primV 'alen))
                   (storage 18 (primV 'substring))))

(struct bindT ([name : Symbol][type : Type]))
(define-type TEnv (Listof bindT))

(define base-tenv (list
                   (bindT 'true (boolT))
                   (bindT 'false (boolT))
                   (bindT '+ (funT (list (numT) (numT)) (numT)))
                   (bindT '- (funT (list (numT) (numT)) (numT)))
                   (bindT '* (funT (list (numT) (numT)) (numT)))
                   (bindT '/ (funT (list (numT) (numT)) (numT)))
                   (bindT '<= (funT (list (numT) (numT)) (boolT)))
                   (bindT 'num-eq? (funT (list (numT) (numT)) (boolT)))
                   (bindT 'str-eq? (funT (list (strT) (strT)) (boolT)))
                   (bindT 'arr-eq? (funT (list (arrT) (arrT)) (boolT)))
                   (bindT 'arr (funT (list (numT) (numT)) (arrT)))
                   (bindT 'aref (funT (list (arrT) (numT)) (numT)))
                   (bindT 'aset (funT (list (arrT) (numT) (numT)) (voidT)))
                   (bindT 'alen (funT (list (arrT)) (numT)))
                   (bindT 'substring (funT (list (strT) (numT) (numT)) (strT)))))

; lookup binding in type environment
(: lookup-type (-> Symbol TEnv Type))
(define (lookup-type for env)
  (cond
    [(empty? env) (error "OAZO type lookup not found")]
    [else (cond
            [(eq? for (bindT-name (first env)))
             (bindT-type (first env))]
            [else (lookup-type for (rest env))])]))

(check-exn (regexp (regexp-quote "OAZO type lookup not found"))
           (lambda () (lookup-type 'a '())))

; catch type errors on AST
(: type-check (-> ExprC TEnv Type))
(define (type-check exp env)
  (match exp
    [(numC n) (numT)]
    [(strC s) (strT)]
    [(idC s) (lookup-type s env)]
    [(lamC args types body)
     (funT types (type-check body (append (map (lambda (arg type) (bindT arg type)) args types) env)))]
    [(walrusC s val) (voidT)]
    [(condC i t e) (if (equal? (type-check i env) (boolT))
                       (if (equal? (type-check t env) (type-check e env))
                           (type-check t env)
                           (error "OAZO type-check: mismatched types in conditional"))
                       (error "OAZO type-check: non-boolean conditional"))]
    [(seqC exprs) (if (empty? exprs)
                      (error "OAZO type-check: seq must have at least 1 arg")
                      (type-check (last exprs) env))]
    [(appC fun params) (let ([fd (type-check fun env)])
                         (match fd
                           [(funT argsT retT)
                            (if (equal? (length argsT) (length params))
                                (if (andmap
                                     (lambda (arg param) (equal? arg (type-check (cast param ExprC) env)))
                                     argsT params)
                                    retT
                                    (error "OAZO type-check: mismatched types in function application"))
                                (error "OAZO incorrect number of args"))]
                           [else (error "OAZO type-check: non-function application")]))]))


; mutates a store at a given index to a given value
(: mutate (-> Store Real Value Store))
(define (mutate sto idx val)
  (match sto
    ['() (error "OAZO mutate: out of bounds index")]
    [(cons f r) (if (eq? idx (storage-loc f))
                    (cons (storage idx val) r)
                    (cons f (mutate r idx val)))]))

(check-equal? (mutate (list (storage 0 #t) (storage 1 #t) (storage 2 #t)) 1 #f)
              (list (storage 0 #t) (storage 1 #f) (storage 2 #t)))
(check-exn (regexp (regexp-quote "OAZO mutate: out of bounds index"))
           (lambda () (mutate top-store 30 "abc")))

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
  (let ([start (next-loc sto)])
    (result (arrV start n)
            (append sto (map (lambda (idx) (storage (cast idx Real) val)) (range start (+ start n)))))))

; add 2 Values
(: primop+ (-> Value Value Value))
(define (primop+ l r)
  (numV (+ (numV-n (cast l numV)) (numV-n (cast r numV)))))


; subtract 2 Values
(: primop- (-> Value Value Value))
(define (primop- l r)
  (numV (- (numV-n (cast l numV)) (numV-n (cast r numV)))))

; multiply 2 Values
(: primop* (-> Value Value Value))
(define (primop* l r)
  (numV (* (numV-n (cast l numV)) (numV-n (cast r numV)))))

; divide 2 Values
(: primop/ (-> Value Value Value))
(define (primop/ l r)
  (if (equal? (numV-n (cast r numV)) 0)
      (error "OAZO divide by 0")
      (numV (/ (numV-n (cast l numV)) (numV-n (cast r numV))))))

(check-exn (regexp (regexp-quote "OAZO divide by 0"))
           (lambda () (primop/ (numV 1) (numV 0))))

; less than or equal to
(: primop<= (-> Value Value Value))
(define (primop<= l r)
  (<= (numV-n (cast l numV)) (numV-n (cast r numV))))

; checks number equality
(: primopNum-eq? (-> Value Value Value))
(define (primopNum-eq? l r)
  (equal? (numV-n (cast l numV)) (numV-n (cast r numV))))

; checks string equality
(: primopStr-eq? (-> Value Value Value))
(define (primopStr-eq? l r)
  (equal? l r))

; checks array equality
(: primopArr-eq? (-> Value Value Value))
(define (primopArr-eq? l r)
  (equal? (arrV-loc (cast l arrV)) (arrV-loc (cast r arrV))))

; initializes an array of given length to a given default value
(: primopArr (-> Value Value Store result))
(define (primopArr size default sto)
  (allocate sto (numV-n (cast size numV)) default))

; return value in given array at given index
(: primopAref (-> Value Value Store result))
(define (primopAref arr idx sto)
  (result (fetch (+ (arrV-loc (cast arr arrV)) (numV-n (cast idx numV))) sto) sto))

; sets the value at the given index of an array
(: primopAset (-> Value Value Value Store result))
(define (primopAset arr idx newval sto)
  (result (voidV) (mutate sto (+ (arrV-loc (cast arr arrV)) (numV-n (cast idx numV))) newval)))

; returns length of array
(: primopAlen (-> Value Value))
(define (primopAlen arr)
  (numV (arrV-len (cast arr arrV))))

; creates a substring
(: primopSubstring (-> Value Value Value Value))
(define (primopSubstring str start end)
  (substring (cast str String) (cast (numV-n (cast start numV)) Integer) (cast (numV-n (cast end numV)) Integer)))

; desugar local variable names
(: desugar-ids (-> Sexp Symbol))
(define (desugar-ids exp)
  (match exp
    [(list (list id ': _) '<- _) (if (or
                                      (equal? id 'let)
                                      (equal? id ':=)
                                      (equal? id 'if)
                                      (equal? id 'then)
                                      (equal? id 'else)
                                      (equal? id ':)
                                      (equal? id '<-)
                                      (equal? id 'seq))
                                     (error "OAZO invalid local assignment id")
                                     (cast id Symbol))]
    [else (error "OAZO invalid let assignment")]))

(check-exn (regexp (regexp-quote "OAZO invalid let assignment"))
           (lambda () (desugar-ids '{})))

; desugar local variable values
(: desugar-exprs (-> Sexp ExprC))
(define (desugar-exprs exp)
  (match exp
    [(list _ '<- exp) (parse exp)]))

; desugar local variable types
(: desugar-types (-> Sexp Type))
(define (desugar-types exp)
  (match exp
    [(list (list _ ': type) '<- _) (parse-type type)]))

; parse Sexp into type
(: parse-type (-> Sexp Type))
(define (parse-type exp)
  (match exp
    ['num (numT)]
    ['bool (boolT)]
    ['str (strT)]
    ['void (voidT)]
    ['numarray (arrT)]
    [(list args ... '-> ret) (funT (map (lambda (arg) (parse-type (cast arg Sexp))) args) (parse-type ret))]
    [else (error "OAZO unknown type")]))


; parse Sexp to ExprC
(: parse (-> Sexp ExprC))
(define (parse exp)
  (match exp
    [(list (? symbol? s) ':= val) (walrusC s (parse val))]
    [(list 'let vars ... body) (let ([ids (map (lambda (i) (desugar-ids (cast i Sexp))) vars)]
                                     [types (map (lambda (t) (desugar-types (cast t Sexp))) vars)]
                                     [exprs (map (lambda (e) (desugar-exprs (cast e Sexp))) vars)])
                                 (if (check-duplicates ids)
                                     (error "OAZO duplicate local assignment")
                                     (appC (lamC ids types (parse body)) exprs)))]
    [(list 'seq exprs ...) (seqC (map parse exprs))]
    [(? real? n) (numC n)]
    [(? symbol? s) (if (or
                        (equal? s 'let)
                        (equal? s ':=)
                        (equal? s 'if)
                        (equal? s 'then)
                        (equal? s 'else)
                        (equal? s ':)
                        (equal? s '<-)
                        (equal? s 'seq))
                       (error "OAZO invalid symbol")
                       (idC s))]
    [(list 'if i 'then t 'else e) (condC (parse i) (parse t) (parse e))]
    [(list 'anon (list (? list? args) ...) ': body)
     (let
         ([params (map (lambda (arg)  (first (rest (cast arg (Listof Any))))) args)]
          [types (map (lambda (arg) (parse-type (cast (first (cast arg (Listof Any))) Sexp))) args)])
       (if (check-duplicates params)
           (error "OAZO duplicate args")
           (lamC (cast params (Listof Symbol)) (cast types (Listof Type)) (parse body))))]
    [(list fun args ...) (appC (parse fun) (map (lambda (arg) (parse arg)) args))]
    [(? string? s) (strC s)]))

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
    ['() (error "OAZO fetch: out of bounds index" loc)]
    [(cons f r) (if (eq? loc (storage-loc f)) (storage-val f) (fetch loc r))]))

(check-exn (regexp (regexp-quote "OAZO fetch: out of bounds index"))
           (lambda () (fetch 30 top-store)))

; recursively interp all the params of an appC while threading the store
(: interp-params (-> (Listof ExprC) Env Store (Listof result)))
(define (interp-params params env sto)
  (if (empty? params)
      '()  ; return an empty list when there are no more parameters
      (let ([res (interp (first params) env sto)])
        (cons res (interp-params (rest params) env (result-s res))))))  ; prepend the result to the rest of the results

; recursively add all args to store
(: thread-params (-> (Listof Value) Store Store))
(define (thread-params args sto)
  (if (empty? args) sto
      (thread-params (rest args) (result-s (allocate sto 1 (cast (first args) Value))))))


; interprets exprC to return Value
(: interp (-> ExprC Env Store result))
(define (interp exprc env sto)
  (match exprc
    [(numC n) (result (numV n) sto)]
    [(strC s) (result s sto)]
    [(idC n) (result (fetch (lookup n env) sto) sto)]
    [(lamC args types body) (result (closV args body env) sto)]
    [(walrusC s val)
     (let ([res (interp val env sto)]) (result (voidV) (mutate (result-s res) (lookup s env) (result-v res))))]
    [(condC i t e) (let* ([res (interp i env sto)][v (result-v res)][s (result-s res)])
                     (if v (interp t env s) (interp e env s)))]
    [(seqC exprs) (match exprs
                    [(list end) (interp end env sto)]
                    [(cons f r) (let ([res (interp f env sto)]) (interp (seqC r) env (result-s res)))])]
    [(appC fun params) (let ([fd (interp fun env sto)])
                         (match (result-v fd)
                           [(closV args body e)
                            (let* ([param-results (interp-params params env (result-s fd))]
                                   [param-values (map (lambda (res) (result-v res)) param-results)]
                                   [param-results-sto (if (equal? param-results '())
                                                          (result-s fd)
                                                          (result-s (last param-results)))]
                                   [extend-env
                                    (append
                                     e
                                     (map (lambda (arg idx) (bind (cast arg Symbol) (cast idx Real)))
                                          args
                                          (range
                                           (length param-results-sto)
                                           (+ (length param-results-sto) (length args)))))]
                                   [extend-sto (thread-params param-values param-results-sto)])
                              (interp body extend-env extend-sto))]
                           [(primV op)
                            (match op
                              ['+ (let* ([r1 (interp (first params) env sto)]
                                         [r2 (interp (first (rest params)) env (result-s r1))])
                                    (result (primop+ (result-v r1) (result-v r2)) (result-s r2)))]
                              ['- (let* ([r1 (interp (first params) env sto)]
                                         [r2 (interp (first (rest params)) env (result-s r1))])
                                    (result (primop- (result-v r1) (result-v r2)) (result-s r2)))]
                              ['* (let* ([r1 (interp (first params) env sto)]
                                         [r2 (interp (first (rest params)) env (result-s r1))])
                                    (result (primop* (result-v r1) (result-v r2)) (result-s r2)))]
                              ['/ (let* ([r1 (interp (first params) env sto)]
                                         [r2 (interp (first (rest params)) env (result-s r1))])
                                    (result (primop/ (result-v r1) (result-v r2)) (result-s r2)))]
                              ['<= (let* ([r1 (interp (first params) env sto)]
                                          [r2 (interp (first (rest params)) env (result-s r1))])
                                     (result (primop<= (result-v r1) (result-v r2)) (result-s r2)))]
                              ['num-eq?
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))])
                                 (result (primopNum-eq? (result-v r1) (result-v r2)) (result-s r2)))]
                              ['str-eq?
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))])
                                 (result (primopStr-eq? (result-v r1) (result-v r2)) (result-s r2)))]
                              ['arr-eq?
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))])
                                 (result (primopArr-eq? (result-v r1) (result-v r2)) (result-s r2)))]
                              ['arr
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))])
                                 (primopArr (result-v r1) (result-v r2) (result-s r2)))]
                              ['aref
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))])
                                 (primopAref (result-v r1) (result-v r2) (result-s r2)))]
                              ['aset
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))]
                                      [r3 (interp (first (rest (rest params))) env (result-s r2))])
                                 (primopAset (result-v r1) (result-v r2) (result-v r3) (result-s r3)))]
                              ['alen
                               (let ([res (interp (first params) env sto)])
                                 (result (primopAlen (result-v res)) (result-s res)))]
                              ['substring
                               (let* ([r1 (interp (first params) env sto)]
                                      [r2 (interp (first (rest params)) env (result-s r1))]
                                      [r3 (interp (first (rest (rest params))) env (result-s r2))])
                                 (result
                                  (primopSubstring (result-v r1) (result-v r2) (result-v r3))
                                  (result-s r3)))])]))]))


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
    [(voidV) "null"]))

; top interp takes OAZO input and returns serialized output
(: top-interp (-> Sexp String))
(define (top-interp s)
  (let ([expr (parse s)])
    (type-check expr base-tenv)
    (serialize (interp expr top-env top-store))))



(check-equal? (parse '{anon {[num z]} : z}) (lamC '(z) (list (numT)) (idC 'z)))
(check-equal? (parse '{+ 3 4}) (appC (idC '+) (list (numC 3) (numC 4))))
(check-equal? (parse '{{anon {[num z]} : z} 1}) (appC (lamC '(z) (list (numT)) (idC 'z)) (list (numC 1))))
(check-equal? (parse '{{anon {[num z][num y]} : {+ z y}} 23 98})
              (appC
               (lamC '(z y) (list (numT) (numT)) (appC (idC '+) (list (idC 'z) (idC 'y))))
               (list (numC 23) (numC 98))))
(check-equal? (top-interp '{+ 3 4}) "7")
(check-equal? (top-interp 'false) "false")
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp '{anon {[num z]} : z}) "#<procedure>")
(check-equal? (top-interp '{anon {[num z]} : {+ z 10}}) "#<procedure>")
(check-equal? (top-interp '{{anon {[num z]} : z} 1}) "1")
(check-equal? (top-interp '{* 3 4}) "12")
(check-equal? (top-interp '{{anon {[num z][num y]} : {+ z y}} {+ 9 14} 98}) "121")
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
                               {[x : numarray] <- {arr 2 0}}
                             {arr-eq? x x}}) "true")
(check-equal? (top-interp '{if true then 3 else 4}) "3")
(check-equal? (top-interp '{if false then 3 else 4}) "4")
(check-equal? (top-interp '{let
                               {[z : num] <- {+ 9 14}}
                             {[y : num] <- 98}
                             {+ z y}}) "121")
(check-equal? (top-interp '{seq {+ 1 2} {+ 3 4} {+ 5 6}}) "11")
(check-equal? (top-interp '{arr 34 0}) "#<array>")

(check-equal? (top-interp '{let {[x : numarray] <- {arr 2 1}}
                             {aref x 1}}) "1")
(check-equal? (top-interp '{let {[x : numarray] <- {arr 2 1}}
                             {aset x 1 2}}) "null")
(check-equal? (top-interp '{let {[x : numarray] <- {arr 2 1}}
                             {alen x}}) "2")
(check-equal? (top-interp '{let {[x : numarray] <- {arr 2 1}}
                             {seq
                              {aset x 1 true}
                              {aref x 1}}}) "true")
(check-equal? (top-interp '{substring "abcdefg" 2 4}) "\"cd\"")
(check-equal? (top-interp '{let {[x : num] <- 1}
                             {seq
                              {x := 2}
                              x}}) "2")
(check-equal? (top-interp '{let
                               {[x : num] <- 2}
                             {{anon {[num y]} : {x := y}} 3}}) "null")
(check-exn (regexp (regexp-quote "OAZO type-check: mismatched types in conditional"))
           (lambda () (top-interp '{if true then 1 else false})))
(check-exn (regexp (regexp-quote "OAZO type-check: non-boolean conditional"))
           (lambda () (top-interp '{if 1 then 1 else 2})))
(check-exn (regexp (regexp-quote "OAZO type-check: seq must have at least 1 arg"))
           (lambda () (top-interp '{seq})))
(check-exn (regexp (regexp-quote "OAZO type-check: mismatched types in function application"))
           (lambda () (top-interp '{{anon {[num z]} : z} "abc"})))
(check-exn (regexp (regexp-quote "OAZO type-check: non-function application"))
           (lambda () (top-interp '{1 2 3})))
(check-exn (regexp (regexp-quote "OAZO invalid local assignment id"))
           (lambda () (top-interp '{let {[: : str] <- "abc"} 1})))
(check-equal? (top-interp '{{anon {[bool b]} : b} true}) "true")
(check-equal? (top-interp '{{anon {[str s]} : s} "abc"}) "\"abc\"")
(check-equal? (top-interp '{let {[x : numarray] <- {arr 2 1}}
                             {anon {[void v]} : {aset x 1 3}}}) "#<procedure>")
(check-equal? (top-interp '{let {[f : {num num -> num}] <- {anon {[num x][num y]} : {+ x y}}}
                             {f 1 1}}) "2")
(check-exn (regexp (regexp-quote "OAZO unknown type"))
           (lambda () (top-interp '{let {[x : unknown] <- 1} 1})))
(check-exn (regexp (regexp-quote "OAZO duplicate local assignment"))
           (lambda () (top-interp '{let {[x : num] <- 1} {[x : num] <- 2} 1})))
(check-exn (regexp (regexp-quote "OAZO duplicate args"))
           (lambda () (top-interp '{anon {[num z][num z]} : z})))
(check-exn (regexp (regexp-quote "OAZO incorrect number of args"))
           (lambda () (top-interp '{{anon {[num x][num y]} : 1} 1})))
(check-exn (regexp (regexp-quote "OAZO invalid symbol"))
           (lambda () (top-interp '{+ let 1})))
(check-equal? (top-interp '{{anon () : 9}}) "9")

