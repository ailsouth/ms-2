#lang play

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}
         | {match <expr> <case>+}
<case> ::= {'case <pattern> '=> <expr>}
<pattern> ::= <num>
         | <bool>
         | <string>
         | <id>
         | (<constr-id> <attr-id>*)
<def>  ::= {define <id> <expr>}
         | {datatype <typename> <type-constructor>*}}
<type-constructor> ::= {<id> <member>*}
<constr-id> :: = <id>
<attr-id> :: = <id>
<typename> :: = <id>
<member>   :: = <id>
|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim-app name args)   ; aplicación de primitivas
  (fun id body)
  (lcal defs body)
  (mtch val cases))

; definiciones
(deftype Def
  (dfine name val-expr) ; define
  (datatype name variants)) ; datatype

; variantes
(deftype Variant
  (variant name params))

; estructuras de datos
(deftype Struct
  (structV name variant values))

; caso en pattern matching
(deftype Case
  (cse pattern body))

; patrón
(deftype Pattern
  (idP id) ; identificador
  (litP l) ; valor literal 
  (constrP ctr patterns)) ; constructor y sub-patrones






;; parse :: s-expr -> Expr
(define(parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? symbol?) (id s-expr)]    
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))] 
    [(list 'match val-expr cases ...) ; note the elipsis to match n elements
     (mtch (parse val-expr) (map parse-case cases))] ; cases is a list
    [(list 'list  a ...)    (if (= 1 (length a))                               ;MINE
                                (app (id 'Cons) (list (parse (car a)) (app (id 'Empty) '())))
                                (app (id 'Cons) (list (parse (car a)) (parse (cons 'list (cdr a)))))
                                )]
    [(list f args ...) ; same here
     (if (assq f *primitives*)
         (prim-app f (map parse args)) ; args is a list
         (app (parse f) (map parse args)))]))





(define (alist p)                                                              ;MINE        
  (match p
    [(cons a b) (constrP 'Cons (list (parse-pattern a) (alist b)))]
    [else (constrP 'Empty '())]
    ))



; parse-def :: s-expr -> Def
(define(parse-def s-expr)
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'datatype name variants ...) (datatype name (map parse-variant variants))]))

; parse-variant :: sexpr -> Variant
(define(parse-variant v)
  (match v
    [(list name params ...) (variant name params)]))

; parse-case :: sexpr -> Case
(define(parse-case c)
  (match c
    [(list 'case pattern => body) (cse (parse-pattern pattern) (parse body))]))

; parse-pattern :: sexpr -> Pattern
(define(parse-pattern p)  
  (match p
    [(? symbol?)  (idP p)]
    [(? number?)  (litP (num p))]
    [(? boolean?) (litP (bool p))]
    [(? string?)  (litP (str p))]                                        ;MINE

    [(list 'list pattern ...) (alist pattern)]

    [(list ctr patterns ...) (constrP (first p) (map parse-pattern patterns))]))








#;(define (strict e)                                        ;MINE
  (match e
    [(exprV expr env) (strict (interp expr env))]
    [else e]))



(define (strict e)
  (match e
    [(exprV expr env cache)
     (if (not (unbox cache))
         (local ([def val (strict (interp expr env))])
           ;(printf "Forcing exprV to ~v~n" val)
           (set-box! cache val)
           val)
         (begin
           ;(printf "Using cached value~v~n" (unbox cache))
           (unbox cache)))]
    [else e]))



;; lazyVal
(deftype Val                                        ;MINE
  (exprV expr env cache))

(deftype isLazyExpr
  (lexpr exp bool)
  )

(define (lazyList fun-expr)
  (match fun-expr
    [ (fun id body) (map (lambda (i) (match i
                                       [(list 'lazy x) #t]
                                       [else #f])) id)]
    [else #f]
    )
  )

(define (deleteLazy idList)                                        ;MINE
  (match idList
    [(cons (list 'lazy a) b) (cons a (deleteLazy b))]
    [(cons a b) (cons a (deleteLazy b))]
    [else '()]
   ))


(define (replaceLazy fun-expr)                                        ;MINE
  (match fun-expr
    [ (fun id body) (fun (deleteLazy id) body)]
    [else fun-expr] 
    )
  )



(define (matchLazy expr env )                                        ;MINE
  ;(println expr)
   (if (lexpr-bool expr)
       (exprV (lexpr-exp expr) env (box #f))
       (interp (lexpr-exp expr) env) )
  )




(define (lazyTuplas aelist llist)
;  (println llist)
  (def nllist (if (or (equal? llist '())
                      (equal? llist #f))
                  (list #f #f )
                  llist))
  (match aelist
    [(cons a b) (cons (lexpr a (car nllist)) (lazyTuplas b (cdr nllist)))]
    [else '()]
    )
  )


(define  (lazyApp fun-expr arg-expr-list env )                                         ;MINE

  (def Newfun-expr (replaceLazy fun-expr))
  (def llist (lazyList fun-expr))
  (def ltuplas (lazyTuplas arg-expr-list (lazyList fun-expr)))
  (  (interp Newfun-expr env)
     (map  (λ (e)  (matchLazy e env)     )
           ltuplas)
     )
  )






;; interp :: Expr Env -> number/procedure/Struct
(define(interp expr env)
  (match expr
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    
    ; conditional
    [(ifc c t f)
     (if  (interp c env)
          (interp t env)
          (interp f env))]
    
    ; identifier
    [(id x) (strict (env-lookup x env))]
    
    ; function (notice the meta interpretation)
    [(fun ids body)
     (λ (arg-vals)  (interp body (extend-env ids arg-vals env)))]
    
    ; application
    [(app fun-expr arg-expr-list)                                                      ;"mine"
     (lazyApp fun-expr arg-expr-list env )
     ]

    ; primitive application
    [(prim-app prim arg-expr-list)
     (apply (cadr (assq prim *primitives*))
            (map (λ (a)  (interp a env)) arg-expr-list))]
    
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))
     (for-each (λ (d) (interp-def d new-env)) defs) 
     (interp body new-env)
     ]
    
    ; pattern matching
    [(mtch expr cases)
     (def value-matched (interp expr env))
     (def (cons alist body) (find-first-matching-case value-matched cases))
     (interp body (extend-env (map car alist) (map cdr alist) env))]
    ))





;defs todo el rato
#;(list (datatype 'List (list (variant 'Empty '())
                              (variant 'Cons '(a b))))
        (dfine 'length (fun '(l) (mtch (id 'l) (list (cse (constrP 'Empty '())
                                                          (num 0))
                                                     (cse (constrP 'Cons (list (idP 'a) (idP 'b)))
                                                          (prim-app '+ (list (num 1) (app (id 'length) (list (id 'b)))))))))))

;defs:------
;body:
#;(app (fun '(x (lazy y)) (id 'x))                            ;fun-expr
       (list (num 42)
             (prim-app '/ (list (num 1) (num 0)))))  ;arg-expr-list

;------

;defs:
#;(list (datatype 'T (list (variant 'C '((lazy a)))))
        (dfine 'x (app (id 'C) (list (prim-app '/ (list (num 1) (num 0)))))))

;body(s):
#;  (app (id 'T?) (list (id 'x)))


(define (lazyList-def var)
  (match var
    [ (variant name params) (if(equal? '() params)
                               #f
                               (map (lambda (p)
                                   (match p
                                     [(list 'lazy x) #t]
                                     [else #f])) params))]
    [else #f]
    )
  )

(define (deleteLazy-def idList)                                        ;MINE
  (match idList
    [(cons (list 'lazy a) b) (cons a (deleteLazy-def b))]
    [(cons a b) (cons a (deleteLazy-def b))]
    [else '()]
   ))


(define (replaceLazy-def var)                                        ;MINE
  (match var
    [ (variant name params)  (variant name (deleteLazy-def params) )]
    [else var] 
    )
  )


(define(env-lookup-def id env)
  ;(println id)
  (match env
    [(mtEnv) #f]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
  ;;;;;;;;;;   (println bindings)
     (if binding
         (cdr binding)
         (env-lookup-def id rest))]))

; interp-def :: Def Env -> Void
(define(interp-def d env)
  ;(println d)
  (match d
    [(dfine id val-expr)     ; (println id)
                             ; (println val-expr)
                            ; ; (println env)
                             ;; (println (env-lookup-def 'C env))
                              ;(println  "")
                              
                               (update-env! id (exprV val-expr env (box #f)) env)
     ;(update-env! id (interp val-expr env) env)
     ]
    [(datatype name variants)     ;; extend environment with new definitions corresponding to the datatype
         (interp-datatype name env)
         (for-each (λ (v) (interp-variant name v env)) variants)]))

; interp-datatype :: String Env -> Void
(define(interp-datatype name env)  ; datatype predicate, eg. Nat?
 ; (println name)
  (update-env! (string->symbol (string-append (symbol->string name) "?"))
               (λ (v) (symbol=? (structV-name (first v)) name))
               env))

; interp-variant :: String String Env -> Void
(define(interp-variant name var env)
 ; (println  var)
 ; (println  (variant-params var))
  (print "nVariant: ")  (println  (replaceLazy-def var)  )
  (print "llist:    ")  (println  (lazyList-def var))

  (def llist  (lazyList-def var))
  (def nVariant   (replaceLazy-def var) )

  

  (def varname (variant-name var))  ;; name of the variant or dataconstructor
  (update-env! varname              ;; variant data constructor, eg. Zero, Succ
               (λ (args) (structV name varname args))
               env)
  (update-env! (string->symbol (string-append (symbol->string varname) "?")) ;; variant predicate, eg. Zero?, Succ?
               (λ (v) (symbol=? (structV-variant (first v)) varname))
               env))

;;;;
; pattern matcher
(define(find-first-matching-case value cases)
  (match cases
    [(list) #f]
    [(cons (cse pattern body) cs)
     (match (match-pattern-with-value pattern value)
       [#f (find-first-matching-case value cs)]
       [alist (cons alist body)])]))

(define(match-pattern-with-value pattern value)
  (match/values (values pattern value)
                [((idP i) v) (list (cons i v))]
                [((litP (bool v)) b)
                 (if (equal? v b) (list) #f)]
                [((litP (num v)) n)
                 (if (equal? v n) (list) #f)]
                [((constrP ctr patterns) (structV _ ctr-name str-values))
                 (if (symbol=? ctr ctr-name)
                     (apply append (map match-pattern-with-value
                                        patterns str-values))
                     #f)]
                [(x y) (error "Match failure")]))

;; run :: s-expr -> number                                                                         my shit
(define(run prog)
    ;(println (interp (lcal (list List+ length+ ) (lazyParse(parse prog)))   empty-env))
    ;(pretty-printing (interp (lcal (list List+ length+ ) (parse prog))   empty-env))
      (pretty-printing (strict (interp  (lcal (list List+ length+ ) (parse prog))   empty-env) ))

  )



#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val 
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

(define(env-lookup id env)
  ;(println id)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
  ;;;;;;;;;;   (println bindings)
     (if binding
         (cdr binding)
         (env-lookup id rest))]))

(define (extend-env ids vals env)

  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))





;; imperative update of env, adding/overring the binding for id.
(define(update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+       ,(lambda args (apply + args)))
    (-       ,(lambda args (apply - args)))
    (*       ,(lambda args (apply * args)))
    (%       ,(lambda args (apply modulo args)))             
    (odd?    ,(lambda args (apply odd? args)))
    (even?   ,(lambda args (apply even? args)))
    (/       ,(lambda args (apply / args)))
    (=       ,(lambda args (apply = args)))
    (<       ,(lambda args (apply < args)))
    (<=      ,(lambda args (apply <= args)))
    (>       ,(lambda args (apply > args)))
    (>=      ,(lambda args (apply >= args)))
    (zero?   ,(lambda args (apply zero? args)))
    (not     ,(lambda args (apply not args)))
    (and     ,(lambda args (apply (lambda (x y) (and x y)) args)))
    (or      ,(lambda args (apply (lambda (x y) (or x y)) args)))
    ))








;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   MYSHIT ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;                     my shit



(define List+
  (datatype 'List
            (list (variant 'Empty '())
                  (variant 'Cons '(a b)))) )


(define length+
  (dfine 'length (fun '(l)
                      (mtch (id 'l)
                            (list
                             (cse (constrP 'Empty '())
                                  (num 0))
                             (cse (constrP 'Cons (list (idP 'a) (idP 'b)))
                                  (prim-app '+ (list (num 1) (app (id 'length) (list (id 'b) ))))
                                  ))))))

(define SugarList+
  (dfine 'list (fun '(l)
                      (mtch (id 'l)
                            (list
                             (cse (constrP 'Empty '())
                                  (num 0))
                             (cse (constrP 'Cons (list (idP 'a) (idP 'b)))
                                  (prim-app '+ (list (num 1) (app (id 'length) (list (id 'b) ))))
                                  ))))))





;;-





(define (concatStr listr)
  (match listr
    [(cons a b) (string-append (if (number? a)
                                   (number->string a)
                                   a)                                
                               (if (equal? "" (concatStr b))
                                   ""
                                   (string-append " " (concatStr b))
                                   ) )  ]
    [else (if (string? listr)
              listr
              (if (symbol? listr)
                  (symbol->string listr)
                  (if (number? listr)
                      (number->string listr)
                      ""                     )))]
    ))




; (structV name variant values)
(define (pretty-printing expr)
  (let ([listedExpr (pretty-list expr)])
  (match listedExpr
    [(structV name variant values)
     (if (empty? values)
         (string-append "{" (string-append (symbol->string (structV-variant listedExpr)) "}" ))
         (string-append "{" (string-append (symbol->string (structV-variant listedExpr))
                                           (string-append " " (string-append
                                                               (concatStr (map pretty-printing values))
                                                               "}")) )) )]
    [else listedExpr]
    )   )
  )
  
(define (pretty-list expr)
  (match expr
    [(structV 'List 'Cons (list a b)) (if (isList b)
                                          (structV 'List 'list (getList expr))
                                          (structV 'List 'Cons (cons (pretty-list a) (pretty-list b)))
                                          )     ]
    [else expr])
  )

(define (isList cons)
  (match cons
    [(structV 'List 'Empty '()) #t]
    [(structV 'List 'Cons (list a b))  (isList b)]
    [else #f]
    ))

(define (getList lst)
  (match lst
    [(structV 'List 'Empty '()) '()]
    [(structV 'List 'Cons (list a b))  (cons (pretty-list a) (getList b))]
   ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   MYTESTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(print-only-errors #t)

(parse '{local {{datatype T 
                              {C {lazy a}}}
                    {define x {C {/ 1 0}}}}
              {T? x}})
;;
#;(run '{local {{datatype T 
                              {C {lazy a}}}
                    {define x {C {/ 1 0}}}}
              {T? x}})

     

(test (run '{local {{datatype T 
                              {C {lazy a}}}
                    {define x {C {/ 1 0}}}}
              {T? x}})
      #t)

(test
(run '{local {{datatype T 
                  {C {lazy a}}}
                {define x {C {+ 1 0}}}
                {define y {C {/ 1 0}}}}
          {match x
            {case {C a} => a}}})
1)





;(run '{{fun {x y} x} 42 {/ 1 0}})













#;(test
   (run '{local {{datatype Cache 
                           {Empty} 
                           {Cons a b}}
                 {define length {fun {l} 
                                   {match l
                                     {case {Empty} => 0}
                                     {case {Cons a b} => {+ 1 {length b} }}}}}}
           {length {Cons {Empty} {Empty}}}})
   1)







(test (run '{{fun {x  {lazy y}} x} 1 {/ 1 0}}) 1)
(test (run '{{fun {{lazy x}  {lazy y}} x} 1 {/ 1 0}}) 1)

(println "-----fail----")
(test/exn (run '{{fun {x  y} x} 1 {/ 1 0}}) "/: division by zero")
(test/exn (run '{{fun {x  {lazy y}} y} 1 {/ 1 0}}) "/: division by zero")
(println "-----fail----")






(println "vVvVvVvVvVvV      TODO WeNo QL     vVvVvVvVvVvV")





(test (run '{local {{datatype Nat 
                              {Zero} 
                              {Succ n}}}
              {Succ {Succ {Zero}}}})
      "{Succ {Succ {Zero}}}")


(test (run '{local {{datatype Nat 
                              {Zero} 
                              {Succ n}}
                    {define pred {fun {n} 
                                      {match n
                                        {case {Zero} => {Zero}}
                                        {case {Succ m} => m}}}}}
              {pred {Succ {Succ {Zero}}}}})
      "{Succ {Zero}}")

;;
(test (run '{match {Cons {+ 1 1} 6}
              {case {Cons h r} => h}
              {case _ => 0}}) 2)

(test (run '{match {list 2 6}
              {case {Cons h r} => h}
              {case _ => 0}}) 2)


(test
 (run '{match {list {+ 1 1} 4 6}
         {case {Cons h r} => h}
         {case _ => 0}})2)



(test (run '{local {{datatype Nat 
                              {Zero} 
                              {Succ n}}}
              {Nat? {Zero}}}) #t)


(test (run '{List? {Empty}}) #t)

(test (run '{length {Empty}}) 0)

(test (run '{length {Cons {Empty} {Empty}}}) 1)

(test (run '{length {Cons {Empty} {Cons {Empty} {Empty}}}}) 2)

(test (run '{local {{datatype List 
                              {Empty} 
                              {Cons a b}}
                    {define length {fun {l} 
                                        {match l
                                          {case {Empty} => 0}
                                          {case {Cons a b} => {+ 1 {length b} }}}}}}
              {length {Cons {Empty} {Empty}}}}) 1)

(test (run '{match   {list 2 {list 4 5} 6}
              {case {list a {list b c} d} => c}})  5)

(test (run '{match   {list 2 {list 4 5} 6}
              {case {Cons a (Cons {Cons b (Cons c {Empty})} (Cons d {Empty}) )} => c}}) 5)
  
(test (run '{match {list 2 {list 4 5} 6}
              {case {list a {list b c} d} => d}}) 6)

(test (run '{match {list 2 4 8 16}
              {case {list a b c d} => b}}) 4)

(test (run '{match {list 2 4 8 16}
              {case {Cons a b} => b}}) "{list 4 8 16}")

(test (run '{match {list 2 6}
              {case {Cons a {Cons b {Empty}}} => a}}) 2)

(test (run '{match {list 2 6}
              {case {Cons a {Cons b {Empty}}} => b}}) 6)

(test (run '{list 2 4 6})
      "{list 2 4 6}")

(test(run '{list 2 {list 4 5} 6})
     "{list 2 {list 4 5} 6}")  
(test (run '{Cons 2 (Cons {Cons 4 (Cons 5 {Empty})} (Cons 6 {Empty}) )})
      "{list 2 {list 4 5} 6}")   

(test (run '{match   {list 2 {list 4 5} 6}
              {case {list a b c} => b}})  "{list 4 5}")

(test (run '{match   {list 2 {list 4 5} 6}
              {case {Cons a {Cons {Cons b c} d}} => c}})
      "{list 5}")



(test (run '{local {{datatype BinTree 
                              {Leaf v} 
                              {Node v l r}}}
              {Node 10 {Leaf 7} {Leaf 2}}})
      "{Node 10 {Leaf 7} {Leaf 2}}")

(test (pretty-printing (structV 'Bin 'Val '(1)))
      "{Val 1}")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; TESTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test sub-module.
;; See http://blog.racket-lang.org/2012/06/submodules.html

;this tests should never fail; these are tests for MiniScheme+ 
(module+ test
  (test (run '{+ 1 1}) 2)
  
  (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)  
  
  (test (run '{< 1 2}) #t)
  
  (test (run '{local {{define x 1}}
                x}) 1)
  
  (test (run '{local {{define x 2}
                      {define y {local {{define x 1}} x}}}
                {+ x x}}) 4)
  
  ;; datatypes  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Cons 1 2}}})
        #f)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Empty}}})
        #f)      
  
  ;; match
  (test (run '{match 1 {case 1 => 2}}) 2)
  
  (test (run '{match 2
                {case 1 => 2}
                {case 2 => 3}})             
        3)
  
  (test (run '{match #t {case #t => 2}}) 2)
  
  (test (run '{match #f
                {case #t => 2}
                {case #f => 3}})             
        3)

  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}})
        #t)
  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}}) #t))

;tests for extended MiniScheme+ 
#;(module+ sanity-tests
    (test (run '{local {{datatype Nat 
                                  {Zero} 
                                  {Succ n}}
                        {define pred {fun {n} 
                                          {match n
                                            {case {Zero} => {Zero}}
                                            {case {Succ m} => m}}}}}
                  {pred {Succ {Succ {Zero}}}}}) "{Succ {Zero}}")
  
(test (run
 `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 11 ones}}}) "{list 1 1 1 1 1 1 1 1 1 1 1}")

(test (run `{local ,stream-lib
          {local {,stream-zipWith ,fibs}
            {stream-take 10 fibs}}}) "{list 1 1 2 3 5 8 13 21 34 55}")

(test (run `{local ,stream-lib
          {local {,ones ,stream-zipWith}
            {stream-take 10
                         {stream-zipWith
                          {fun {n m}
                               {+ n m}}
                          ones
                          ones}}}})  "{list 2 2 2 2 2 2 2 2 2 2}")
(test 
(run `{local ,stream-lib
               {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
                 {stream-take 10 {merge-sort fibs fibs}}}})   "{list 1 1 1 1 2 2 3 3 5 5}"))
