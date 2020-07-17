#lang racket
(require "faster-miniKanren-master/mk.rkt")
(require "faster-miniKanren-master/numbers.rkt")

;defines ^ as expt
(define ^ (lambda (a b) (expt a b)))

;checks if list has x
(define member?
  (lambda (x l)
    (cond
      ((null? l) #f)
      ((equal? (car l) x) #t)
      (else (member? x (cdr l))))))

;checks if list contains lists
(define haslist?
  (lambda (expr)
    (cond
      ((null? expr) #f) 
      ((list? (car expr)) #t)
      (else (haslist? (cdr expr))))))


"SIMPLIFY";______________________________________________________________________________________________________

;simplifies one parens 
(define simplifyhelper
  (lambda (expr)
    (match expr
      [`(+ ,v) v]
      [`(* ,v) v]
      [(list-no-order '+ 0 v ) v]
      [(list-no-order '* 1 v ) v]
      [(list-no-order '+ 0 v ...) `(+ . ,v)]
      [(list-no-order '* 0 v ...) 0]
      [(list-no-order '* 1 v ...) `(* . ,v)]
      [`(^ ,v 1) v]
      [`(^ ,v 0) (if (and (number? v)(zero? v))
                     (error 'simplifyhelper "(^ 0 0)")
                     1)]
      [`(^ 0 ,v) 0]
      [`(^ 1 ,v) 1];just added
      [else expr])))



;simplifies all 
(define simplifyonestep
  (lambda (expr)
    (let ((s (simplifyhelper expr)))
      (cond
        ((null? s) '())
        ((not (list? s)) s)
        ((list? (car s)) (cons (simplifyonestep (car s)) (simplifyonestep (cdr (simplifyhelper expr)))))
        (else (cons (car s) (simplifyonestep (cdr s))))))))

;calls simplifyonestep until fully simplified
(define simplify
  (lambda (expr)
    (let ((simplified (simplifyonestep expr)))
      (cond
        ((equal? simplified expr) expr)
        (else (simplify simplified))))))


"FORWARD ACCUMULATION DERIVATIVES";______________________________________________________________________________________________________

(define *v* 'v_has_not_been_set)

;automatic differentiation by forward accumulation 

(define favcaller
  (lambda (expr x seed)
    (set! *v* seed)
    (forwardaccg expr x)
    ))

'global_version

;this version has a global association list to save values 
(define forwardaccg
  (lambda (expr x)
    (let ((s (simplify expr)))
      (letrec ((deriv
                (lambda (expr)
                  ;(let ((s (simplify expr)))
                  (let ((expr (if (number? expr) 'n expr)))
                    (cond
                      ((assoc expr *v*) => cadr)
                      (else (let ((d (simplify (forwardaccg expr x))))
                              (set! *v* (cons `(,expr ,d) *v*))
                              d)))))))
      
        (match s
          [`(+ . ,e*) `(+ . ,(map deriv e*))]
          [`(* . ,e*)
           (letrec ((multrule
                     (lambda(e*)
                       (cond
                         ((= (length e*) 1) (deriv (car e*)))
                         (else `(+ (* ,(deriv (car e*)) (* . ,(cdr e*)))
                                   (* ,(car e*) ,(multrule (cdr e*)))))))))
             (multrule e*))]
          [`(^ ,a ,b)#:when (not (equal? b '0)) (deriv (simplify `(* ,a (^ ,a ,(- b 1)))))]
          [`(^ ,a 0) '0]
                       
          [else 'ERROR_EXPR_NOT_MATCHED])))))

(simplify (favcaller '(^ y 2) 'y '((y 1)(n 0))))
`(---*v* ,*v*)
(simplify (favcaller '(+ y y 5) 'y '((y 1)(n 0))))
`(---*v* ,*v*)
(simplify (favcaller '(+ y (* 4 y) 5) 'y '((y 1)(n 0))))
`(---*v* ,*v*)
(simplify (favcaller '(* (* y 4) (+ (* 0 5) (* y 3) (* y 4))) 'y '((y 1)(n 0))))
`(---*v* ,*v*)
(simplify (favcaller '(+ (^ y 3) (^ y 2) (^ y 1)) 'y '((y 1)(n 0))))
`(---*v* ,*v*)


;(load "test.rkt")
;(load "simplify.rkt")

;automatic differentiation by forward accumulation


'monadic_style_version

(define snake-map
  (lambda (df l v)
    (cond
      ((null? l) (list '() v))
      (else (let ((d/v (df (car l) v)))
              (let ((d (car d/v))
                    (v (cadr d/v)))
                (let ((d/v-rest (snake-map df (cdr l) v)))
                  (let ((d-rest (car d/v-rest))
                        (v-rest (cadr d/v-rest)))
                    (list (cons d d-rest) v-rest)))))))))

;; returns (deriv new-v)
(define forwardaccm
  (lambda (expr x v)
    (let ((s (simplify expr)))
      (letrec ((deriv ;; returns (deriv new-v)
                (lambda (expr v)
                  (let ((expr (if (number? expr) 'n expr)))
                    (cond
                      ((assoc expr v) => (lambda (p)
                                           (list (cadr p) v)))
                      (else (let ((d/v (forwardaccm expr x v)))
                              (let ((d (car d/v))
                                    (v (cadr d/v)))
                                (let ((d (simplify d)))
                                  (let ((v (cons `(,expr ,d) v)))
                                    (list d v)))))))))))  
        (match s
          [`(+ . ,e*) (let ((d/v (snake-map deriv e* v)))
                        (let ((d (car d/v))
                              (v (cadr d/v)))
                          (list `(+ . ,d) v)))]
          [`(* . ,e*)
           (letrec ((multrule
                     (lambda (e* v)
                       (cond
                         ((= (length e*) 1) (deriv (car e*) v))
                         (else (let ((d/v-a (deriv (car e*) v)))
                                 (let ((d-a (car d/v-a))
                                       (v-a (cadr d/v-a)))
                                   (let ((d/v-d (multrule (cdr e*) v-a)))
                                     (let ((d-d (car d/v-d))
                                           (v-d (cadr d/v-d)))
                                       (list `(+ (* ,d-a (* . ,(cdr e*)))
                                                 (* ,(car e*) ,d-d))
                                             v-d))))))))))
             (multrule e* v))]
          [`(^ ,a ,b) #:when (not (equal? b '0)) (deriv (simplify `(* ,a (^ ,a ,(- b 1)))) v)]
          [`(^ ,a 0) (list 0 v)]
          [else (error 'forwardaccm (format "EXPR ~s NOT MATCHED" s))])))))

(define favcallerm forwardaccm)

(favcallerm '(^ y 2) 'y '((y 1) (n 0)))
(simplify (favcallerm '(+ (^ y 3) (^ y 2) (^ y 1)) 'y '((y 1) (n 0))))


#;((test
  (simplify (favcallerm '(+ y y 5) 'y '((y 1) (n 0))))
  `((+ 1 1) ((y 1) (n 0))))

(test
   (simplify (favcallerm '(+ y 5) 'y '((y 1) (n 0))))
  '(1 ((y 1) (n 0))))

(test
  (simplify (favcallerm ' (* 4 y) 'y '((y 1) (n 0))))
  '(4 ((y 1) (n 0))))

(test
  (simplify (favcallerm '(+ y (* 4 y) 5) 'y '((y 1) (n 0))))
  (list '(+ 1 4) '(((* 4 y) 4) (y 1) (n 0))))

(test
  (simplify (favcallerm '(* (* y 4) (+ (* 0 5) (* y 3) (* y 4))) 'y '((y 1) (n 0))))
  (list '(+ (* 4 (+ (* y 3) (* y 4))) (* (* y 4) (+ 3 4)))
        '(((+ (* y 3) (* y 4)) (+ 3 4)) ((* y 3) 3) ((* y 4) 4) (y 1) (n 0))))


(test
  (favcallerm '(+ 1 (* y (^ y 1))) 'y '((y 1) (n 0)))
  (list '(+ 0 (+ y y))
       '(((* y y) (+ y y)) (y 1) (n 0)) ))


(test
  (favcallerm '(^ y 2) 'y '((y 1) (n 0)))
  (list '(+ y y)
        '(((* y (^ y 1)) (+ y y)) (y 1) (n 0))))


;;;
(test
  (favcallerm '(+ (^ y 3) (^ y 2) (^ y 1)) 'y '((y 1) (n 0)))
  (list '(+ (+ (^ y 2) (* y (+ y y))) (+ y y) 1)
        '(((^ y 3) (+ (^ y 2) (* y (+ y y)))) ((* y (^ y 2)) (+ (^ y 2) (* y (+ y y)))) ((^ y 2) (+ y y)) ((* y (^ y 1)) (+ y y)) (y 1) (n 0))))


(test
  (simplify (favcallerm '(+ (^ y 3) (^ y 2) (^ y 1)) 'y '((y 1) (n 0))))
  (list '(+ (+ (^ y 2) (* y (+ y y))) (+ y y) 1)
        '(((^ y 3) (+ (^ y 2) (* y (+ y y))))
          ((* y (^ y 2)) (+ (^ y 2) (* y (+ y y))))
          ((^ y 2) (+ y y))
          ((* y (^ y 1)) (+ y y))
          (y 1)
          (n 0))))
)

'snake_version

;note this cant be called more than one times on the same thing aka check its not already in v


;this version passes the association table as it goes and sequentially goes through the expression


;trying a left to right method

(define snake
  (lambda (expr x v)
    (let ((s (simplify expr)))
      (let ((sn (if (number? s) 'n s)))
        (let ((a (assoc sn v)))
          (cond
            (a `(,(cadr a) ,v))
            
            (else (match s
                    [`(+ ,e . ,e*) (letrec ((addrec
                                             (lambda (expr^ v^)
                                               (let ((ee (snake (car expr^) x v^)))
                                                 (cond
                                                   ((null? (cdr expr^)) `((,(car ee)) ,(cadr ee))) 
                                                   (else (let ((r (addrec (cdr expr^) (cadr ee))))
                                                           (let ((d `(,(car ee) . ,(car r))))
                                                             `(,d ((,(simplify `(+ . ,expr^)) ,(simplify `(+ . ,d))) . ,(cadr r)))))))))))
                                     (let ((addlist (addrec `(,e . ,e*) v)))
                                       `(,(simplify `(+ . ,(car addlist))) ,(cadr addlist))))]

                      
                    [`(* ,e . ,e*) (letrec ((multrule
                                             (lambda (expr^ v^)
                                               (let ((ee (snake (car expr^) x v^)))
                                                 (cond
                                                   ((null? (cdr expr^)) ee)
                                                   (else (let ((r (multrule (cdr expr^) (cadr ee))))
                                                           (let ((d (simplify `(+ ,(simplify `(* ,(car ee) . ,(cdr expr^)))
                                                                                  ,(simplify `(* ,(car expr^) ,(car r)))))))
                                                             `(,d ((,(simplify `(* . ,expr^)) ,(simplify d)) . ,(cadr r)))))))))))
                                                           
                                     (multrule `(,e . ,e*) v))]

                    [`(^ ,a ,b) #:when (not (zero? b)) (let ((r (snake `(* ,a (^ ,a ,(- b 1))) x v))) 
                                                         `(,(car r) ((,s ,(car r)) . ,(cadr r))))]

                    [`(^ ,a 0) (if (zero? a) 'ERROR_^_0_0
                                   `(0 ((,s 0) . ,v)))]
                    ))))))))



'(add)
(snake 'y 'y  '((y 1)(n 0)))
(snake '(+ y  10 0 y) 'y  '((y 1)(n 0)))
(snake '(+ (+ y 5) y) 'y  '((y 1)(n 0)))
(snake '(+ (+ (+ 2 3) y) (+ 2 3)) 'y  '((y 1)(n 0)))


'(multiply)
(snake '(* y) 'y  '((y 1)(n 0)))
(snake '(* 5 y) 'y  '((y 1)(n 0)))
(snake '(* y 5 y) 'y  '((y 1)(n 0)))
(snake '(* y 1 2) 'y  '((y 1)(n 0)))
(snake '(* (+ (* y 1 2) 3) (* y 1 2)) 'y  '((y 1)(n 0))) 


'(exponent)
(snake '(^ y 1) 'y  '((y 1)(n 0)))
(snake '(+ (^ y 3) (^ y 2)) 'y  '((y 1)(n 0)))


;recursive draft without letrec before simplification code and before exponent 
                                       ;(else (let ((r (snake `(* . ,e*) x (cadr ee))))

#;(define snakenotsimp
  (lambda (expr x v)
    ;(let ((s (simplify expr)))
    (let ((s expr))
      (let ((sn (if (number? s) 'n s)))
        (let ((a (assoc sn v)))
          (let ((b (assoc s v)))
          (cond
            (a `(,(cadr a) ,v))
            (b `(,(cadr b) ,v))
            (else (match s

                    [`(+ ,e . ,e*) (letrec ((addrec;working version using addrec 
                                             (lambda (expr^ v^)
                                               (let ((ee (snakenotsimp (car expr^) x v)))
                                                 (cond
                                                   ((null? (cdr expr^)) `((,(car ee)) ,(cadr ee)));is the list on car ee correct 
                                                   (else (let ((r (addrec (cdr expr^) (cadr ee))))
                                                           (let ((d `(,(car ee) . ,(car r))))
                                                             `(,d (((+ . ,expr^) ,d) . ,(cadr r)))))))))))
                                     (let ((addlist (addrec `(,e . ,e*) v)))
                                       `((+ . ,(car addlist)) ,(cadr addlist))))]


                    #;[`(+ ,e . ,e*) (let ((ee (snakenotsimp e x v)));working version without addrec 
                                     (cond
                                       ((null? e*) `((+ ,(car ee)) ,(cadr ee)));is the + going to be a problem when I start to simplify 
                                       (else (let ((r (snakenotsimp `(+ . ,e*) x (cadr ee))))
                                               (let ((d `(+ ,(car ee) . ,(cdar r))))
                                                 `(,d ((,sn ,d) . ,(cadr r))))))
                                       ))]
                    [`(* ,e . ,e*) (letrec ((multrule
                                             (lambda (expr^ v^)
                                               (let ((ee (snakenotsimp (car expr^) x v)))
                                               (cond
                                                 ((null? (cdr expr^)) ee)
                                                 (else (let ((r (multrule (cdr expr^) (cadr ee))))
                                                         (let ((d `(+ (* ,(car ee) . ,(cdr expr^)) (* ,(car expr^) ,(car r)))))
                                                           `(,d (((* . ,expr^) ,d) . ,(cadr r)))))))))))
                                                           
                                                         (multrule `(,e . ,e*) v))]



                    )))))))))

;trying a level method 
#;(define snake
  (lambda (expr x v level)
    (letrec ((findlist
              (lambda (expr)
                (cond
                  ((list? (car expr)) (snake
    (cond
      ((assoc expr v) => cadr)
      ((haslist? expr)
)))))))))))



'old_version

;this version wont correctly use a table 
(define forwardaccold
  (lambda (expr x v)
    (letrec ((deriv
              (lambda (expr)
                (let ((expr (if (number? expr) 'n expr)))
                  (cond
                    ((assoc expr v)(cadr (assoc expr v)))
                    (else (forwardaccold expr x v)))))));i should pass soomething other than v
                        
      (match expr
        [`(+ . ,e*) `(+ . ,(map deriv e*))]
        [`(* . ,e*)
         (letrec ((multrule
                   (lambda(e*)
                     (cond
                       ((= (length e*) 1) (deriv (car e*)))
                       (else `(+ (* ,(deriv (car e*)) (* . ,(cdr e*)))
                                 (* ,(car e*) ,(multrule (cdr e*)))))))))
           (multrule e*))]
                                           
                       
        [else 'ERROR_EXPR_NOT_MATCHED]
        ))))

(forwardaccold '(+ y) 'y '((y 1)(n 0)))
(forwardaccold '(+ y y 5) 'y '((y 1)(n 0)))
(forwardaccold '(+ y (* 4 y) 5) 'y '((y 1)(n 0)))

'MK_version

(define listo
  (lambda (expr)
    (fresh (a b)
      (== `(a . ,b) expr))))

(define assoco
  (lambda (item list ivalue)
    (fresh (rest a b)
      (conde
        ((== `((,item ,ivalue) . ,rest) list))
        ((== `((,a ,b) . ,rest) list)
         (=/= item a)
         (assoco item rest ivalue))
        ((== '() list) (== 'novalue ivalue))
        ((== '() list) (== 'noitem item))))))


(define *vo* 'v_has_not_been_set)

(define favmkcallero
  (lambda (expr deriv x seed)
    (set! *vo* seed)
    (fresh ()
      (forwardaccmko expr deriv x)
    )))

(define forwardaccmko
  (lambda (expr deriv x)
    (fresh ()
      (letrec ((derivo
                (lambda (e d)
                  (fresh (en)
                    (conde
                      ((== en 'n) (numbero e))
                      ((== en e) (symbolo e))
                      ((== en e) (listo e)))
                      (conde
                        ((=/= d 'novalue) (=/= en 'noitem) (assoco en *vo* d))
                        ((assoco en *vo* 'novalue) (forwardaccmko e d x) (set! *vo* (cons `(,e ,d) *vo*)));the last part isnt correct ofc 
                        ((assoco en *vo* 'noitem) (forwardaccmko e d x) (set! *vo* (cons `(,e ,d) *vo*)))
                        )))))
        (conde
          ((fresh (e* d*)
             (== `(+ . ,e*) expr)
             (== `(+ . ,d*) deriv)
             (letrec ((addrec (lambda (e* d*)
                                (fresh (e1 d1 e2 d2)
                                  (conde
                                    ((== `(,e1) e*) (== `(,d1) d*)
                                     (derivo e1 d1))
                                    ((== `(,e1 . ,e2) e*)(=/= '() e2)
                                     (== `(,d1 . ,d2) d*)(=/= '() d2)
                                     (derivo e1 d1)
                                     (addrec e2 d2)))))))
               (addrec e* d*))))
          
          #;((fresh (e*)
             (== `(* . ,e*) expr)
             ;multrule e*
             ))
          
          ((fresh (a b bm1)
             (== `(^ ,a ,b) expr) (=/= 0 b)
             (derivo `(* ,a (^ ,a ,bm1)) deriv)
             (pluso bm1 1 b)))
          ((fresh (a)
             (== `(^ ,a 0) expr) (== '0 deriv)))
          )))))
        
          
                   
                    
                

  #;(define forwardaccg;copied for refrence 
  (lambda (expr x)
    (let ((s (simplify expr)))
      (letrec ((deriv
                (lambda (expr)
                  ;(let ((s (simplify expr)))
                  (let ((expr (if (number? expr) 'n expr)))
                    (cond
                      ((assoc expr *v*) => cadr)
                      (else (let ((d (simplify (forwardaccg expr x))))
                              (set! *v* (cons `(,expr ,d) *v*))
                              d)))))))
      
        (match s
          [`(+ . ,e*) `(+ . ,(map deriv e*))]
          [`(* . ,e*)
           (letrec ((multrule
                     (lambda(e*)
                       (cond
                         ((= (length e*) 1) (deriv (car e*)))
                         (else `(+ (* ,(deriv (car e*)) (* . ,(cdr e*)))
                                   (* ,(car e*) ,(multrule (cdr e*)))))))))
             (multrule e*))]
          [`(^ ,a ,b)#:when (not (equal? b '0)) (deriv `(* ,a (^ ,a ,(- b 1))))]
          [`(^ ,a 0) '0];^ 0 0
                       
          [else 'ERROR_EXPR_NOT_MATCHED])))))

'FORWARD 
(run 1 (q) (favmkcallero '(+ y y 5) q 'y '((y 1)(n 0))))
`(---*vo* ,*vo*)
(run 1 (q) (favmkcallero '(+ y (+ 2 y (+ y 1)) 5) q 'y '((y 1)(n 0))))
`(---*vo* ,*vo*)
;(run 1 (q) (favmkcallero '(+ y (* 4 y) 5) q 'y '((y 1)(n 0))))
;`(---*vo* ,*vo*)
;(run 1 (q) (favmkcallero '(* (* y 4) (+ (* 0 5) (* y 3) (* y 4))) q 'y '((y 1)(n 0))))
;`(---*vo* ,*vo*)
;(run 1 (q) (favmkcallero '(+ (^ y 3) (^ y 2) (^ y 1)) q 'y '((y 1)(n 0))))
;`(---*vo* ,*vo*)

'BACKWARD
;;;(run 1 (q) (favmkcallero '(+ y y 5) 'y '((y 1)(n 0))))
;;;`(---*vo* ,*vo*)
;(run 1 (q) (favmkcallero '(+ y (* 4 y) 5) 'y '((y 1)(n 0))))
;`(---*vo* ,*vo*)
;(run 1 (q) (favmkcallero '(* (* y 4) (+ (* 0 5) (* y 3) (* y 4))) 'y '((y 1)(n 0))))
;`(---*vo* ,*vo*)
;(run 1 (q) (favmkcallero '(+ (^ y 3) (^ y 2) (^ y 1)) 'y '((y 1)(n 0))))
;`(---*vo* ,*vo*)


"REVERSE ACCUMULATION DERIVATIVES";_________________________________________________________________________________________________




