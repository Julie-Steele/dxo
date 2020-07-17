#lang racket
(require racket/trace)
;defines ^ as expt
(define ^ (lambda (a b) (expt a b)))

;checks if list has x
(define member?
  (lambda (x l)
    (cond
      ((null? l) #f)
      ((equal? (car l) x) #t)
      (else (member? x (cdr l))))))

;removes x from l
(define remove
  (lambda (x l)
    (cond
      ((equal? (car l) x) (cdr l))
      (else (cons (car l) (remove x (cdr l)))))))

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
      [`(^ ,v 0) (if (zero? v)
                     (error 'simplifyhelper "(^ 0 0)")
                     1)]
      [`(^ 0 ,v) 0]
      [`(^ 1 ,v) 1];just added
      [else expr])))

;my version of list-no-order
(define mylist-no-order
  (lambda (items l)
    (cond
      ((and (null? items) (null? l)) #t)
      ((equal? items '(rest)) #t)
      ((equal? items '(any)) (mylist-no-order '() (cdr l)))
      ((null? items) #f)
      ((member? (car items) l) (mylist-no-order (cdr items) (remove (car items) l)))
      (else #f))))
      

;simplifies one parens without using list-no-order
(define newsimplifyhelper
  (lambda (expr)
    (match expr
      [`(+ ,v) v]
      [`(* ,v) v]
      [`(+ . ,v*) #:when (mylist-no-order '(+ 0 any) expr) (car (remove '+ (remove '0 expr)))]
      [`(+ . ,v*) #:when (mylist-no-order '(+ 0 rest) expr) (remove '0 expr)]
      [`(* . ,v*) #:when (mylist-no-order '(* 0 rest) expr) 0]
      [`(* . ,v*) #:when (mylist-no-order '(* 1 rest) expr) (remove '1 expr)]
      [`(^ ,v 1) v]
      [`(^ ,v 0) (if (zero? v)
                     (error 'newsimplifyhelper "(^ 0 0)")
                     1)]
      [`(^ 0 ,v) 0]
       [`(^ 1 ,v) 1];just added
      [else expr])))

;simplifies one parens without using list-no-order or mylist-no-order
(define simplenewsimplifyhelper
  (lambda (expr)
    (match expr
      [`(+ ,v) v]
      [`(* ,v) v]
      ;[`(+ ,v ,v2) #:when (member? 0 expr) (car (remove '+ (remove '0 expr)))]
      [`(+ . ,v*) #:when (member? 0 expr) (remove '0 expr)]
      [`(* . ,v*) #:when (member? 0 expr) 0]
      [`(* . ,v*) #:when (member? 1 expr) (remove '1 expr)]
      [`(^ ,v 1) v]
      [`(^ ,v 0) (if (zero? v)
                     (error 'simplenewsimplifyhelper "(^ 0 0)")
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

;runs d _ times
(define d!helper
  (lambda (int x expr)
    (cond
      ((= int 0) expr)
      (else (d!helper (- int 1) x (simplify (d x expr)))))))

;simplifies output of d!
(define d!
  (lambda (int x expr)
    (simplify (d!helper int x expr))))

;takes derivative 
(define d
  (lambda (x expr)
    (match expr
      [`(+ . ,e*)
       (let ((dhelper (lambda (e)
                        (d x e))))
         `(+ . ,(map dhelper e*)))]

      [` (^ ,v ,0) #:when  (equal? v x) 0]
      
      [`(* (^ ,v ,0) ,int) #:when (and (number? int) (equal? v x)) 0]

      ;[`(* (^ ,v ,int) ,0) #:when (and (number? int) (equal? v x)) 0]

      [`(* . ,e*)
       ;(printf "e*: ~s\n " e*)
       (letrec ((multrule
                 (lambda (e*)
                   (cond
                     ((= (length e*) 1) (d x (car e*)))
                     (else `(+ (* ,(d x (car e*)) (* . ,(cdr e*)))
                               (* ,(car e*) ,(multrule (cdr e*)))))))))
         (multrule e*))]

      [`(^ ,v ,int) #:when (and (number? int) (equal? v x)) `(* (^ ,v ,(- int 1)) ,int)]

      [v  #:when (equal? v x) 1 ]

      ;[`(* ,v ,int) #:when (and (number? int) (equal? v x)) int]

      
      [int  #:when (number? int) 0 ])))
 
'(d (* a))
'(d a)

'(d (* a b))
'(+ (* (d a) b) (* a (d b)))

'(d (* a b c))
'(+ (*( d a) (* b c)) (* a (d (* b c))))

'(d (* a ...))
'(+ (* (d a) ...) (* a (d ...)))

;helper for evaluatehelper, returns value of single operation 
(define opprec
 (lambda (x n opp expr value)
    (cond
      ((null? expr) value)
      ((equal? opp 'add)
       (cond
         ((equal? (car expr) x) (opprec x n opp (cdr expr) (+ value n)))
         ((number? (car expr)) (opprec x n opp (cdr expr) (+ value (car expr))))))
      ((equal? opp 'mult)
       (cond
         ((equal? (car expr) x) (opprec x n opp (cdr expr) (* value n)))
         ((number? (car expr)) (opprec x n opp (cdr expr) (* value (car expr))))))
      ((equal? opp 'exp)
       (cond
         ((equal? (car expr) x) (opprec x n opp '() (^ n (car (cdr expr)))))
         ((number? (car expr)) (opprec x n opp '() (^ (car expr) (car (cdr expr)))))))
         )))

;checks if list contains lists
(define haslist?
  (lambda (expr)
    (cond
      ((null? expr) #f) 
      ((list? (car expr)) #t)
      (else (haslist? (cdr expr))))))

;evaluates expression with x as n by calling evaluateonelevel repeatedly
(define evaluate
  (lambda (x n expr)
    (cond
      ((number? expr) expr)
      ;((equal? expr (evaluateonelevel x n expr)) expr)
      (else (evaluate x n (evaluateonelevel x n expr))))))

;evaluates inner lists by calling evaluatehelper, helper for evaluate 
(define evaluateonelevel
 (lambda (x n expr)
   (cond
      ((null? expr) '())
      ((and (equal? (haslist? expr) #f) (or (equal? (car expr) '+)(equal? (car expr) '*)(equal? (car expr) '^)))  (evaluatehelper x n expr))
      ((list? (car expr)) (cons (evaluateonelevel x n (car expr)) (evaluateonelevel x n (cdr expr))))
      (else (cons (car expr) (evaluateonelevel x n (cdr expr)))))))

;evaluates single opperation by calling opprec, helper for evaluate 
(define evaluatehelper  
  (lambda (x n expr)
    (match expr
      [`(+ ,a . ,a*) (opprec x n 'add `(,a . ,a*) 0)]
      [`(* ,a . ,a*) (opprec x n 'mult `(,a . ,a*) 1)]
      [`(^ ,a ,a2) (opprec x n 'exp `(,a ,a2) 0)]
       )))

;evaluates expression with a variable by calling evaluate2helper (because of eval, only works in the repel)
(define evaluate2
  (lambda (x n expr)
    (eval (evaluate2helper x n expr))))

;helper for evaluate2 switches a variable with a number 
(define evaluate2helper
  (lambda (x n expr)
    (cond
      ((null? expr) '())
      ((equal? (car expr) x) (cons n (evaluate2helper x n(cdr expr))))
      ((list? (car expr)) (cons (evaluate2helper x n (car expr)) (evaluate2helper x n (cdr expr))))
      (else (cons (car expr) (evaluate2helper x n (cdr expr)))))))

;checks if test returns expected 
(define-syntax test
  (syntax-rules ()
    [(_ expr expected)
     (let ((v expr)(x expected))
       (if (equal? v x)
           #t
           (printf "TEST FAILED: ~s produced ~s, expected ~s \n" 'expr v x)))]))

;checks that all tests run correctly
(define grandtest
  (lambda (t n)
    (cond
      ((null? t) (if (= n 0) (println "all tests are correct")
                     (println "ERROR IN TESTS")) '())
      ((equal? (car t) #t) (grandtest (cdr t) n))
      (else (cons (car t) (grandtest (cdr t) (+ n 1)))))))

(grandtest
 `(
 ,(test (d! 1 'x '(* 5 (^ x 3)(^ x 3)(* (^ x 4) (+ x 4)))) '(*
  5
  (+
   (* (* (^ x 2) 3) (* (^ x 3) (* (^ x 4) (+ x 4))))
   (*
    (^ x 3)
    (+
     (* (* (^ x 2) 3) (* (^ x 4) (+ x 4)))
     (*
      (^ x 3)
      (+ (* (* (^ x 3) 4) (+ x 4)) (^ x 4))))))))
,(test (simplify '(+ hello 0)) 'hello)
,(test (simplify '(+ hello 0)) 'hello)
,(test (simplify '(+ (* x 1) 0)) 'x)) 0)


(display '(derivative tests))
;new line
'()
(trace d!)
;(trace d!helper)
;(trace simplify)

(d! 1 'x '(+ (* (^ x 3) 5) (* (^ x 2) 1) 0))
(d! 1 'x '(+ (* (^ x 4) 10) (* (^ x 2) 0)))
(d! 3 'x '(+ (* (^ x 8) 5) (* (^ x 2) 1)))
(println "long deriv")
(d! 300 'x '(+ (* (^ x 3) 5) (* (^ x 2) 1)))
(println "long deriv")

(define 3values
  (lambda ( x y z)
    (values x y z)))


(let-values (((a b c) (3values 4 5 6)))
  (+ a c))

(evaluate 'x 1 '(+ 5 (^ x 2) (* 3 3) (* x 10
(+ 1 2 x)) (+ x x)))