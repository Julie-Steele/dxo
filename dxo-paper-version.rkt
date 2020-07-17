#lang racket
(require "faster-miniKanren-master/mk.rkt")
(require "faster-miniKanren-master/numbers.rkt")

;defines ^ as expt
(define ^ (lambda (a b) (expt a b)))

;defines ZERO and ONE
(define ZERO `(num ,(build-num 0)))
(define ONE `(num ,(build-num 1)))


;multiplies: (* a b)=c
(define timeso
  (lambda (a b c)
    (fresh (bm1 rec d)
      (conde
        ((== (build-num 0) b) (== (build-num 0) c))
        (;(poso b)
         (=/= (build-num 0) b)
         (pluso bm1 (build-num 1) b)
         (timeso a bm1 rec)
         (pluso a rec c))))))

;exponent: (^ a b)=c
(define expo
  (lambda (a b c)
    (fresh (bm1 rec)
      (conde
        ((== (build-num 0) b) (== (build-num 1) c))
        ((=/= (build-num 0) b)
         (pluso bm1 (build-num 1) b)
         (expo a bm1 rec)
         (timeso a rec c))))))

;atom?
(define atom?
  (lambda (expr)
    (cond
      ((list? expr) #f)
      ((null? expr) #f)
      (else #t))))

;atom, null, or list 
(define typeo
  (lambda (expr answer)
    (fresh (a b)
      (conde
        ((== `(,a . ,b) expr)(== 'list answer)(=/= 'num a)(=/= 'var a))
        ((== `() expr) (== 'null answer))
        ((== `(num ,a) expr)(== 'atom answer))
        ((== `(var ,a) expr)(== 'atom answer))
        ((== '+ expr) (== '+or* answer))
        ((== '* expr) (== '+or* answer))))))
        
;minikanren number
(define numo
  (lambda (n)
    (fresh (b rest)
      (conde
        ((== '() n))
        ((== `(,b . ,rest) n)
         (conde
           ((== '1 b))
           ((== '0 b)))
         (numo rest))))))
         
;empty env 
(define empty-env `())

;ext-env
(define ext-env
  (lambda (x v env)
    (cons `(,x . ,v) env)))

;lookupo
(define lookupo
  (lambda (x env v)
    (fresh (env* y w)
      (conde
        ((== `((,x . ,v) . ,env*) env))
        ((== `((,y . ,w) . ,env*) env) (=/= y x) (lookupo x env* v))))))
      
;unbuild-numinner to every element and if list, then to list
(define unbuild-numhelper
  (lambda (expr)
    (cond
      ((null? expr) '())
      ((list? (car expr)) (cons (unbuild-numinner (car expr)) (unbuild-numhelper (cdr expr))))
      (else (cons (car expr) (unbuild-numhelper (cdr expr)))))))

;calls unbuld-numinner for every answer in minikanren 
(define unbuild-num
  (lambda (expr)
    (cond
      ((null? expr) '())
      (else (cons (unbuild-numinner (car expr)) (unbuild-num (cdr expr)))))))

;undoes build-num by calling unbinary 
(define unbuild-numinner
  (lambda (expr)
    (match expr
      [`() `()]
      [`(num ,b) `(num ,(unbinary b 1))]
      [`(var ,b) `(var ,b)]
      [`(+ ,e . ,e*) (unbuild-numhelper `(,e . ,e*))]
      [`(* ,e . ,e*) (unbuild-numhelper `(,e . ,e*))]
      [`(^ ,e . ,e*) (unbuild-numhelper `(,e . ,e*))])))

;helper for unbuild-numinner that goes from binary to base 10
(define unbinary
  (lambda (expr n)
    (cond
      ((null? expr) 0)
      ((atom? expr) expr)
      ((equal? (car expr) 1) (+ n (unbinary (cdr expr) (* 2 n))))
      ((equal? (car expr) 0) (unbinary (cdr expr) (* 2 n))))))


;l contains item 
(define membero
  (lambda (item l)
    (fresh (a rest)
      (conde
        ((== `(,item . ,rest) l))
        ((== `(,a . ,rest) l) (=/= item a) (membero item rest))))))

;l does not contain item
(define notmembero
  (lambda (item l)
    (fresh (a rest)
      (conde
        ((== '() l))
        ((== `(,a . ,rest) l)
         (=/= a item) 
         (notmembero item rest))))))
             
;removes item from l 
(define removeo
  (lambda (item contain removed)
    (fresh (rest rest2 c)
      (conde
        ((== `(,item . ,rest) contain)
         (== rest removed))
            
        ((== `(,c . ,rest) contain)
         (=/= item c)
         (== `(,c . ,rest2) removed)
         (removeo item rest rest2))))))


;the implementation of dxo uses these definitions from the faster-miniKanren 
;implementation of miniKanren, based on the relational arithmetic system
; created by Oleg Kiselyov------------------------
(define samelengtho
  (lambda (e1 e2)
    (fresh (c1 c2 rest1 rest2)
      (conde
        ((== '() e1) (== '() e2))
        ((== `(,c1 . ,rest1) e1) (== `(,c2 . ,rest2) e2) (samelengtho rest1 rest2))))))

(define poso
  (lambda (n)
    (fresh (a d)
      (== `(,a . ,d) n))))

(define >1o
  (lambda (n)
    (fresh (a ad dd)
      (== `(,a ,ad . ,dd) n))))

(define =lo
  (lambda (n m)
    (conde
      ((== '() n) (== '() m))
      ((== '(1) n) (== '(1) m))
      ((fresh (a x b y)
         (== `(,a . ,x) n) (poso x)
         (== `(,b . ,y) m) (poso y)
         (=lo x y))))))

(define <lo
  (lambda (n m)
    (conde
      ((== '() n) (poso m))
      ((== '(1) n) (>1o m))
      ((fresh (a x b y)
         (== `(,a . ,x) n) (poso x)
         (== `(,b . ,y) m) (poso y)
         (<lo x y))))))

(define <=lo
  (lambda (n m)
    (conde
      ((=lo n m))
      ((<lo n m)))))

(define <o
  (lambda (n m)
    (conde
      ((<lo n m))
      ((=lo n m)
       (fresh (x)
         (poso x)
         (pluso n x m))))))

(define <=o
  (lambda (n m)
    (conde
      ((== n m))
      ((<o n m)))))

(define odd-*o
  (lambda (x n m p)
    (fresh (q)
      (bound-*o q p n m)
      (*o x m q)
      (pluso `(0 . ,q) m p))))

(define bound-*o
  (lambda (q p n m)
    (conde
      ((== '() q) (poso p))
      ((fresh (a0 a1 a2 a3 x y z)
         (== `(,a0 . ,x) q)
         (== `(,a1 . ,y) p)
         (conde
           ((== '() n)
            (== `(,a2 . ,z) m)
            (bound-*o x y z '()))
           ((== `(,a3 . ,z) n) 
            (bound-*o x y z m))))))))

(define *o
  (lambda (n m p)
    (conde
      ((== '() n) (== '() p))
      ((poso n) (== '() m) (== '() p))
      ((== '(1) n) (poso m) (== m p))
      ((>1o n) (== '(1) m) (== n p))
      ((fresh (x z)
         (== `(0 . ,x) n) (poso x)
         (== `(0 . ,z) p) (poso z)
         (>1o m)
         (*o x m z)))
      ((fresh (x y)
         (== `(1 . ,x) n) (poso x)
         (== `(0 . ,y) m) (poso y)
         (*o m n p)))
      ((fresh (x y)
         (== `(1 . ,x) n) (poso x)
         (== `(1 . ,y) m) (poso y)
         (odd-*o x n m p))))))

"SIMPLIFY";----------------------------------------------------------

(define simpo
  (lambda (comp simp)
    (fresh ()
      (conde
        ((fresh (n)
           (== `(num ,n) comp)
           (== comp simp)))
        ((fresh (v)
           (== `(var ,v) comp)
           (== comp simp)))
        
        ((fresh (e1 e2 s1 s2)
           (== `(^ ,e1 ,e2) comp)
           (conde
             ((== ONE s1) (== ONE simp))
             ((== ZERO s1) (=/= ZERO s2) (== ZERO simp))
             ((=/= ZERO s1) (== ZERO s2) (=/= ONE s1) (== ONE simp))
             ((=/= ZERO s1) (=/= ONE s1) (== ONE s2) (== s1 simp))
             ((== `(^ ,s1 ,s2) simp)
              (=/= ONE s1)
              (=/= ONE s2)
              (=/= ZERO s1)
              (=/= ZERO s2)))
           (simpo e1 s1)
           (simpo e2 s2)))

        ((fresh (e e* s temp t* n v)
           (== `(* ,e . ,e*) comp)
           (conde
             ((== '() e*) (simpo e simp))
             ((== ZERO s)(=/= '() e*)(== ZERO simp))
             ((== ONE s)(=/= '() e*) (simpo `(* . ,e*) simp))
             ((=/= ONE s)
              (=/= ZERO s)
              (=/= '() e*) 
              (conde
                ((== ZERO temp) (== ZERO simp))
                ((== ONE temp) (== s simp))
                ((== `(^ . ,n) temp) (== `(* ,s ,temp) simp))
                ((== `(+ . ,n) temp) (== `(* ,s ,temp) simp))
                ((== `(num ,n) temp) (=/= ZERO temp) 
                 (=/= ONE temp) (== `(* ,s ,temp) simp))
                ((== `(var ,v) temp) (== `(* ,s ,temp) simp))
                ((==`(* . ,t*) temp) (== `(* ,s . ,t*) simp)))
              (simpo `(* . ,e*) temp)))
           (simpo e s)
           ))

        ((fresh (e e* s temp t* n v)
           (== `(+ ,e . ,e*) comp)
           (conde
             ((== '() e*) (simpo e simp))
             ((== ZERO s)(=/= '() e*)(simpo `(+ . ,e*) simp))
             ((=/= ZERO s)
              (=/= '() e*)
              (conde
                ((== ZERO temp) (== s simp))
                ((== `(^ . ,n) temp) (== `(+ ,s ,temp) simp))
                ((== `(* . ,n) temp) (== `(+ ,s ,temp) simp)) 
                ((== `(num ,n) temp) (=/= ZERO temp) (== `(+ ,s ,temp) simp))
                ((== `(var ,v) temp) (== `(+ ,s ,temp) simp))
                ((== `(+ . ,t*) temp) (== `(+ ,s . ,t*) simp)))
              (simpo `(+ . ,e*) temp)))
           (simpo e s)))))))


"DERIVATIVE";----------------------------------------------------------

;takes derivative        
(define do
  (lambda (x expr deriv)
    (fresh ()
      (symbolo x)
      (conde
        ((fresh (d* e* a b c d)
           (== expr `(+ . ,e*)) (== e* `(,a . ,b))
           (== deriv `(+ . ,d*)) (== d* `(,c . ,d))
           (samelengtho e* d*)
           (map-do-o x e* d*)))

        ((fresh ()
           (== expr `(^ (var ,x) (num ,(build-num 0))))
           (== deriv ZERO)))

        ((fresh (l e)
           (== expr `(* . ,l))       
           (letrec ((multruleo
                     (lambda (l dd)
                       (fresh (e e* d d* a b)
                         (conde
                           [(== l `(,e))
                            (do x e dd)
                            ]
                           [(== l `(,e . ,e*))
                            (== e* `(,a . ,b))
                            (== dd `(+ (* ,d . ,e*) (* ,e ,d*)))
                            (do x e d)
                            (multruleo e* d*)
                            ])))))
             (multruleo l deriv))))
        
        ((fresh (int intm1)
           (== expr  `(^ (var ,x) (num ,int)))
           (== deriv `(* (^ (var ,x) (num ,intm1)) (num ,int)))
           (minuso int (build-num 1) intm1)))

        ((fresh (int1 int2)
           (== expr `(^ (num ,int1) (num ,int2)))
           (== deriv ZERO)
           (conde
             ((poso int1))
             ((== ZERO int1)(poso int2)))
              ))

        ((fresh ()
           (== expr `(var ,x))
           (== deriv ONE)))
                    
        ((fresh (int)
           (== expr `(num ,int))
           (== deriv ZERO)))))))

;maps do function 
(define map-do-o
  (lambda (x expr* output)
    (fresh (e* e out out*)
      (conde 
        [(== expr* '()) (== output '())]
        [(== expr* `(,e . ,e*))
         (== output `(,out . ,out*))
         (do x e out)
         (map-do-o x e* out*)]))))

"EVALUATE";------------------------------------------------------------

;evaluater
(define evalo
  (lambda (env expr value)
    (fresh (m x c a b rest evc evrest eva evb)
      (conde
        ((== `(var ,x) expr) (lookupo x env value))
        ((== `(num ,m) expr) (numo m) (== m value))
        ((== `(+ ,c . ,rest) expr)
         (conde
           ((== '() rest) (evalo env c value))
           ((=/= '() rest)
            (evalo env c evc)
            (evalo env `(+ . ,rest) evrest)
            (pluso evc evrest value))))
        ((== `(* ,c . ,rest) expr)
         (conde
           ((== '() rest) (evalo env c value))
           ((=/= '() rest)
            (evalo env c evc)
            (evalo env `(* . ,rest) evrest)
            (*o evc evrest value))))
        ((== `(^ ,a ,b) expr)
         (evalo env a eva)
         (evalo env b evb)
         (expo eva evb value))))))

"REORDER";______________________________________________________________

;another option instead of using reordero is to always enter expressions in the same right order 
;reorders expression deeply, reordering any + and * expressions 
(define reordero
  (lambda (e1 e2)
    (fresh ()
      (conde
        ((== e1 e2) (typeo e1 'atom))
        ((fresh (o e1* e2*)
           (== `(,o . ,e1*) e1)
           (== `(,o . ,e2*) e2)
           (typeo o '+or*)
           (reorderitemso e1* e2*)))
        ((fresh (a1 b1 a2 b2)
           (== `(^ ,a1 ,b1) e1)
           (== `(^ ,a2 ,b2) e2)
           (reordero a1 a2)
           (reordero b1 b2)))))))


;permutes a list by calling reorderinnero, and calls reordero on the items in the list deeply
(define reorderitemso
  (lambda (e1* e2*)
    (fresh ()
      (samelengtho e1* e2*)
      (reorderinnero e1* e2*))))



;permutes and calls reordero on the items, helper for reorderitemso
(define reorderinnero
  (lambda (e1* e2*)
    (fresh (c1 rc1 rest1 rest2)
      (conde
        ((== '() e1*)(== '() e2*))
        ((== `(,c1 . ,rest1) e1*)
         (removeo rc1 e2* rest2)
         (reorderinnero rest1 rest2)
         (reordero c1 rc1)
         )))))

"ANYDO";__________________________________________________________________________________

(define anydo
  (lambda (expr deriv x)
    (fresh (ecomp dcomp esimp dsimp dcorder)
      (project (expr deriv)
        (if (var? expr)
            (fresh ()
              (simpo deriv dsimp)
              (simpo dcorder dsimp)
              (reordero dcomp dcorder)
              (do x ecomp dcomp)
              (simpo ecomp esimp)
              (simpo expr esimp))
            
            (fresh ()
              (simpo expr esimp)
              (simpo ecomp esimp)
              (do x ecomp dcomp)
              (reordero dcomp dcorder)
              (simpo dcorder dsimp)
              (simpo deriv dsimp)))))))


(define doitallevalo
  (lambda (ieval inte deriv deval x env)
    (fresh (icomp dcomp isimp dsimp dcorder)
      (evalo env inte ieval)
      (evalo env deriv deval)
      (do x icomp dcomp)
      (reordero dcomp dcorder)
      (simpo deriv dsimp)
      (simpo dcorder dsimp)
      (simpo inte isimp)
      (simpo icomp isimp))))





