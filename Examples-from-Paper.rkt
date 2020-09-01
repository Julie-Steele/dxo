#lang racket
(require "faster-miniKanren/mk.rkt")
(require "faster-miniKanren/numbers.rkt")
(require "dxo-paper-version.rkt")

;introduction 
(run 200 (expr) (evalo `((z . (0 1))) expr '(0 0 0 1)))      ; z\(=2, \)value\(=8\)

(run* (q) (do 'x
    '(+ (^ (var x) (num (1 1))) (^ (var x) (num ())))        ; \(x\sp{3}+x\sp{0}=\) expr
    '(+ (* (^ (var x) (num (0 1))) (num (1 1))) (num ()))))   ; \((x\sp{2}*3)+0=\) deriv

(run* (q) (do 'x
    '(+ (^ (var x) (num (1 1))) (^ (var x) (num ())))      ; \(x\sp{3}+x\sp{0}=\) expr
    '(* (num (1)) (^ (var x) (num (0 1))) (num (1 1)))))    ; \(1*x\sp{2}*3=\) deriv


(run 1 (q) (anydo '(+ (^ (var x) (num (1 1))) (^ (var x) (num ())))     ; \(x\sp{3}+x\sp{0}=\) expr
       '(* (num (1)) (^ (var x) (num (0 1))) (num (1 1)))    ; \(1*x\sp{2}*3=\) deriv
       'x))


;simpo

(run* (simp) (simpo '(^ (num (1)) (num (1))) simp))       ; \(1\sp{1}=\) comp

;diverges:
;(run 1 (comp) (simpo comp '(^ (num (1)) (num (1)))))       ; \(1\sp{1}=\) simp

(run* (q) (simpo `(^ (num  (1)) (num (1)))             ; \(1\sp{1}=\) comp
                 `(+ . ,q)))                           ; simp is some addition expression


;do

(run 24 (expr deriv) (do 'x expr deriv))

(run 1 (expr)(do 'x expr '(* (^ (var x) (num (1))) (num (0 1))))) ; \(x\sp{1}*2=\) deriv 

;diverges 
;(run 1 (expr)(do 'x expr '(* (num (0 1)) (^ (var x) (num (1)))))) ; \(2*x\sp{1}=\) deriv

;evalo 
(run 200 (expr) (evalo `((z . (0 1))) expr '(0 0 0 1)))      ; z\(=2, \)value\(=8\)

(run 1 (env)
  (fresh (xv yv zv z2v)
    (== `((x . ,xv) (y . ,yv) (z . ,zv) (z-squared . ,z2v)) env)
    (evalo env `(+ (^ (var x) (num (0 1))) (^ (var y) (num (0 1)))) z2v)
    (*o zv zv z2v)))

(run 1 (env)
  (fresh (xv yv zv z2v)
    (poso xv)
    (poso yv)
    (poso zv)
    (== `((x . ,xv) (y . ,yv) (z . ,zv) (z-squared . ,z2v)) env)
    (evalo env `(+ (^ (var x) (num (0 1))) (^ (var y) (num (0 1)))) z2v)
    (*o zv zv z2v)))

;reordero
(run* (e2) (reordero `(+ (num (1)) (* (num (0 1)) (num (1 1)))) e2))   ; \(1+2*3=\) e1



























