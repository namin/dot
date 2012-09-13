#lang racket
(require redex)
(require "dotf.ss")

(define-metafunction dot
  e-subtype : S U -> e
  [(e-subtype S U) 
   (cast Top (fun x S U x))
   (where x ,(variable-not-in (term (S U)) 'x))])

(define-metafunction dot
  e-vals : ((x c) ...) e -> e
  [(e-vals () e) e]
  [(e-vals ((x_1 c_1) (x_r c_r) ...) e) (val x_1 = new c_1 in (e-vals ((x_r c_r) ...) e))])

(define-syntax (check-dot stx)
  (syntax-case stx ()
    [(_ ([valname valtype valbind ...] ...) e ...)
     #'(and (if
             (typecheck
              (term (() ()))
              (term (e-vals ((valname (valtype valbind ...)) ... ) e)))
             #t
             (begin (display 'e) #f))
            ...)]))


(check-dot
 ([u (rfn Top u
          (: (cc Pet) Bot Top)
          (: (cc Dog) Bot (sel u (cc Pet)))
          (: (cc Cat) Bot (sel u (cc Pet)))
          (: (cc Poodle) Bot (sel u (cc Dog))))])
 (cast Top u)
 (e-subtype (sel u (cc Dog)) (sel u (cc Pet)))
 (e-subtype (sel u (cc Poodle)) (sel u (cc Dog)))
)