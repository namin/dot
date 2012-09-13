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
 ([pets (rfn Top z
             (: (cc Pet) Bot Top)
             (: (cc Dog) Bot (sel z (cc Pet)))
             (: (cc Cat) Bot (sel z (cc Pet)))
             (: (cc Poodle) Bot (sel z (cc Dog))))])
 (cast Top pets)
 (e-subtype (sel pets (cc Dog)) (sel pets (cc Pet)))
 (e-subtype (sel pets (cc Poodle)) (sel pets (cc Dog)))
)