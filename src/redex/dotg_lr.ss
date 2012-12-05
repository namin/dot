#lang racket
(require redex)
(require "dotg.ss")

(define-metafunction dot
  fresh-var : any ... -> x
  [(fresh-var any_1 ...) x
   (where x ,(variable-not-in (term (any_1 ...)) 'x))])

(define-judgment-form dot
  #:mode (lrV I I I)
  #:contract (lrV T e env)
  [(lrV T (location i) (Gamma store))
   (where c (store-lookup store i))
   (found c #t)
   (where (Tc (l_c vx_c) ... (m_c x_c e_c) ...) c)
   (subtype (Gamma store) Tc T)
   (where x (fresh-var T Gamma store))
   (expansion (Gamma store) x Tc (((: Lt S U) ...) (Dl ...) (Dm ...)))
   (where ((l_s vx_s) ...) (sorted-assigns ((l_c vx_c) ...)))
   (where ((: l_s V_d) ...) (sorted-decls (Dl ...)))
   (where ((m_s y_ms e_ms) ...) (sorted-method-assigns ((m_c x_c e_c) ...)))
   (where ((: m_s V_md W_md) ...) (sorted-decls (Dm ...)))
   (wfe-type (Gamma store) (subst V_md x (location i))) ...
   (subtype (Gamma store) (subst S x (location i)) (subst U x (location i))) ...
   (typeof (Gamma store) vx_s V_s) ...
   (subtype (Gamma store) V_s (subst V_d x (location i))) ...
   (typeof ((gamma-extend Gamma y_ms (subst V_md x (location i))) store) e_ms W_ms) ...
   (subtype ((gamma-extend Gamma y_ms (subst V_md x (location i))) store) W_ms (subst W_md x (location i))) ...])

(define (lrE T e store_beg)
  (redex-let dot ([(e_ev store_ev) (term (ev ,store_beg ,e))])
             (and (judgment-holds (lrV ,T e_ev (() store_ev))) T)))

(define (test-lr e)
  (if (and (well-formed? e) (typecheck (term (() ())) e))
      (lrE (typecheck (term (() ())) e) e (term ()))
      #t))

;; Examples

(test-lr (term (val u = new (Top) in u)))
(test-lr (term (app (fun x Top Top x) (fun x Top Top x))))
(test-lr (term (val u = new ((rfn Top u (: (cm l) Top Top)) [(cm l) x u]) in (sel u (cm l) u))))
(test-lr (term (val u = new ((rfn Top u (: (cc l) Top Top))) in (app (fun x (sel u (cc l)) Top u) u))))
;(test-lr (dotExample))

(let ((typeX (term (rfn Top z
                        (: (ca A) Top Top)
                        (: (cm l) Top (sel z (ca A))))))
      (typeY (term (rfn Top z
                        (: (cm l) Top Top)))))
  (test-lr
   (term
    (val u = new (,typeX ((cm l) dummy (as (sel u (ca A)) u))) in
    (sel (app (fun y (arrow Top ,typeY) ,typeY (app y (as Top u))) (as (arrow Top ,typeY) (fun d Top ,typeX (cast ,typeX u)))) (cm l) (as Top u))))))

(test-lr
 (term
  (val b = new ((rfn Top z
                     (: (ca X) Top Top)
                     (: (cv l) (sel z (ca X))))
                ((cv l) b)) in
  (val a = new ((rfn Top z
                     (: (cv i) (rfn Top z
                                    (: (ca X) Bot Top)
                                    (: (cv l) (sel z (ca X))))))
                ((cv i) b)) in
  (cast Top
        (cast (sel (sel a (cv i)) (ca X))
              (sel (sel a (cv i)) (cv l))))))))
