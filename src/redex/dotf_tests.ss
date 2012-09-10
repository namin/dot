#lang racket
(require redex)
(require "dotf.ss")

;(require rackunit)
; redefining these so that redex includes them in the summary
(define (check-true e)
  (test-equal e #t))
(define (check-false e)
  (test-equal e #f))
(define (check-not-false e)
  (test-equal (not (not e)) #t))

;; grammar
(check-true (redex-match? dot e (term (val u = new (Top) in u))))
(check-true (redex-match? dot e (term (val u = new ((refinement Top self (: (label-value l) Top)) [(label-value l) u]) in (sel u (label-value l))))))

;; substitution
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (label-method f) Top Top)) [(label-method f) x_2 x_2]) in x_1)
 (term (subst (val u = new ((refinement Top self (: (label-method f) Top Top)) [(label-method f) x x]) in u) x y))))
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (label-method f) Top Top)) [(label-method f) (side-condition x_2 (not (equal? 'y (term x_2)))) y]) in x_1)
 (term (subst (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method f) y x])) u) x y))))
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (label-method f) Top Top)) [(label-method f) (side-condition x_2 (not (equal? 'y (term x_2)))) y]) in x_1)
 (term (subst (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method f) z x])) u) x y))))
(check-true (redex-match? dot
 (val x_1 = new (Top) in y)
 (term (subst (valnew (u (Top)) x) x y))))
(check-true (redex-match? dot
 (val (side-condition x_1 (not (equal? 'u (term x_1)))) = new (Top) in u)
 (term (subst (valnew (u (Top)) x) x u))))
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (label-method mt) Top Top)) [(label-method mt) x_2 x_1]) in (sel x_1 (label-method mt) x_1))
 (term (subst (valnew (u ((refinement Top self (: (label-method mt) Top Top)) [(label-method mt) y u])) (sel u (label-method mt) u)) mt x))))

;; reduction
;(trace-dot (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

;; evaluation
(check-not-false (term (ev () (valnew (u (Top)) u))))
(check-not-false (term (ev () (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method l) x x])) (sel u (label-method l) u)))))
(check-not-false (term (ev () (valnew (u ((refinement Top self (: (label-method l) Top Top)) [(label-method l) x u])) (sel u (label-method l) u)))))

;; type-checking

(test-equal (typecheck (term (() ())) (term (valnew (u (Top)) u)))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (o (Top)) (valnew (o (Top)) o))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-method f) Top Top)) [(label-method f) x x])) u)))
            (term (refinement Top u (: (label-method f) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-method f) Top Top)) [(label-method f) x x])) (sel u (label-method f) u))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-method l) Top Top)) [(label-method l) x u])) (sel u (label-method l) u))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) u)))
            (term (refinement Top u (: (label-class l) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-class l) Top Top))))
                                                    (valnew (w ((refinement Top w (: (label-method f) (sel u (label-class l)) Top))
                                                                [(label-method f) x x]))
                                                            (sel w (label-method f) u)))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-class l) Top Top) (: (label-method f) (sel u (label-class l)) Top))
                                                        [(label-method f) x x]))
                                                    (sel u (label-method f) u))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u
                                                                    (: (label-abstract-type l) Top Top)
                                                                    (: (label-method f) (sel u (label-abstract-type l)) (refinement Top z (: (label-abstract-type l) Top Top))))
                                                        [(label-method f) x u]))
                                                    (sel u (label-method f) u))))
            (term (refinement Top z (: (label-abstract-type l) Top Top))))

;; sugar
(test-equal (typecheck (term (() ())) (term (fun (x Top) Top x)))
            (term (refinement Top f (: (label-method apply) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (d (Top)) (fun (x Top) Top x))))
            (term (refinement Top f (: (label-method apply) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (d (Top)) (app (fun (x Top) Top x) d))))
            'Top)

;(typecheck (term (() ())) (dotExample))

;; soundness
(test-predicate preservation (term (valnew (u (Top)) u)))
(test-predicate preservation (term (app (fun (x Top) Top x) (fun (x Top) Top x))))
(test-predicate preservation (term (valnew (u ((refinement Top u (: (label-method l) Top Top)) [(label-method l) x u])) (sel u (label-method l) u))))
(test-predicate preservation (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) (app (fun (x (sel u (label-class l))) Top u) u))))
;(test-predicate preservation (dotExample))

(test-predicate big-step-preservation (term (valnew (u (Top)) u)))
(test-predicate big-step-preservation (term (app (fun (x Top) Top x) (fun (x Top) Top x))))
(test-predicate big-step-preservation (term (valnew (u ((refinement Top u (: (label-method l) Top Top)) [(label-method l) x u])) (sel u (label-method l) u))))
(test-predicate big-step-preservation (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) (app (fun (x (sel u (label-class l))) Top u) u))))
;(test-predicate big-step-preservation (dotExample))

(test-predicate type-safety (term (valnew (u (Top)) u)))
(test-predicate type-safety (term (app (fun (x Top) Top x) (fun (x Top) Top x))))
(test-predicate type-safety (term (valnew (u ((refinement Top u (: (label-method l) Top Top)) [(label-method l) x u])) (sel u (label-method l) u))))
(test-predicate type-safety (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) (app (fun (x (sel u (label-class l))) Top u) u))))
;(test-predicate type-safety (dotExample))


(check-true (subtyping-transitive (term (([x (refinement Top self (: (label-class L) Bottom (sel self (label-class L))))]) ())) (term (sel x (label-class L))) (term Top) (term (refinement Top z))))
(test-predicate preservation (term (valnew (u ((refinement Top self (: (label-class L) Bottom (sel self (label-class L)))))) (fun (x Top) Top x))))


(check-false
(typecheck (term (() ())) (term (valnew (u ((refinement Top self (: (label-class L) Bottom (sel self (label-class L)))))) (cast Top
(cast (arrow (sel u (label-class L)) (refinement Top z))
      (cast (arrow (sel u (label-class L)) Top)
            (fun (x (sel u (label-class L))) (sel u (label-class L)) x)))
))))
)

(check-false
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                                                        (: (label-abstract-type L1) Bottom (sel self (label-abstract-type L1)))
                                                        (: (label-abstract-type L2) Bottom (refinement Top z (: (label-abstract-type L3) Bottom Top)))
                                                        (: (label-abstract-type L4) (intersection (sel self (label-abstract-type L2)) (sel self (label-abstract-type L1))) (sel self (label-abstract-type L2))))))
                                        (cast Top
(cast (arrow (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))) (refinement Top z (: (label-abstract-type L3) Bottom Top)))
      (cast (arrow (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))) (sel u (label-abstract-type L4)))
            (fun (x (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))))
                 (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1)))
                 x)))
))))
)

(check-true
(let ([env (term (([u (refinement Top self 
                                  (: (label-class Bad) Bottom (sel self (label-class Bad))) 
                                  (: (label-class BadBounds) Top (sel self (label-class Bad))) 
                                  (: (label-class Mix) (sel self (label-class BadBounds)) Top))])
                  ()))]
      [s (term (sel u (label-class BadBounds)))]
      [t (term (sel u (label-class Mix)))]
      [u (term (refinement (sel u (label-class Mix)) z))])
  (subtyping-transitive env s t u))
)

(check-true
(let ([env (term (([u (refinement Top self
                                  (: (label-class Bad) Bottom (sel self (label-class Bad)))
                                  (: (label-class Good) (refinement Top z (: (label-class L) Bottom Top)) (refinement Top z (: (label-class L) Bottom Top)))
                                  (: (label-class Lower) (intersection (sel self (label-class Bad)) (sel self (label-class Good))) (sel self (label-class Good)))
                                  (: (label-class Upper) (sel self (label-class Good)) (union (sel self (label-class Bad)) (sel self (label-class Good))))
                                  (: (label-class X) (sel self (label-class Lower)) (sel self (label-class Upper))))])
                  ()))]
      [s (term (intersection (sel u (label-class Bad)) (sel u (label-class Good))))]
      [t (term (sel u (label-class Lower)))]
      [u (term (refinement (sel u (label-class X)) z (: (label-class L) Bottom Top)))])
  (subtyping-transitive env s t u))
)

(check-true
(let ([Tc (term (refinement Top self
                            (: (label-class Bad) Bottom (sel self (label-class Bad)))
                            (: (label-class Good) (refinement Top z (: (label-class L) Bottom Top)) (refinement Top z (: (label-class L) Bottom Top)))
                            (: (label-class Lower) (intersection (sel self (label-class Bad)) (sel self (label-class Good))) (sel self (label-class Good)))
                            (: (label-class Upper) (sel self (label-class Good)) (union (sel self (label-class Bad)) (sel self (label-class Good))))
                            (: (label-class X) (sel self (label-class Lower)) (sel self (label-class Upper)))))]
      [s (term (intersection (sel u (label-class Bad)) (sel u (label-class Good))))]
      [t (term (sel u (label-class Lower)))]
      [u (term (refinement (sel u (label-class X)) z (: (label-class L) Bottom Top)))])
  (preservation (term (valnew (u (,Tc)) (cast Top
    (cast (arrow ,s ,u)
          (cast (arrow ,s ,t)
                (cast (arrow ,s ,s)
                      (fun (x ,s) ,s x)))))))))
)

(test-equal
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                              (: (label-class Bar) Bottom (refinement Top self (: (label-class T) Bottom Top)))
                              (: (label-class Foo) Bottom (refinement (sel self (label-class Bar)) z (: (label-class T) Bottom (sel self (label-class Foo)))))
                              (: (label-method foo) Top (arrow Top (sel self (label-class Foo)))))
              ((label-method foo) dummy (fun (x Top) (sel u (label-class Foo)) (valnew (foo ((sel u (label-class Foo)))) foo)))))
              (as Top (sel u (label-method foo) (as Top u))))))
'Top)

(test-equal
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                              (: (label-class Bar) Bottom (refinement Top self (: (label-class T) Bottom Top) (: (label-method some) Top (sel self (label-class T)))))
                              (: (label-class Foo) Bottom (refinement (sel self (label-class Bar)) z (: (label-class T) (sel self (label-class Foo)) Top)))
                              (: (label-method foo) Top (arrow Top (sel self (label-class Foo)))))
              ((label-method foo) dummy (fun (x Top) (sel u (label-class Foo)) (valnew (foo ((sel u (label-class Foo)) ((label-method some) dummy (as (sel foo (label-class T)) foo)))) foo)))))
              (cast Top (sel u (label-method foo) (as Top u))))))
'Top)

#;
(let ((w (term (refinement Top b
                           (: (label-class T) Bottom (sel (sel b (label-value x)) (label-class T)))
                           (: (label-value x) (sel u (label-class C)))))))
  (judgment-holds
   (expansion (((u (refinement Top a
                               (: (label-class C) Bottom ,w)))
                (w ,w))
               ())
              z
              (sel w (label-class T))
              ((DLt ...) (Dl ...) (Dm ...)))
   ((DLt ...) (Dl ...) (Dm ...))))

(check-not-false
(typecheck (term (() ())) (term (fun (x Bottom) Top (fun (z (sel x (label-class Lt))) (sel x (label-class Lt)) z))))
)

(check-not-false
(let ((typeX (term (refinement Top z
                               (: (label-abstract-type A) Top Top)
                               (: (label-method l) Top (sel z (label-abstract-type A))))))
      (typeY (term (refinement Top z
                               (: (label-method l) Top Top)))))
  (type-safety
   (term
    (valnew
     (u (,typeX ((label-method l) dummy (as (sel u (label-abstract-type A)) u))))
     (sel (app (fun (y (arrow Top ,typeY)) ,typeY (app y (as Top u))) (as (arrow Top ,typeY) (fun (d Top) ,typeX (cast ,typeX u)))) (label-method l) (as Top u))))))
)

(check-not-false
(let ((typeX (term (refinement Top z
                               (: (label-abstract-type A) Top Top)
                               (: (label-method l) Top (sel z (label-abstract-type A))))))
      (typeY (term (refinement Top z
                               (: (label-method l) Top Top)))))
  (big-step-preservation
   (term
    (valnew
     (u (,typeX ((label-method l) dummy (as (sel u (label-abstract-type A)) u)))) (cast Top
      (app (fun (y (arrow- f ((: (label-abstract-type Y) ,typeX ,typeY)) Top (sel f (label-abstract-type Y)))) 
                (arrow Top Top)
                (fun (d Top) Top (sel (cast (sel y (label-abstract-type Y)) (app y (as Top u))) (label-method l) (as Top u))))
           (as (arrow- f ((: (label-abstract-type Y) ,typeX ,typeY)) Top (sel f (label-abstract-type Y)))
               (fun- f ((: (label-abstract-type Y) ,typeX ,typeX)) (d Top) (sel f (label-abstract-type Y)) (as (sel f (label-abstract-type Y)) u)))))))))
)

(test-predicate type-safety
 (term
  (valnew
   (b ((refinement Top z
                   (: (label-abstract-type X) Top Top)
                   (: (label-value l) (sel z (label-abstract-type X))))
       ((label-value l) b)))
   (valnew
    (a ((refinement Top z
                    (: (label-value i) (refinement Top z
                                                   (: (label-abstract-type X) Bottom Top)
                                                   (: (label-value l) (sel z (label-abstract-type X))))))
        ((label-value i) b)))
    (cast Top
     (cast (sel (sel a (label-value i)) (label-abstract-type X))
      (sel (sel a (label-value i)) (label-value l))))))))

(test-predicate big-step-preservation
 (term
  (valnew
   (b ((refinement Top z
                   (: (label-abstract-type X) Top Top)
                   (: (label-value l) (sel z (label-abstract-type X))))
       ((label-value l) b)))
   (valnew
    (a ((refinement Top z
                    (: (label-value i) (refinement Top z
                                                   (: (label-abstract-type X) Bottom Top)
                                                   (: (label-value l) (sel z (label-abstract-type X))))))
        ((label-value i) b)))
    (cast Top
     (app (fun (x (sel (sel a (label-value i)) (label-abstract-type X)))
               (arrow Top Top)
               (fun (d Top) (sel (sel a (label-value i)) (label-abstract-type X)) x))
          (sel (sel a (label-value i)) (label-value l))))))))

(test-predicate type-safety
 (term
   (valnew
    (b ((refinement Top z
                    (: (label-abstract-type X) Top Top)
                    (: (label-value l) (sel z (label-abstract-type X))))
        ((label-value l) b)))
   (valnew
    (a ((refinement Top z
                    (: (label-value i) (refinement Top z
                                                   (: (label-abstract-type X) Bottom Top)
                                                   (: (label-value l) (sel z (label-abstract-type X))))))
        ((label-value i) b)))
    (cast Top
     (cast (sel (sel a (label-value i)) (label-abstract-type X))
      (sel (sel a (label-value i)) (label-value l))))))))

(test-predicate big-step-preservation
 (term
   (valnew
    (b ((refinement Top z
                    (: (label-abstract-type X) Top Top)
                    (: (label-value l) (sel z (label-abstract-type X))))
        ((label-value l) b)))
   (valnew
    (a ((refinement Top z
                    (: (label-value i) (refinement Top z
                                                   (: (label-abstract-type X) Bottom Top)
                                                   (: (label-value l) (sel z (label-abstract-type X))))))
        ((label-value i) b)))
    (cast Top
     (app (fun (x (sel (sel a (label-value i)) (label-abstract-type X)))
               (arrow Top (sel (sel a (label-value i)) (label-abstract-type X)))
               (fun (d Top) (sel (sel a (label-value i)) (label-abstract-type X)) x))
          (sel (sel a (label-value i)) (label-value l))))))))

(check-true
(let* ([typeX (term (refinement Top z
                                (: (label-abstract-type A) Top Top)
                                (: (label-abstract-type B) Top Top)
                                (: (label-abstract-type C) Bottom (sel z (label-abstract-type B)))))]
       [typeY (term (refinement Top z
                                (: (label-abstract-type A) Bottom Top)
                                (: (label-abstract-type B) Bottom Top)
                                (: (label-abstract-type C) Bottom (sel z (label-abstract-type A)))))]
       [typeZ (term (refinement ,typeX z
                                (: (label-abstract-type A) Bottom Bottom)
                                (: (label-abstract-type B) Bottom Bottom)))])
  (subtyping-transitive (term (() ())) typeZ typeX typeY))
)

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z (: (label-class L) Bottom (refinement Top z (: (label-abstract-type A) Top Bottom))))))
          (app (fun (x (refinement Top z (: (label-class L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top)))))
                    Top
                    (valnew (z ((sel x (label-class L)))) (cast Top z)))
               v))))

(test-predicate type-safety
 (term
  (valnew (v ((refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom (sel z (label-abstract-type A))))))))
  (app (fun (x (refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom Top))))) Top
            (valnew (z ((refinement Top z (: (label-method l)
                                             (intersection
                                              (sel x (label-abstract-type L))
                                              (refinement Top z (: (label-abstract-type A) Bottom (sel z (label-abstract-type B))) (: (label-abstract-type B) Bottom Top)))
                                             Top))
                        ((label-method l) y
                                          (as Top (fun (a (sel y (label-abstract-type A))) Top a)))))
                    (cast Top z)))
       (as (refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom Top)))) v)))))

(test-predicate type-safety
 (term
  (valnew (x00 ((refinement Top z (: (label-abstract-type L) Bottom
                                     (refinement Top self
                                                 (: (label-abstract-type A) Bottom Top)
                                                 (: (label-abstract-type B) Bottom Top)
                                                 (: (label-class Lc2) Bottom (sel self (label-abstract-type A))))))))
  (valnew (x0 ((refinement Top z (: (label-class Lc1) Bottom (refinement Top z (: (label-abstract-type L) Bottom (sel x00 (label-abstract-type L))))))))
  (valnew (x1 ((refinement (sel x0 (label-class Lc1)) z (: (label-abstract-type L) Bottom 
                                                           (refinement (sel x00 (label-abstract-type L)) self 
                                                                       (: (label-abstract-type A) Bottom (sel self (label-abstract-type B))))))))
  (valnew (x2 ((refinement (sel x0 (label-class Lc1)) z (: (label-abstract-type L) Bottom 
                                                           (refinement (sel x00 (label-abstract-type L)) self 
                                                                       (: (label-abstract-type B) Bottom (sel self (label-abstract-type A))))))))
  (app (fun (x (sel x0 (label-class Lc1))) Top
            (fun (z0 (intersection (sel x (label-abstract-type L)) (sel x2 (label-abstract-type L)))) Top
                 (valnew (z ((sel z0 (label-class Lc2))))
                         (cast Top z))))
       (as (sel x0 (label-class Lc1)) x1))))))))

(test-predicate type-safety
 (term
  (valnew (v ((refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) (sel z (label-abstract-type A)) Top))))))
  (app (fun (x (refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom Top))))) Top
            (valnew (z ((refinement Top z (: (label-method l)
                                             (intersection
                                              (sel x (label-abstract-type L))
                                              (refinement Top z (: (label-abstract-type A) (sel z (label-abstract-type B)) Top) (: (label-abstract-type B) Bottom Top)))
                                             Top))
                        ((label-method l) y
                                          (as Top (fun (a (sel y (label-abstract-type A))) Top a)))))
                    (cast Top z)))
       (as (refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom Top)))) v)))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z (: (label-abstract-type L) Bottom Top) (: (label-value l) (refinement Top z (: (label-abstract-type L) Bottom Top))))
              ((label-value l) v)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-value l) Top)) v) (label-value l))))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z (: (label-method m) Top Top))
              ((label-method m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-method m) (refinement Top z (: (label-method m) Top Top)) Top)) v)
            (label-method m)
            v)))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z
                          (: (label-abstract-type A) Top Top)
                          (: (label-method m) (refinement Top z (: (label-abstract-type A) Top Top)) (refinement Top z (: (label-abstract-type A) Top Top))))
             ((label-method m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-method m) (refinement Top z (: (label-abstract-type A) Top Top)) Top)) v)
            (label-method m)
            (as (refinement Top z (: (label-abstract-type A) Top Top)) v))))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z
                          (: (label-abstract-type A) Top Top)
                          (: (label-abstract-type B) Bottom Top)
                          (: (label-method m) (refinement Top z (: (label-abstract-type A) Top Top)) (refinement Top z (: (label-abstract-type A) Top Top))))
             ((label-method m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-method m) (refinement Top z (: (label-abstract-type A) Top Top) (: (label-abstract-type B) Bottom Top)) Top)) v)
            (label-method m)
            (as (refinement Top z (: (label-abstract-type A) Top Top) (: (label-abstract-type B) Bottom Top)) v))))))

(test-predicate type-safety
 (term
  (valnew (v ((refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom (sel z (label-abstract-type A))))))))
  (app (as (arrow (refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom (sel z (label-abstract-type A)))))) Top)
           (fun (x (refinement Top z (: (label-abstract-type L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top) (: (label-abstract-type B) Bottom Top))))) Top
                (valnew (z ((refinement Top z (: (label-method l)
                                                 (intersection
                                                  (sel x (label-abstract-type L))
                                                  (refinement Top z (: (label-abstract-type A) Bottom (sel z (label-abstract-type B))) (: (label-abstract-type B) Bottom Top)))
                                                 Top))
                            ((label-method l) y (as Top (fun (a (sel y (label-abstract-type A))) Top a)))))
                        (cast Top z))))
       v))))

(check-not-false
(let ((Tc (term (refinement Top z
                            (: (label-abstract-type A) (refinement Top z (: (label-method m) Bottom Top)) Top)
                            (: (label-abstract-type B) Top Top)
                            (: (label-method m) (sel z (label-abstract-type A)) Top))))
      (T  (term (refinement Top z
                            (: (label-abstract-type A) (refinement Top z (: (label-method m) Bottom Top)) Top)
                            (: (label-abstract-type B) Top Top)
                            (: (label-method m) (refinement (sel z (label-abstract-type A)) z (: (label-abstract-type B) Top Top)) Top)))))
  (preservation
   (term
    (valnew (v (,Tc ((label-method m) x (as Top x))))
    (as Top
        (sel (as ,T v)
             (label-method m)
             v))))))
)

(test-predicate preservation
 (term
  (valnew (a ((refinement Top z
                          (: (label-class C) Bottom (refinement Top z
                                                                (: (label-class D) Bottom (sel z (label-abstract-type X)))
                                                                (: (label-abstract-type X) Bottom Top))))))
  (valnew (b ((refinement (sel a (label-class C)) z
                          (: (label-abstract-type X) Bottom Bottom))))
  (valnew (c ((sel a (label-class C))))
  (app (fun (x (sel a (label-class C))) Top
            (valnew (d ((sel x (label-class D))))
                    (app (fun (x Bottom) Bottom (sel x (label-value foo)))
                         d)))
       b))))))

(check-not-false
(let ((Tc (term (refinement Top z
                            (: (label-abstract-type A) (refinement Top z (: (label-method m) Bottom Top)) Top)
                            (: (label-abstract-type B) Top Top)
                            (: (label-method m) (sel z (label-abstract-type A)) Top))))
      (T  (term (refinement Top z
                            (: (label-abstract-type A) (refinement Top z (: (label-method m) Bottom Top)) Top)
                            (: (label-abstract-type B) Top Top)
                            (: (label-method m) (refinement (sel z (label-abstract-type A)) z (: (label-abstract-type B) Top Top)) Top)))))
  (preservation
   (term
    (valnew (v (,Tc ((label-method m) x x)))
    (valnew (u ((refinement Top z (: (label-value v) ,Tc))
                ((label-value v) v)))
    (as Top
        (sel (as ,T (sel u (label-value v)))
             (label-method m)
             (app (fun (h ,T) Top (as (refinement (sel h (label-abstract-type A)) z (: (label-abstract-type B) Top Top)) v))
                  (sel u (label-value v))))))))))
)

(test-results)