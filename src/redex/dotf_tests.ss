#lang racket
(require redex)
(require "dotf.ss")

(define-metafunction dot
  valnew : (x c) e -> e
  [(valnew (x c) e) (val x = new c in e)])

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
(check-true (redex-match? dot e (term (val u = new ((refinement Top self (: (cv l) Top)) [(cv l) u]) in (sel u (cv l))))))

;; substitution
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (cm f) Top Top)) [(cm f) x_2 x_2]) in x_1)
 (term (subst (val u = new ((refinement Top self (: (cm f) Top Top)) [(cm f) x x]) in u) x y))))
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (cm f) Top Top)) [(cm f) (side-condition x_2 (not (equal? 'y (term x_2)))) y]) in x_1)
 (term (subst (valnew (u ((refinement Top self (: (cm f) Top Top)) [(cm f) y x])) u) x y))))
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (cm f) Top Top)) [(cm f) (side-condition x_2 (not (equal? 'y (term x_2)))) y]) in x_1)
 (term (subst (valnew (u ((refinement Top self (: (cm f) Top Top)) [(cm f) z x])) u) x y))))
(check-true (redex-match? dot
 (val x_1 = new (Top) in y)
 (term (subst (valnew (u (Top)) x) x y))))
(check-true (redex-match? dot
 (val (side-condition x_1 (not (equal? 'u (term x_1)))) = new (Top) in u)
 (term (subst (valnew (u (Top)) x) x u))))
(check-true (redex-match? dot
 (val x_1 = new ((refinement Top self (: (cm mt) Top Top)) [(cm mt) x_2 x_1]) in (sel x_1 (cm mt) x_1))
 (term (subst (valnew (u ((refinement Top self (: (cm mt) Top Top)) [(cm mt) y u])) (sel u (cm mt) u)) mt x))))

;; reduction
;(trace-dot (term (valnew (u ((refinement Top self (: (cv l) Top)) [(cv l) u])) (sel u (cv l)))))

;; evaluation
(check-not-false (term (ev () (valnew (u (Top)) u))))
(check-not-false (term (ev () (valnew (u ((refinement Top self (: (cm f) Top Top)) [(cm l) x x])) (sel u (cm l) u)))))
(check-not-false (term (ev () (valnew (u ((refinement Top self (: (cm l) Top Top)) [(cm l) x u])) (sel u (cm l) u)))))

;; type-checking

(test-equal (typecheck (term (() ())) (term (valnew (u (Top)) u)))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (o (Top)) (valnew (o (Top)) o))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (cm f) Top Top)) [(cm f) x x])) u)))
            (term (refinement Top u (: (cm f) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (cm f) Top Top)) [(cm f) x x])) (sel u (cm f) u))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (cm l) Top Top)) [(cm l) x u])) (sel u (cm l) u))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (cc l) Top Top)))) u)))
            (term (refinement Top u (: (cc l) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (cc l) Top Top))))
                                                    (valnew (w ((refinement Top w (: (cm f) (sel u (cc l)) Top))
                                                                [(cm f) x x]))
                                                            (sel w (cm f) u)))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (cc l) Top Top) (: (cm f) (sel u (cc l)) Top))
                                                        [(cm f) x x]))
                                                    (sel u (cm f) u))))
            'Top)
(test-equal (typecheck (term (() ())) (term (valnew (u ((refinement Top u
                                                                    (: (ca l) Top Top)
                                                                    (: (cm f) (sel u (ca l)) (refinement Top z (: (ca l) Top Top))))
                                                        [(cm f) x u]))
                                                    (sel u (cm f) u))))
            (term (refinement Top z (: (ca l) Top Top))))

;; sugar
(test-equal (typecheck (term (() ())) (term (fun (x Top) Top x)))
            (term (refinement Top f (: (cm apply) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (d (Top)) (fun (x Top) Top x))))
            (term (refinement Top f (: (cm apply) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (d (Top)) (app (fun (x Top) Top x) d))))
            'Top)
;(test-equal (typecheck (term (() ())) (dotExample)) 'Top)

;; soundness
(test-predicate preservation (term (valnew (u (Top)) u)))
(test-predicate preservation (term (app (fun (x Top) Top x) (fun (x Top) Top x))))
(test-predicate preservation (term (valnew (u ((refinement Top u (: (cm l) Top Top)) [(cm l) x u])) (sel u (cm l) u))))
(test-predicate preservation (term (valnew (u ((refinement Top u (: (cc l) Top Top)))) (app (fun (x (sel u (cc l))) Top u) u))))
;(test-predicate preservation (dotExample))

(test-predicate big-step-preservation (term (valnew (u (Top)) u)))
(test-predicate big-step-preservation (term (app (fun (x Top) Top x) (fun (x Top) Top x))))
(test-predicate big-step-preservation (term (valnew (u ((refinement Top u (: (cm l) Top Top)) [(cm l) x u])) (sel u (cm l) u))))
(test-predicate big-step-preservation (term (valnew (u ((refinement Top u (: (cc l) Top Top)))) (app (fun (x (sel u (cc l))) Top u) u))))
;(test-predicate big-step-preservation (dotExample))

(test-predicate type-safety (term (valnew (u (Top)) u)))
(test-predicate type-safety (term (app (fun (x Top) Top x) (fun (x Top) Top x))))
(test-predicate type-safety (term (valnew (u ((refinement Top u (: (cm l) Top Top)) [(cm l) x u])) (sel u (cm l) u))))
(test-predicate type-safety (term (valnew (u ((refinement Top u (: (cc l) Top Top)))) (app (fun (x (sel u (cc l))) Top u) u))))
;(test-predicate type-safety (dotExample))


(check-true (subtyping-transitive (term (([x (refinement Top self (: (cc L) Bottom (sel self (cc L))))]) ())) (term (sel x (cc L))) (term Top) (term (refinement Top z))))
(test-predicate preservation (term (valnew (u ((refinement Top self (: (cc L) Bottom (sel self (cc L)))))) (fun (x Top) Top x))))


(check-false
(typecheck (term (() ())) (term (valnew (u ((refinement Top self (: (cc L) Bottom (sel self (cc L)))))) (cast Top
(cast (arrow (sel u (cc L)) (refinement Top z))
      (cast (arrow (sel u (cc L)) Top)
            (fun (x (sel u (cc L))) (sel u (cc L)) x)))
))))
)

(check-false
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                                                        (: (ca L1) Bottom (sel self (ca L1)))
                                                        (: (ca L2) Bottom (refinement Top z (: (ca L3) Bottom Top)))
                                                        (: (ca L4) ((sel self (ca L2)) ∧ (sel self (ca L1))) (sel self (ca L2))))))
                                        (cast Top
(cast (arrow ((sel u (ca L2)) ∧ (sel u (ca L1))) (refinement Top z (: (ca L3) Bottom Top)))
      (cast (arrow ((sel u (ca L2)) ∧ (sel u (ca L1))) (sel u (ca L4)))
            (fun (x ((sel u (ca L2)) ∧ (sel u (ca L1))))
                 ((sel u (ca L2)) ∧ (sel u (ca L1)))
                 x)))
))))
)

(check-true
(let ([env (term (([u (refinement Top self 
                                  (: (cc Bad) Bottom (sel self (cc Bad))) 
                                  (: (cc BadBounds) Top (sel self (cc Bad))) 
                                  (: (cc Mix) (sel self (cc BadBounds)) Top))])
                  ()))]
      [s (term (sel u (cc BadBounds)))]
      [t (term (sel u (cc Mix)))]
      [u (term (refinement (sel u (cc Mix)) z))])
  (subtyping-transitive env s t u))
)

(check-true
(let ([env (term (([u (refinement Top self
                                  (: (cc Bad) Bottom (sel self (cc Bad)))
                                  (: (cc Good) (refinement Top z (: (cc L) Bottom Top)) (refinement Top z (: (cc L) Bottom Top)))
                                  (: (cc Lower) ((sel self (cc Bad)) ∧ (sel self (cc Good))) (sel self (cc Good)))
                                  (: (cc Upper) (sel self (cc Good)) ((sel self (cc Bad)) ∨ (sel self (cc Good))))
                                  (: (cc X) (sel self (cc Lower)) (sel self (cc Upper))))])
                  ()))]
      [s (term ((sel u (cc Bad)) ∧ (sel u (cc Good))))]
      [t (term (sel u (cc Lower)))]
      [u (term (refinement (sel u (cc X)) z (: (cc L) Bottom Top)))])
  (subtyping-transitive env s t u))
)

(check-true
(let ([Tc (term (refinement Top self
                            (: (cc Bad) Bottom (sel self (cc Bad)))
                            (: (cc Good) (refinement Top z (: (cc L) Bottom Top)) (refinement Top z (: (cc L) Bottom Top)))
                            (: (cc Lower) ((sel self (cc Bad)) ∧ (sel self (cc Good))) (sel self (cc Good)))
                            (: (cc Upper) (sel self (cc Good)) ((sel self (cc Bad)) ∨ (sel self (cc Good))))
                            (: (cc X) (sel self (cc Lower)) (sel self (cc Upper)))))]
      [s (term ((sel u (cc Bad)) ∧ (sel u (cc Good))))]
      [t (term (sel u (cc Lower)))]
      [u (term (refinement (sel u (cc X)) z (: (cc L) Bottom Top)))])
  (preservation (term (valnew (u (,Tc)) (cast Top
    (cast (arrow ,s ,u)
          (cast (arrow ,s ,t)
                (cast (arrow ,s ,s)
                      (fun (x ,s) ,s x)))))))))
)

(test-equal
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                              (: (cc Bar) Bottom (refinement Top self (: (cc T) Bottom Top)))
                              (: (cc Foo) Bottom (refinement (sel self (cc Bar)) z (: (cc T) Bottom (sel self (cc Foo)))))
                              (: (cm foo) Top (arrow Top (sel self (cc Foo)))))
              ((cm foo) dummy (fun (x Top) (sel u (cc Foo)) (valnew (foo ((sel u (cc Foo)))) foo)))))
              (as Top (sel u (cm foo) (as Top u))))))
'Top)

(test-equal
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                              (: (cc Bar) Bottom (refinement Top self (: (cc T) Bottom Top) (: (cm some) Top (sel self (cc T)))))
                              (: (cc Foo) Bottom (refinement (sel self (cc Bar)) z (: (cc T) (sel self (cc Foo)) Top)))
                              (: (cm foo) Top (arrow Top (sel self (cc Foo)))))
              ((cm foo) dummy (fun (x Top) (sel u (cc Foo)) (valnew (foo ((sel u (cc Foo)) ((cm some) dummy (as (sel foo (cc T)) foo)))) foo)))))
              (cast Top (sel u (cm foo) (as Top u))))))
'Top)

#;
(let ((w (term (refinement Top b
                           (: (cc T) Bottom (sel (sel b (cv x)) (cc T)))
                           (: (cv x) (sel u (cc C)))))))
  (judgment-holds
   (expansion (((u (refinement Top a
                               (: (cc C) Bottom ,w)))
                (w ,w))
               ())
              z
              (sel w (cc T))
              ((DLt ...) (Dl ...) (Dm ...)))
   ((DLt ...) (Dl ...) (Dm ...))))

(check-not-false
(typecheck (term (() ())) (term (fun (x Bottom) Top (fun (z (sel x (cc Lt))) (sel x (cc Lt)) z))))
)

(check-not-false
(let ((typeX (term (refinement Top z
                               (: (ca A) Top Top)
                               (: (cm l) Top (sel z (ca A))))))
      (typeY (term (refinement Top z
                               (: (cm l) Top Top)))))
  (type-safety
   (term
    (valnew
     (u (,typeX ((cm l) dummy (as (sel u (ca A)) u))))
     (sel (app (fun (y (arrow Top ,typeY)) ,typeY (app y (as Top u))) (as (arrow Top ,typeY) (fun (d Top) ,typeX (cast ,typeX u)))) (cm l) (as Top u))))))
)

(check-not-false
(let ((typeX (term (refinement Top z
                               (: (ca A) Top Top)
                               (: (cm l) Top (sel z (ca A))))))
      (typeY (term (refinement Top z
                               (: (cm l) Top Top)))))
  (big-step-preservation
   (term
    (valnew
     (u (,typeX ((cm l) dummy (as (sel u (ca A)) u)))) (cast Top
      (app (fun (y (arrow- f ((: (ca Y) ,typeX ,typeY)) Top (sel f (ca Y)))) 
                (arrow Top Top)
                (fun (d Top) Top (sel (cast (sel y (ca Y)) (app y (as Top u))) (cm l) (as Top u))))
           (as (arrow- f ((: (ca Y) ,typeX ,typeY)) Top (sel f (ca Y)))
               (fun- f ((: (ca Y) ,typeX ,typeX)) (d Top) (sel f (ca Y)) (as (sel f (ca Y)) u)))))))))
)

(test-predicate type-safety
 (term
  (valnew
   (b ((refinement Top z
                   (: (ca X) Top Top)
                   (: (cv l) (sel z (ca X))))
       ((cv l) b)))
   (valnew
    (a ((refinement Top z
                    (: (cv i) (refinement Top z
                                                   (: (ca X) Bottom Top)
                                                   (: (cv l) (sel z (ca X))))))
        ((cv i) b)))
    (cast Top
     (cast (sel (sel a (cv i)) (ca X))
      (sel (sel a (cv i)) (cv l))))))))

(test-predicate big-step-preservation
 (term
  (valnew
   (b ((refinement Top z
                   (: (ca X) Top Top)
                   (: (cv l) (sel z (ca X))))
       ((cv l) b)))
   (valnew
    (a ((refinement Top z
                    (: (cv i) (refinement Top z
                                                   (: (ca X) Bottom Top)
                                                   (: (cv l) (sel z (ca X))))))
        ((cv i) b)))
    (cast Top
     (app (fun (x (sel (sel a (cv i)) (ca X)))
               (arrow Top Top)
               (fun (d Top) (sel (sel a (cv i)) (ca X)) x))
          (sel (sel a (cv i)) (cv l))))))))

(test-predicate type-safety
 (term
   (valnew
    (b ((refinement Top z
                    (: (ca X) Top Top)
                    (: (cv l) (sel z (ca X))))
        ((cv l) b)))
   (valnew
    (a ((refinement Top z
                    (: (cv i) (refinement Top z
                                                   (: (ca X) Bottom Top)
                                                   (: (cv l) (sel z (ca X))))))
        ((cv i) b)))
    (cast Top
     (cast (sel (sel a (cv i)) (ca X))
      (sel (sel a (cv i)) (cv l))))))))

(test-predicate big-step-preservation
 (term
   (valnew
    (b ((refinement Top z
                    (: (ca X) Top Top)
                    (: (cv l) (sel z (ca X))))
        ((cv l) b)))
   (valnew
    (a ((refinement Top z
                    (: (cv i) (refinement Top z
                                                   (: (ca X) Bottom Top)
                                                   (: (cv l) (sel z (ca X))))))
        ((cv i) b)))
    (cast Top
     (app (fun (x (sel (sel a (cv i)) (ca X)))
               (arrow Top (sel (sel a (cv i)) (ca X)))
               (fun (d Top) (sel (sel a (cv i)) (ca X)) x))
          (sel (sel a (cv i)) (cv l))))))))

(check-true
(let* ([typeX (term (refinement Top z
                                (: (ca A) Top Top)
                                (: (ca B) Top Top)
                                (: (ca C) Bottom (sel z (ca B)))))]
       [typeY (term (refinement Top z
                                (: (ca A) Bottom Top)
                                (: (ca B) Bottom Top)
                                (: (ca C) Bottom (sel z (ca A)))))]
       [typeZ (term (refinement ,typeX z
                                (: (ca A) Bottom Bottom)
                                (: (ca B) Bottom Bottom)))])
  (subtyping-transitive (term (() ())) typeZ typeX typeY))
)

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z (: (cc L) Bottom (refinement Top z (: (ca A) Top Bottom))))))
          (app (fun (x (refinement Top z (: (cc L) Bottom (refinement Top z (: (ca A) Bottom Top)))))
                    Top
                    (valnew (z ((sel x (cc L)))) (cast Top z)))
               v))))

(test-predicate type-safety
 (term
  (valnew (v ((refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom (sel z (ca A))))))))
  (app (fun (x (refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom Top))))) Top
            (valnew (z ((refinement Top z (: (cm l)
                                             ((sel x (ca L))
                                              ∧
                                              (refinement Top z (: (ca A) Bottom (sel z (ca B))) (: (ca B) Bottom Top)))
                                             Top))
                        ((cm l) y
                                          (as Top (fun (a (sel y (ca A))) Top a)))))
                    (cast Top z)))
       (as (refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom Top)))) v)))))

(test-predicate type-safety
 (term
  (valnew (x00 ((refinement Top z (: (ca L) Bottom
                                     (refinement Top self
                                                 (: (ca A) Bottom Top)
                                                 (: (ca B) Bottom Top)
                                                 (: (cc Lc2) Bottom (sel self (ca A))))))))
  (valnew (x0 ((refinement Top z (: (cc Lc1) Bottom (refinement Top z (: (ca L) Bottom (sel x00 (ca L))))))))
  (valnew (x1 ((refinement (sel x0 (cc Lc1)) z (: (ca L) Bottom 
                                                           (refinement (sel x00 (ca L)) self 
                                                                       (: (ca A) Bottom (sel self (ca B))))))))
  (valnew (x2 ((refinement (sel x0 (cc Lc1)) z (: (ca L) Bottom 
                                                           (refinement (sel x00 (ca L)) self 
                                                                       (: (ca B) Bottom (sel self (ca A))))))))
  (app (fun (x (sel x0 (cc Lc1))) Top
            (fun (z0 ((sel x (ca L)) ∧ (sel x2 (ca L)))) Top
                 (valnew (z ((sel z0 (cc Lc2))))
                         (cast Top z))))
       (as (sel x0 (cc Lc1)) x1))))))))

(test-predicate type-safety
 (term
  (valnew (v ((refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) (sel z (ca A)) Top))))))
  (app (fun (x (refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom Top))))) Top
            (valnew (z ((refinement Top z (: (cm l)
                                             ((sel x (ca L))
                                              ∧
                                              (refinement Top z (: (ca A) (sel z (ca B)) Top) (: (ca B) Bottom Top)))
                                             Top))
                        ((cm l) y
                                          (as Top (fun (a (sel y (ca A))) Top a)))))
                    (cast Top z)))
       (as (refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom Top)))) v)))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z (: (ca L) Bottom Top) (: (cv l) (refinement Top z (: (ca L) Bottom Top))))
              ((cv l) v)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (cv l) Top)) v) (cv l))))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z (: (cm m) Top Top))
              ((cm m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (cm m) (refinement Top z (: (cm m) Top Top)) Top)) v)
            (cm m)
            v)))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z
                          (: (ca A) Top Top)
                          (: (cm m) (refinement Top z (: (ca A) Top Top)) (refinement Top z (: (ca A) Top Top))))
             ((cm m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (cm m) (refinement Top z (: (ca A) Top Top)) Top)) v)
            (cm m)
            (as (refinement Top z (: (ca A) Top Top)) v))))))

(test-predicate preservation
 (term
  (valnew (v ((refinement Top z
                          (: (ca A) Top Top)
                          (: (ca B) Bottom Top)
                          (: (cm m) (refinement Top z (: (ca A) Top Top)) (refinement Top z (: (ca A) Top Top))))
             ((cm m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (cm m) (refinement Top z (: (ca A) Top Top) (: (ca B) Bottom Top)) Top)) v)
            (cm m)
            (as (refinement Top z (: (ca A) Top Top) (: (ca B) Bottom Top)) v))))))

(test-predicate type-safety
 (term
  (valnew (v ((refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom (sel z (ca A))))))))
  (app (as (arrow (refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom (sel z (ca A)))))) Top)
           (fun (x (refinement Top z (: (ca L) Bottom (refinement Top z (: (ca A) Bottom Top) (: (ca B) Bottom Top))))) Top
                (valnew (z ((refinement Top z (: (cm l)
                                                 ((sel x (ca L))
                                                  ∧
                                                  (refinement Top z (: (ca A) Bottom (sel z (ca B))) (: (ca B) Bottom Top)))
                                                 Top))
                            ((cm l) y (as Top (fun (a (sel y (ca A))) Top a)))))
                        (cast Top z))))
       v))))

(check-not-false
(let ((Tc (term (refinement Top z
                            (: (ca A) (refinement Top z (: (cm m) Bottom Top)) Top)
                            (: (ca B) Top Top)
                            (: (cm m) (sel z (ca A)) Top))))
      (T  (term (refinement Top z
                            (: (ca A) (refinement Top z (: (cm m) Bottom Top)) Top)
                            (: (ca B) Top Top)
                            (: (cm m) (refinement (sel z (ca A)) z (: (ca B) Top Top)) Top)))))
  (preservation
   (term
    (valnew (v (,Tc ((cm m) x (as Top x))))
    (as Top
        (sel (as ,T v)
             (cm m)
             v))))))
)

(test-predicate preservation
 (term
  (valnew (a ((refinement Top z
                          (: (cc C) Bottom (refinement Top z
                                                                (: (cc D) Bottom (sel z (ca X)))
                                                                (: (ca X) Bottom Top))))))
  (valnew (b ((refinement (sel a (cc C)) z
                          (: (ca X) Bottom Bottom))))
  (valnew (c ((sel a (cc C))))
  (app (fun (x (sel a (cc C))) Top
            (valnew (d ((sel x (cc D))))
                    (app (fun (x Bottom) Bottom (sel x (cv foo)))
                         d)))
       b))))))

(check-not-false
(let ((Tc (term (refinement Top z
                            (: (ca A) (refinement Top z (: (cm m) Bottom Top)) Top)
                            (: (ca B) Top Top)
                            (: (cm m) (sel z (ca A)) Top))))
      (T  (term (refinement Top z
                            (: (ca A) (refinement Top z (: (cm m) Bottom Top)) Top)
                            (: (ca B) Top Top)
                            (: (cm m) (refinement (sel z (ca A)) z (: (ca B) Top Top)) Top)))))
  (preservation
   (term
    (valnew (v (,Tc ((cm m) x x)))
    (valnew (u ((refinement Top z (: (cv v) ,Tc))
                ((cv v) v)))
    (as Top
        (sel (as ,T (sel u (cv v)))
             (cm m)
             (app (fun (h ,T) Top (as (refinement (sel h (ca A)) z (: (ca B) Top Top)) v))
                  (sel u (cv v))))))))))
)

(test-results)