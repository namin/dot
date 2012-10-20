#lang racket
(require redex)
(require "dotf.ss")

(typecheck (term (() ())) (term
(val p = new ((rfn Top p
                   (: (cc A) Bot Top)
                   (: (cc B) Bot Top)
                   (: (cc C) Bot Top)
                   (: (cc D) Bot Top))) in
(app (fun f ((arrow (sel p (cc A)) (sel p (cc C))) ∨ (arrow (sel p (cc B)) (sel p (cc D)))) Top
          (cast ((sel p (cc C)) ∨ (sel p (cc D)))
                (app (cast (arrow ((sel p (cc A)) ∧ (sel p (cc B))) ((sel p (cc C)) ∨ (sel p (cc D)))) f)
                     (val ab = new (((sel p (cc A)) ∧ (sel p (cc B)))) in ab))))
     (fun x (sel p (cc A)) (sel p (cc C)) (val c = new ((sel p (cc C))) in c))))
))