#lang racket
(require redex)
(require "dotf.ss")
(require (only-in mzlib/struct copy-struct))
(require (only-in slideshow/pict text))
(require (only-in racket/match match))

(define (with-dot-writers thunk)
  (define (combine e a)
    ;; Buils the same element as a but with content e
    (copy-struct lw a [lw-e e]))
  (define (add a e)
    (build-lw e
              (+ (lw-line a) (lw-line-span a)) 0
              (+ (lw-column a) (lw-column-span a)) 0))
  (define (then e a)
    (build-lw e
              (lw-line a) 0
              (lw-column a) 0))
  (define (collapse-all lws)
    (collapse (first lws) (last lws)))
  (define (collapse a b)
    ;; Build a zero-width element that takes the same columns
    ;; as a through b
    (build-lw ""
              (lw-line a) (+ (- (lw-line b) (lw-line a))
                             (lw-line-span b))
              (lw-column a) (+ (- (lw-column b) (lw-column a))
                               (lw-column-span b))))
  (define (subtext txt)
    ;; Creates a text element as a subscript
    (text txt `(subscript . ,(default-style)) (default-font-size)))
  (define (pretty-binding a)
    (match (lw-e a)
      [(list oparen l v cparen)
       (combine
        (list
         (collapse oparen oparen)
         l (then "=" v) v
         (collapse cparen cparen)) a)]
      [(list oparen m x e cparen)
       (combine
        (list
         (collapse oparen oparen)
         m (then "(" x) x (then ")=" e) e
         (collapse cparen cparen)) a)]))
  (define (pretty-constructor a)
    (match (lw-e a)
      [(list oparen ty bs ... cparen)
       (combine
        (list*
         (collapse oparen oparen)
         ty (add ty "(")
         (append
          (map pretty-binding bs)
          (list (then ")" cparen) (collapse cparen cparen)))) a)]))
  (define (label-type a)
    (lw-e (cadr (lw-e a))))
  (with-atomic-rewriter 'Top "⊤"
  (with-atomic-rewriter 'Bot "⊥"
  (with-compound-rewriters
   (['val
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 0))
        (combine "val" (list-ref lws 1))
        (list-ref lws 2) ; x
        (list-ref lws 3) ; =
        (list-ref lws 4) ; new
        (pretty-constructor (list-ref lws 5)) ; c
        (combine ";" (list-ref lws 6)) ; in
        (list-ref lws 7) ; e
        (collapse (list-ref lws 8) (last lws))
       ))]
    ['sel
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 1))
        (list-ref lws 2)
        "."
        (list-ref lws 3)
        (collapse (list-ref lws 4) (last lws))))]
    ['cv
     (λ (lws)
       (list
        (combine (lw-e (list-ref lws 2)) (collapse-all lws))))]
    ['cm
     (λ (lws)
       (list
        (combine (lw-e (list-ref lws 2)) (collapse-all lws))))]
    ['ca
     (λ (lws)
       (list
        (combine (lw-e (list-ref lws 2)) (collapse-all lws))))]
    ['cc
     (λ (lws)
       (list
        (combine (lw-e (list-ref lws 2)) (collapse (first lws) (list-ref lws 2)))
        (subtext "c")
        (collapse (list-ref lws 3) (last lws))))]
    [':
     (λ (lws)
       (if (= (length lws) 5)
           (list
            (collapse (first lws) (list-ref lws 1))
            (list-ref lws 2)
            (add (list-ref lws 2) ":")
            (list-ref lws 3)
            (collapse (list-ref lws 4) (last lws)))
           (list
            (collapse (first lws) (list-ref lws 1))
            (list-ref lws 2)
            (add (list-ref lws 2) ":")
            (list-ref lws 3)
            (then (if (eq? 'cm (label-type (list-ref lws 2))) "→" "..") (list-ref lws 4))
            (list-ref lws 4)
            (collapse (list-ref lws 5) (last lws)))))]
    ['rfn
     (λ (lws)
       (define (helper lws prev)
         (if (null? (cdr lws))
             (list (combine " }" (last lws)))
             (append
              (if (null? prev) (list (car lws)) (list (add prev ",") (car lws)))
              (helper (cdr lws) (car lws)))))
       (list*
         (collapse (first lws) (list-ref lws 1))
         (list-ref lws 2)
         (add (list-ref lws 2) " { ")
         (list-ref lws 3)
         (add (list-ref lws 3) " ⇒ ")
         (helper (list-tail lws 4) null)))])
   (thunk)))))

;; we are only typesetting concrete values
(non-terminal-style (default-style))

(define-syntax (render-dot-term stx)
  (syntax-case stx ()
    [(_ name p e)
     #'(and (typecheck (term (() ())) (term e))
            (if p (preservation (term e)) (not (preservation (term e))))
            (type-safety (term e))
            (if name
                (with-dot-writers (lambda () (render-term dot e (build-path (string-append name ".pdf")))))
                #t)
            (with-dot-writers (lambda () (render-term dot e))))]))

(with-dot-writers (lambda () (render-term dot
(sel (sel (sel x (cv a)) (cv b)) (cv c))
)))

(render-dot-term "simple" #t
(val u = new ((rfn Top self (: (cv l) Top))
              [(cv l) u]) in
(sel u (cv l)))
)

(render-dot-term "simple2" #t
(val u = new ((rfn Top self  (: (cc X) Top Top) (: (cv l) Top))
              [(cv l) u]) in
(cast Top (cast (sel u (cc X)) (sel u (cv l)))))
)

(render-dot-term "foo" #f
(val v = new ((rfn Top z (: (ca L) Bot (rfn Top z (: (ca A) Bot Top) (: (ca B) Bot (sel z (ca A))))))) in
(app (cast (arrow (rfn Top z (: (ca L) Bot (rfn Top z (: (ca A) Bot Top) (: (ca B) Bot (sel z (ca A)))))) Top)
           (fun (x (rfn Top z (: (ca L) Bot (rfn Top z (: (ca A) Bot Top) (: (ca B) Bot Top))))) Top
                (val z = new ((rfn Top z (: (cm l) ((sel x (ca L)) ∧ (rfn Top z (: (ca A) Bot (sel z (ca B))) (: (ca B) Bot Top))) Top))
                              ((cm l) y (as Top (fun (a (sel y (ca A))) Top a)))) in
                (cast Top z))))
     v))
)
