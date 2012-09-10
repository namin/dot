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
                (with-dot-writers (lambda () (render-term dot e (build-path (string-append name ".ps")))))
                #t)
            (with-dot-writers (lambda () (render-term dot e))))]))

(render-dot-term "ex_glb" #t
(val u = new ((rfn Top z
              (: (cc A) Bot (rfn Top y (: (ca T) Bot (sel z (cc A)))))
              (: (cc B) Bot (rfn Top y (: (ca T) Bot (sel z (cc B))))))) in
(cast Top
      (fun x ((sel u (cc A)) ∧ (sel u (cc B))) Top
           (fun y (sel x (ca T)) Top y))))
)