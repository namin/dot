#lang racket
(require redex)
(require "dotf.ss")
(require (only-in mzlib/struct copy-struct))
(require (only-in slideshow/pict text))

(define (with-dot-writers thunk)
  (define (combine e a)
    ;; Buils the same element as a but with content e
    (copy-struct lw a [lw-e e]))
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
    (text txt `(subscript.,(default-style)) (default-font-size)))
  (with-atomic-rewriter 'Top "⊤"
  (with-atomic-rewriter 'Bottom "⊥"
  (with-compound-rewriters
   (['val
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 0))
        (combine "val" (list-ref lws 1))
        (list-ref lws 2) ; x
        (list-ref lws 3) ; =
        (list-ref lws 4) ; new
        (list-ref lws 5) ; c
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
    ['label-value
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 1))
        (list-ref lws 2)
        (collapse (list-ref lws 3) (last lws))))]
    ['label-method
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 1))
        (list-ref lws 2)
        (collapse (list-ref lws 3) (last lws))))]
    ['label-abstract-type
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 1))
        (list-ref lws 2)
        (subtext "a")
        (collapse (list-ref lws 3) (last lws))))]
    ['label-class
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 1))
        (list-ref lws 2)
        (subtext "c")
        (collapse (list-ref lws 3) (last lws))))]
    [':
     (λ (lws)
       (list
        (collapse (first lws) (list-ref lws 1))
        (list-ref lws 2)
        ":"
        (list-ref lws 3)
        (collapse (list-ref lws 4) (last lws))))]
    ['refinement
     (λ (lws)
       (define (helper lws first?)
         (if (null? (cdr lws))
             (list (combine " }" (last lws)))
             (append
              (if first? (list (car lws)) (list "," (car lws)))
              (helper (cdr lws) #f))))
       (list*
         (collapse (first lws) (list-ref lws 1))
         (list-ref lws 2)
         " { "
         (list-ref lws 3)
         " ⇒ "
         (helper (list-tail lws 4) #t)))])
   (thunk)))))

(with-dot-writers (lambda () (render-term dot
(val u = new ((refinement Top self (: (label-value l) Top))
              [(label-value l) u]) in
(sel u (label-value l)))
)))