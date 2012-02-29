#lang racket
(require redex)

(define-language dot
  ((x y z) variable-not-otherwise-mentioned)
  (l (label-value variable-not-otherwise-mentioned))
  (i natural)
  (loc (location i))
  (v loc (λ (x T) e))
  (vx v x)
  (e vx (e e) (valnew (x c) e) (sel e l))
  (p x loc (sel p l))
  (c (Tc (l vx) ...))
  (Gamma ([x T] ...))
  (store (c ...))
  (env (Gamma store))
  (Lt Lc La)
  (Lc (label-class variable-not-otherwise-mentioned))
  (La (label-abstract-type variable-not-otherwise-mentioned))
  ((S T U V) (sel p Lt) (refinement T z DLt ... Dl ...) (-> T T) (intersection T T) (union T T) Top Bottom)
  ((Sc Tc) (sel p Lc) (refinement Tc z DLt ... Dl ...) (intersection Tc Tc) Top)
  (DLt (: Lt S U))
  (Dl (: l T))
  (D DLt Dl)
  (ec hole (ec e) (v ec) (sel ec l))
  (bool #t #f)
  (quality complete loose)
  (Lany Lt l))

(define-extended-language mini-dot dot
  ((S T U V) (-> T T) Top)
  ((Sc Tc) (refinement Tc z Dl ...) Top))

(redex-match dot e (term (λ (x Top) x)))
(redex-match dot e (term (valnew (u (Top)) u)))
(redex-match dot e (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define-metafunction dot
  subst : any x any -> any
  ;; 1. x_1 bound
  [(subst (λ (x_1 T_1) any_1) x_1 any_2)
   (λ (x_1 (subst T_1 x_1 any_2)) any_1)]
  [(subst (valnew (x_1 c_1) any_1) x_1 any_2)
   (valnew (x_1 c_1) any_1)]
  [(subst (refinement T_1 x_1 D_1 ...) x_1 any_2)
   (refinement (subst T_1 x_1 any_2) x_1 D_1 ...)]
  
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst (λ (x_1 T_1) any_1) x_2 any_2)
   (λ (x_3 (subst T_1 x_2 any_2))
     (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (valnew (x_1 c_1) any_1) x_2 any_2)
   (valnew (x_3 (subst (subst-var c_1 x_1 x_3) x_2 any_2))
           (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 c_1 any_1 any_2))
                                (term x_1)))]
  [(subst (refinement T_1 x_1 D_1 ...) x_2 any_2)
   (refinement (subst T_1 x_2 any_2) x_3 (subst (subst-var D_1 x_1 x_3) x_2 any_2) ...)
   (where x_3 ,(variable-not-in (term (D_1 ... x_2 any_2))
                                (term x_1)))]

  ;; do not treat labels as variables
  [(subst (label-value variable_1) x_1 any_1) (label-value variable_1)]
  [(subst (label-class variable_1) x_1 any_1) (label-class variable_1)]
  [(subst (label-abstract-type variable_1) x_1 any_1) (label-abstract-type variable_1)]

  ;; 3. replace x_1 with any_1
  [(subst x_1 x_1 any_1) any_1]
  
  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2])

(define-metafunction dot
  subst-var : any x x -> any
  [(subst-var (label-value variable_1) x_1 x_2) (label-value variable_1)]
  [(subst-var (label-class variable_1) x_1 x_2) (label-class variable_1)]
  [(subst-var (label-abstract-type variable_1) x_1 x_2) (label-abstract-type variable_1)]

  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

(term (subst (λ (x Top) x) x y))
(term (subst (λ (y Top) x) x y))
(term (subst (λ (z Top) (z x)) x y))
(term (subst (valnew (u (Top)) x) x y))
(term (subst (valnew (u (Top)) x) x u))
(term (subst (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l))) l x))

(define-metafunction dot
  store-extend : store c -> store
  [(store-extend (c_before ...) c_new)
   (c_before ... c_new)])

(define-metafunction dot
  store-lookup : store i -> c or #f
  [(store-lookup (c ...) i)
   ,(if (< (term i) (length (term (c ...))))
        (list-ref (term (c ...)) (term i))
        #f)])

(define-metafunction dot
  store-fresh-location : store -> loc
  [(store-fresh-location (c ...))
   (location ,(length (term (c ...))))])

(define-metafunction dot
  value-label-lookup : c l -> v or #f
  [(value-label-lookup (Tc (l_req v_req) (l_after v_after) ...) l_req) v_req]
  [(value-label-lookup (Tc (l_first v_first) (l_after v_after) ...) l_req) (value-label-lookup (Tc (l_after v_after) ...) l_req)]
  [(value-label-lookup (Tc) l_req) #f])

(define-judgment-form dot
  #:mode (found I O)
  #:contract (found any bool)
  [(found #f #f)]
  [(found (side-condition any (term any)) #t)])

(define-judgment-form dot
  #:mode (red I I O O)
  #:contract (red store e e store)
  [(red store (in-hole ec ((λ (x T) e) v)) (in-hole ec (subst e x v)) store)] ;; (βv)
  [(red store (in-hole ec (valnew (x c) e)) (in-hole ec (subst e x loc_new)) (store-extend store (subst c x loc_new)))
   (where loc_new (store-fresh-location store))] ;; (New)
  [(red store (in-hole ec (sel (location i) l)) (in-hole ec v) store) ;; (Sel)
   (where c (store-lookup store i))
   (found c #t)
   (where v (value-label-lookup c l))
   (found v #t)])

(define red-rr
  (reduction-relation
   dot
   (--> (store_1 e_1) (store_2 e_2)
        (judgment-holds (red store_1 e_1 e_2 store_2)))))

(define (trace-dot expr)
  (traces red-rr (term (() ,expr))))

;(trace-dot (term ((λ (x Top) x) (λ (x Top) x))))
;(trace-dot (term (valnew (u (Top)) u)))
;(trace-dot (term (valnew (u (Top)) ((λ (x Top) x) (λ (x Top) x)))))
;(trace-dot (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define value? (redex-match dot v))
(define (single-step? e)
  (= (length (apply-reduction-relation red-rr (term (() ,e))))
     1))
(define (steps-to store e)
  (match (apply-reduction-relation red-rr (term (,store ,e)))
    [(list) #f]
    [(list any) any]
    [_ (error 'steps-to
              "multiple derivations for term ~a"
              e)]))

(define-metafunction dot
  fn : any x -> bool
  ;; x_1 bound
  [(fn (λ (x_1 T_1) any_1) x_1) (fn T_1 x_1)]
  [(fn (valnew (x_1 c_1) any_1) x_1) #f]
  [(fn (refinement T_1 x_1 D_1 ...) x_1) (fn T_1 x_1)]

  ;; x_1 free
  [(fn x_1 x_1) #t]

  ;; do not treat labels as variables
  [(fn Lany x) #f]

  ;; the last two cases just recur on the tree structure of the term
  [(fn (any_1 ...) x_1)
   ,(ormap (lambda (x) x) (term ((fn any_1 x_1) ...)))]
  [(fn any_1 x_1) #f])

(define-metafunction dot
  gamma-extend : Gamma x T -> Gamma
  [(gamma-extend ((x_before T_before) ...) x_new T_new)
   ((x_before T_before) ... (x_new T_new))])

(define-metafunction dot
  gamma-lookup : Gamma x -> T or #f
  [(gamma-lookup ((x_before T_before) ... (x_req T_req)) x_req) T_req]
  [(gamma-lookup ((x_before T_before) ... (x_last T_last)) x_req) (gamma-lookup ((x_before T_before) ...) x_req)]
  [(gamma-lookup () x_req) #f])

(define-metafunction dot
  constructor-type-lookup : c -> Tc
  [(constructor-type-lookup (Tc any ...)) Tc])

(define-judgment-form dot
  #:mode (wf-decl I I)
  #:contract (wf-decl env D)
  [(wf-decl env (: l T))
   (wf-type env T)]
  [(wf-decl env (: Lt S U))
   (wf-type env S)
   (wf-type env U)])

(define-metafunction dot
  is_wf-type : (T ...) env T -> bool
  [(is_wf-type (T_p ...) env Top) #t]
  [(is_wf-type (T_p ...) env (-> T_1 T_2)) #t
   (side-condition (term (is_wf-type (T_p ...) env T_1)))
   (side-condition (term (is_wf-type (T_p ...) env T_2)))]
  [(is_wf-type (T_p ...) (Gamma store) (refinement Tc z D ...)) #t
   (where env_extended ((gamma-extend Gamma z (refinement Tc z D ...)) store))
   (side-condition (andmap (lambda (d) (judgment-holds (wf-decl env_extended ,d))) (term (D ...))))]
  [(is_wf-type (T_p ...) env (sel p Lt)) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (Bottom U) any_bound)]
  [(is_wf-type (T_p ...) env (sel p Lt)) #t
   (side-condition (not (member (term (sel p Lt)) (term (T_p ...)))))
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S U) any_bound)
   (side-condition (term (is_wf-type ((sel p Lt) T_p ...) env S)))
   (side-condition (term (is_wf-type ((sel p Lt) T_p ...) env U)))]
  [(is_wf-type (T_p ...) env (intersection T_1 T_2)) #t
   (side-condition (term (is_wf-type (T_p ...) env T_1)))
   (side-condition (term (is_wf-type (T_p ...) env T_2)))]
  [(is_wf-type (T_p ...) env (union T_1 T_2)) #t
   (side-condition (term (is_wf-type (T_p ...) env T_1)))
   (side-condition (term (is_wf-type (T_p ...) env T_2)))]
  [(is_wf-type (T_p ...) env Bottom) #t]
  [(is_wf-type (T_p ...) env T) #f])

(define-judgment-form dot
  #:mode (wf-type I I)
  #:contract (wf-type env T)
  [(wf-type env T) (found (is_wf-type () env T) #t)])
 
(define (sort-decls ds)
  (sort ds #:key (lambda (x) (symbol->string (cadr (cadr x)))) string<?))
(define-metafunction dot
  sorted-decls : (D ...) -> (D ...)
  [(sorted-decls (D_1 ...)) ,(sort-decls (term (D_1 ...)))])
  
(define (sort-assigns as)
  (sort as #:key (lambda (x) (symbol->string (cadr (car x)))) string<?))
(define-metafunction dot
  sorted-assigns : ((l vx) ...) -> ((l vx) ...)
  [(sorted-assigns ((l_1 vx_1) ...)) ,(sort-assigns (term ((l_1 vx_1) ...)))])

(define-metafunction dot
  decl-intersection : (D ...) (D ...) -> (D ...)
  [(decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(cons (term (: l (intersection T_1 T_2)))
          (term (decl-intersection (Dl_1 ...) (Dl_2 ...))))]
  [(decl-intersection ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   ,(append (term (Dl_before ...))
            (term (decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))))]
  [(decl-intersection (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(append (term (Dl_before ...))
            (term (decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))))]
  [(decl-intersection ((: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))
   ,(cons (term (: Lt (union S_1 S_2) (intersection U_1 U_2)))
          (term (decl-intersection (DLt_1 ...) (DLt_2 ...))))]
  [(decl-intersection ((: Lt S_1 U_1) DLt_1 ...) (DLt_before ... (: Lt S_2 U_2) DLt_2 ...))
   ,(append (term (DLt_before ...))
            (term (decl-intersection ((: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))))]
  [(decl-intersection (DLt_before ... (: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))
   ,(append (term (DLt_before ...))
            (term (decl-intersection ((: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))))]
  [(decl-intersection (Dl_1 ...) (Dl_2 ...))
   (Dl_1 ... Dl_2 ...)]
  [(decl-intersection (DLt_1 ...) (DLt_2 ...))
   (DLt_1 ... DLt_2 ...)])

(define-metafunction dot
  decl-union : (D ...) (D ...) -> (D ...)
  [(decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(cons (term (: l (union T_1 T_2)))
          (term (decl-union (Dl_1 ...) (Dl_2 ...))))]
  [(decl-union ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union ((: Lt S_1 U_1) DLt_1 ...) ((: Lt S_1 U_1) DLt_2 ...))
   ,(cons (term (: Lt (intersection S_1 S_2) (union U_1 U_2)))
          (term (decl-union (DLt_1 ...) (DLt_2 ...))))]
  [(decl-union ((: Lt S_1 U_1) DLt_1 ...) (DLt_before ... (: Lt S_2 U_2) DLt_2 ...))
   (decl-union ((: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))]
  [(decl-union (DLt_before ... (: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))
   (decl-union ((: Lt S_1 U_1) DLt_1 ...) ((: Lt S_2 U_2) DLt_2 ...))]
  [(decl-union (Dl_1 ...) (Dl_2 ...))
   ()]
  [(decl-union (DLt_1 ...) (DLt_2 ...))
   ()])

(define-metafunction dot
  membership-type-lookup : env e Lt -> (S U) or #f
  [(membership-type-lookup env_1 p_1 Lt_1)
   (subst (S_1 U_1) z_1 p_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((D_before ... (: Lt_1 S_1 U_1) D_after ...) (Dl ...)) complete))]
  [(membership-type-lookup env_1 e_1 Lt_1)
   (S_1 U_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((D_before ... (: Lt_1 S_1 U_1) D_after ...) (Dl ...)) complete))
   (judgment-holds (found (fn (S_1 U_1) z_1) #f))]
  [(membership-type-lookup env_1 e_1 Lt_1)
   (Top Bottom)
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bottom))]  
  [(membership-type-lookup env_1 e_1 Lt_1)
   #f])

(define-metafunction dot
  membership-value-lookup : env e l -> T or #f
  [(membership-value-lookup env_1 p_1 l_1)
   (subst T_1 z_1 p_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (D_before ... (: l_1 T_1) D_after ...)) complete))]
  [(membership-value-lookup env_1 e_1 l_1)
   T_1
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (D_before ... (: l_1 T_1) D_after ...)) complete))
   (judgment-holds (found (fn T_1 z_1) #f))]
  [(membership-value-lookup env_1 e_1 l_1)
   Bottom
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bottom))]
  [(membership-value-lookup env_1 e_1 l_1)
   #f])

(define-metafunction dot
  q&q : quality quality -> quality
  [(q&q loose loose) loose]
  [(q&q loose complete) loose]
  [(q&q complete loose) loose]
  [(q&q complete complete) complete])
  
(define-judgment-form dot
  #:mode (expansion-iter I I I I O O)
  #:contract (expansion-iter (T ...) env z T ((DLt ...) (Dl ...)) quality)
  [(expansion-iter (T_before ... T_x T_after ...) env z T_x (() ()) loose)]
  [(expansion-iter (T_p ...) env z Top (() ()) complete)]
  [(expansion-iter (T_p ...) env z (-> S T) (() ()) complete)]
  [(expansion-iter (T_p ...) env z_1 (refinement T_1 z_2 DLt_1 ... Dl_1 ...)
                   ((decl-intersection (sorted-decls (subst (DLt_1 ...) z_2 z_1)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dl_1  ...) z_2 z_1)) (sorted-decls (Dl_2  ...))))
                   quality_2)
   (expansion-iter (T_p ... (refinement T_1 z_2 DLt_1 ... Dl_1 ...)) env z_1 T_1 ((DLt_2 ...) (Dl_2 ...)) quality_2)]
  [(expansion-iter (T_p ...) env z (intersection T_1 T_2)
                   ((decl-intersection (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...))))
                   (q&q quality_1 quality_2))
   (expansion-iter (T_p ... (intersection T_1 T_2)) env z T_1 ((DLt_1 ...) (Dl_1 ...)) quality_1)
   (expansion-iter (T_p ... (intersection T_1 T_2)) env z T_2 ((DLt_2 ...) (Dl_2 ...)) quality_2)]
  [(expansion-iter (T_p ...) env z (union T_1 T_2)
                   ((decl-union (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-union (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...))))
                   (q&q quality_1 quality_2))
   (expansion-iter (T_p ... (union T_1 T_2)) env z T_1 ((DLt_1 ...) (Dl_1 ...)) quality_1)
   (expansion-iter (T_p ... (union T_1 T_2)) env z T_2 ((DLt_2 ...) (Dl_2 ...)) quality_2)]
  [(expansion-iter (T_p ...) env z (sel p Lt) ((DLt_u ...) (Dl_u ...)) quality_u)
   (where any_bound (membership-type-lookup env p Lt))
   (found any_bound #t)
   (where (S_p (side-condition U_p (not (member (term (sel p Lt)) (term (T_p ...)))))) any_bound)
   (expansion-iter (T_p ... (sel p Lt)) env z U_p ((DLt_u ...) (Dl_u ...)) quality_u)])

(define-judgment-form dot
  #:mode (expansion I I I O O)
  #:contract (expansion env z T ((DLt ...) (Dl ...)) quality)
  [(expansion env z T ((DLt ...) (Dl ...)) quality)
   (expansion-iter () env z T ((DLt ...) (Dl ...)) quality)])

(define-judgment-form dot
  #:mode (subdecl I I I)
  #:contract (subdecl env D D)
  [(subdecl env (: l_1 T_1) (: l_1 T_2))
   (subtype env T_1 T_2)]
  [(subdecl env (: Lt_1 S_1 T_1) (: Lt_1 S_2 T_2))
   (subtype env S_2 S_1)
   (subtype env T_1 T_2)])

(define-judgment-form dot
  #:mode (subdecls I I I)
  #:contract (subdecls env (D ...) (D ...))
  [(subdecls env (D ...) ())]
  [(subdecls env (D_1 D_rest1 ...) (D_2 D_rest2 ...))
   (subdecl env D_1 D_2)
   (subdecls env (D_rest1 ...) (D_rest2 ...))]
  [(subdecls env (D_1 D_rest1 ...) (D_2 D_rest2 ...))
   (subdecls env (D_rest1 ...) (D_2 D_rest2 ...))])

(define-metafunction dot
  is_subtype : ((T T) ...) env S T -> bool
  [(is_subtype ((T_a T_b) ...) env S T) #f
   (side-condition (member (term (S T)) (term ((T_a T_b) ...))))]
  [(is_subtype ((T_a T_b) ...) env T T) #t]
  [(is_subtype ((T_a T_b) ...) env T Top) #t]
  [(is_subtype ((T_a T_b) ...) env Bottom T) #t]
  [(is_subtype ((T_a T_b) ...) env (-> S_1 S_2) (-> T_1 T_2)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((-> S_1 S_2) (-> T_1 T_2))) env T_1 S_1)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((-> S_1 S_2) (-> T_1 T_2))) env S_2 T_2)))]
  [(is_subtype ((T_a T_b) ...) env S (refinement T z)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (S (refinement T z))) env S T)))]
  [(is_subtype ((T_a T_b) ...) env S (refinement T z DLt ... Dl ...)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (S (refinement T z DLt ... Dl ...))) env S T)))
   (judgment-holds (expansion env z S ((DLt_s ...) (Dl_s ...)) quality_s))
   (judgment-holds (subdecls env (sorted-decls (Dl_s ...)) (sorted-decls (Dl ...))))
   (judgment-holds (subdecls env (sorted-decls (DLt_s ...)) (sorted-decls (DLt ...))))]
  [(is_subtype ((T_a T_b) ...) env (refinement T_1 z DLt ... Dl ...) T_2) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((refinement T_1 z DLt ... Dl ...) T_2)) env T_1 T_2)))]
  [(is_subtype ((T_a T_b) ...) env S_1 (sel p Lt)) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S_p U_p) any_bound)
   (side-condition (term (is_subtype ((T_a T_b) ... (S_1 (sel p Lt))) env S_p U_p)))
   (side-condition (term (is_subtype ((T_a T_b) ... (S_1 (sel p Lt))) env S_1 S_p)))]
  [(is_subtype ((T_a T_b) ...) env (sel p Lt) U_1) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S_p U_p) any_bound)
   (side-condition (term (is_subtype ((T_a T_b) ... ((sel p Lt) U_1)) env S_p U_p)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((sel p Lt) U_1)) env U_p U_1)))]
  [(is_subtype ((T_a T_b) ...) env T_o (intersection T_1 T_2)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (intersection T_1 T_2))) env T_o T_1)))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (intersection T_1 T_2))) env T_o T_2)))]
  [(is_subtype ((T_a T_b) ...) env (intersection T_1 T_2) T_o) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((intersection T_1 T_2) T_o)) env T_1 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (intersection T_1 T_2) T_o) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((intersection T_1 T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (union T_1 T_2) T_o) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((union T_1 T_2) T_o)) env T_1 T_o)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((union T_1 T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env T_o (union T_1 T_2)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (union T_1 T_2))) env T_o T_1)))]
  [(is_subtype ((T_a T_b) ...) env T_o (union T_1 T_2)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (union T_1 T_2))) env T_o T_2)))]  
  [(is_subtype ((T_a T_b) ...) env S T) #f])

(define-judgment-form dot
  #:mode (subtype I I I)
  #:contract (subtype env S T)
  [(subtype env S T) (found (is_subtype () env S T) #t)])

(define-judgment-form dot
  #:mode (typeof I I O)
  #:contract (typeof env e T)
  [(typeof (Gamma store) x T)
   (where T (gamma-lookup Gamma x))
   (found T #t)]
  [(typeof (Gamma store) (valnew (x (Tc (l vx) ...)) e) T)
   (wf-type (Gamma store) Tc)
   (expansion (Gamma store) x Tc (((: Lt S U) ...) (Dl ...)) complete)
   (where ((l_s vx_s) ...) (sorted-assigns ((l vx) ...)))
   (where ((: l_s V_d) ...) (sorted-decls (Dl ...)))
   (subtype ((gamma-extend Gamma x Tc) store) S U) ...
   (typeof ((gamma-extend Gamma x Tc) store) vx_s V_s) ...
   (subtype ((gamma-extend Gamma x Tc) store) V_s V_d) ...
   (typeof ((gamma-extend Gamma x Tc) store) e T)
   (found (fn T x) #f)]
  [(typeof (Gamma store) (location i) Tc)
   (where c (store-lookup store i))
   (found c #t)
   (where Tc (constructor-type-lookup c))]
  [(typeof (Gamma store) (λ (x S) e) (-> S T))
   (wf-type (Gamma store) S)
   (typeof ((gamma-extend Gamma x S) store) e T)
   (found (fn T x) #f)]
  [(typeof env (e_1 e_2) T)
   (typeof env e_1 (-> S T))
   (typeof env e_2 T_2)
   (subtype env T_2 S)]
  [(typeof env (sel e_1 l_1) T_1)
   (where T_1 (membership-value-lookup env e_1 l_1))
   (found T_1 #t)])

(define (typecheck env e)
  (match (judgment-holds (typeof ,env ,e T) T)
    [(list) #f]
    [(list T) T]
    [_ (error 'typecheck
              "multiple typing derivations for term ~a in environment ~a"
              e env)]))

(typecheck (term (() ())) (term (valnew (u (Top)) u)))
(typecheck (term (() ())) (term (valnew (o (Top)) (valnew (o (Top)) o))))
(typecheck (term (() ())) (term (λ (x Top) x)))
(typecheck (term (() ())) (term ((λ (x Top) x) (λ (x Top) x))))
(typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))
(typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) u)))
(typecheck (term (() ())) (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) ((λ (x (sel u (label-class l))) u) u))))
(typecheck (term (() ())) (term (valnew (u ((refinement Top self (: (label-class l) Top Top)))) ((λ (x (sel u (label-class l))) u) u))))
(typecheck (term (() ())) (term (valnew (u ((refinement Top self (: (label-abstract-type l) Top Top)))) ((λ (x (sel u (label-abstract-type l))) u) u))))

(define dotExample
  (term (valnew (root ((refinement
                        Top rootThis
                        (: (label-class UnitClass) Bottom Top)
                        (: (label-class BooleanClass) Bottom (refinement
                                                              Top this
                                                              (: (label-value ifNat)
                                                                 (-> (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass)))
                                                                     (-> (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass)))
                                                                         (sel rootThis (label-class NatClass)))))))
                        (: (label-class NatClass) Bottom (refinement
                                                          Top this
                                                          (: (label-value isZero)
                                                             (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class BooleanClass))))
                                                          (: (label-value pred)
                                                             (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass))))
                                                          (: (label-value succ)
                                                             (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass))))))
                        (: (label-value unit) (-> Top (sel rootThis (label-class UnitClass))))
                        (: (label-value false) (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class BooleanClass))))
                        (: (label-value true) (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class BooleanClass))))
                        (: (label-value zero) (-> (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass))))
                        (: (label-value successor) (-> (sel rootThis (label-class NatClass)) (sel rootThis (label-class NatClass)))))
                       [(label-value unit) (λ (x Top) (valnew (u ((refinement (sel root (label-class UnitClass)) this))) u))]
                       [(label-value false)
                        (λ (u (sel root (label-class UnitClass)))
                          (valnew (ff ((refinement (sel root (label-class BooleanClass)) this)
                                       [(label-value ifNat) (λ (t (-> (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                              (λ (e (-> (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                                (e ((sel root (label-value unit)) (sel root (label-value unit))))))]))
                                  ff))]
                       [(label-value true)
                        (λ (u (sel root (label-class UnitClass)))
                          (valnew (tt ((refinement (sel root (label-class BooleanClass)) this)
                                       [(label-value ifNat) (λ (t (-> (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                              (λ (e (-> (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                                (t ((sel root (label-value unit)) (sel root (label-value unit))))))]))
                                  tt))]
                       [(label-value zero)
                        (λ (u (sel root (label-class UnitClass)))
                          (valnew (zz ((refinement (sel root (label-class NatClass)) this)
                                       [(label-value isZero) (λ (u (sel root (label-class UnitClass))) ((sel root (label-value true)) ((sel root (label-value unit)) (sel root (label-value unit))))
                       )]
                                       [(label-value succ) (λ (u (sel root (label-class UnitClass))) ((sel root (label-value successor)) zz))]
                                       [(label-value pred) (λ (u (sel root (label-class UnitClass))) zz)]))
                                  zz))]
                       [(label-value successor)
                        (λ (n (sel root (label-class NatClass)))
                          (valnew (ss ((refinement (sel root (label-class NatClass)) this)
                                       [(label-value isZero) (λ (u (sel root (label-class UnitClass))) ((sel root (label-value false)) ((sel root (label-value unit)) (sel root (label-value unit))))
                       )]
                                       [(label-value succ) (λ (u (sel root (label-class UnitClass))) ((sel root (label-value successor)) ss))]
                                       [(label-value pred) (λ (u (sel root (label-class UnitClass))) n)]))
                                  ss))]))
                ((λ (x Top) x)
                 ((λ (unit (sel root (label-class UnitClass)))
                    ((sel ((sel ((sel ((sel root (label-value zero)) unit) (label-value succ)) unit) (label-value pred)) unit) (label-value isZero)) unit)
                    ) ((sel root (label-value unit)) (sel root (label-value unit))))))))

(typecheck (term (() ())) dotExample)


(define-metafunction dot
  wf-prog : any -> bool
  [(wf-prog (refinement T z DLt ... Dl ...)) #f
   (side-condition (not (equal? (term (DLt ... Dl ...)) (remove-duplicates (term (DLt ... Dl ...)) #:key cadadr))))]
  [(wf-prog (any_1 ...))
   ,(andmap (lambda (x) x) (term ((wf-prog any_1) ...)))]
  [(wf-prog any_1) #t]) 

(define-metafunction dot
  lc-decls : any -> (variable ...)
  [(lc-decls (: (label-class variable_1) S_1 U_1))
   (variable_1)]
  [(lc-decls (any_1 ...))
   ,(apply append (term ((lc-decls any_1) ...)))]
  [(lc-decls any_1)
   ()])

(define (well-formed? e)
  (and (term (wf-prog ,e))
       (let ((cs (term (lc-decls ,e))))
         (equal? cs (remove-duplicates cs)))))

(define (progress e)
  (if (and (well-formed? e) (typecheck (term (() ())) e))
      (begin
        (printf "progress: trying ~a\n" e)
        (or (value? e)
            (single-step? e)))
      #t))

(define (preservation e)
  (if (and (well-formed? e) (typecheck (term (() ())) e) (single-step? e))
      (begin
        (printf "preservation: trying ~a\n" e)
        (let loop ((e e) (store (term ())) (t (typecheck (term (() ())) e)))
          (or (and (value? e) t)
              (match (steps-to store e)
                [(list store_to e_to)
                 (let ((t_new (typecheck (term (() ,store_to)) e_to)))
                   (and t_new
                        (judgment-holds (subtype (() ,store_to) ,t_new ,t))
                        (loop e_to store_to t_new)))]
                [_ (error 'preservation "expect match")]))))
      #t))

(preservation (term (valnew (u (Top)) u)))
(preservation (term ((λ (x Top) x) (λ (x Top) x))))
(preservation (term (valnew (u ((refinement Top u (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))
(preservation (term (valnew (u ((refinement Top u (: (label-class l) Top Top)))) ((λ (x (sel u (label-class l))) u) u))))
(preservation dotExample)

(define-metafunction dot
  vars : any -> (x ...)
  [(vars (label-value variable_1)) ()]
  [(vars (label-class variable_1)) ()]
  [(vars (label-abstract-type variable_1)) ()]
  [(vars x_1) (x_1)]
  [(vars (any_1 ...)) ,(apply append (term ((vars any_1) ...)))]
  [(vars any_1) ()])

(define (close e)
  (let loop ((e e) (vs (term (vars ,e))))
    (if (null? vs)
        e
        (loop (term (subst ,e ,(car vs) (λ (x Top) x))) (cdr vs)))))

(define (pick-random lst def)
  (if (null? lst)
      def
      (list-ref lst (random (length lst)))))

(define-metafunction dot
  massage-mini : (x ...) (l ...) any -> any
  [(massage-mini (x_b ...) (l_b ...) (valnew (x_1 (Tc_1 (l_1 vx_1) ...)) e_1))
   (valnew (x_1 (Tc_1 (l_e ,(pick-random (term (x_b ... x_1)) (term (λ (x Top) x)))) ...)) (massage-mini (x_b ... x_1) (l_b ... l_e ...) e_1))
   (judgment-holds (expansion (() ()) x_1 Tc_1 (() ((: l_e T_le) ...)) complete))]
  [(massage-mini (x_b ...) (l_b ...) (λ (x_1 T_1) e_2))
   (λ (x_1 T_1) (massage-mini (x_b ... x_1) (l_b ...) e_2))]
  [(massage-mini (x_b ...) (l_b ...) (sel e_1 l_1)) (sel (massage-mini (x_b ...) (l_b ...) e_1) ,(pick-random (term (l_b ...)) (term l_1)))]
  [(massage-mini (x_b ...) (l_b ...) x_1)
   ,(let ((res (pick-random (term (x_b ... )) (term (λ (x Top) x)))))
      (if (or (null? (term (l_b ...))) (= 0 (random 1)))
          res
          (term (sel ,res ,(pick-random (term (l_b ...)) #f)))))]
  [(massage-mini (x_b ...) (l_b ...) (refinement Tc_1 z_1 D_1 ...)) (refinement Tc_1 z_1 D_1 ...)]
  [(massage-mini (x_b ...) (l_b ...) (any_1 ...)) ((massage-mini (x_b ...) (l_b ...) any_1) ...)]
  [(massage-mini (x_b ...) (l_b ...) any_1) any_1])

(define (prepare-mini e)
  (term (massage-mini () () ,e)))

;(redex-check dot e (progress (term e)))
;(redex-check dot e (preservation (term e)))

;(redex-check mini-dot e (progress (term e)) #:prepare close)
;(redex-check mini-dot e (preservation (term e)) #:prepare close)

#;
(let ([R (reduction-relation mini-dot
  [--> (valnew (x ((refinement Top z (: l_1 Top) Dl ...) (l vx) ...)) e) (valnew (x ((refinement Top z (: l_1 Top) Dl ...) (l vx) ...)) e)])])
  (redex-check mini-dot e (progress (term e)) #:source R #:prepare prepare-mini)
  (redex-check mini-dot e (preservation (term e)) #:source R #:prepare prepare-mini))

(define-metafunction dot
  path-var : p -> x
  [(path-var x) x]
  [(path-var loc) 'x]
  [(path-var (sel p l)) (path-var p)])

(define-metafunction dot
  massage : (x ...) (l ...) (Lc ...) (Lt ...) any -> any
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (valnew (x_1 (T_1 (l_1 vx_1) ...)) e_1))
   (valnew (x_1 (T_1 (l_e ,(pick-random (term (x_b ... x_1)) (term (λ (x Top) x)))) ...))
           (massage (x_b ... x_1) (l_b ... l_e ...) ,(append (term (Lc_b ...)) (filter (lambda (l) (redex-match dot Lc l)) (term (Lt_e ...)))) (Lt_b ... Lt_e ...) e_1))
   (judgment-holds (expansion (() ()) x_1 T_1 (((: Lt_e S_lte U_lte) ...) ((: l_e T_le) ...)) complete))]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (λ (x_1 T_1) e_2))
   (λ (x_1 T_1) (massage (x_b ... x_1) (l_b ...) (Lc_b ...) (Lt_b ...) e_2))]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (sel e_1 l_1))
   (sel (massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) e_1) ,(pick-random (term (l_b ...)) (term l_1)))]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (sel p_1 Lc_1))
   (sel (massage ((path-var p_1) x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) p_1) ,(pick-random (term (Lc_b ...)) (term Lc_1)))]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (sel p_1 Lt_1))
   (sel (massage ((path-var p_1) x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) p_1) ,(pick-random (term (Lt_b ...)) (term Lt_1)))]  
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) x_1)
   ,(let ((res (pick-random (term (x_b ... )) (term (λ (x Top) x)))))
      (if (or (null? (term (l_b ...))) (= 0 (random 1)))
          res
          (term (sel ,res ,(pick-random (term (l_b ...)) #f)))))]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (refinement T_1 z_1 D_1 ...)) (refinement T_1 z_1 D_1 ...)]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) (any_1 ...)) ((massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) any_1) ...)]
  [(massage (x_b ...) (l_b ...) (Lc_b ...) (Lt_b ...) any_1) any_1])

(define (prepare e)
  ;(printf "preparing ~a\n" e)
  (term (massage () () () () ,e)))

#;
(let ([R (reduction-relation dot
  [--> (valnew (x ((refinement Top z DLt ... Dl ...) (l vx) ...)) e) (valnew (x ((refinement Top z DLt ... Dl ...) (l vx) ...)) e)])])
  (redex-check dot e (progress (term e)) #:source R #:prepare prepare)
  (redex-check dot e (preservation (term e)) #:source R #:prepare prepare))

(define (subtyping-transitive env s t u)
  (if (and (judgment-holds (wf-type ,env ,s)) (judgment-holds (wf-type ,env ,t)) (judgment-holds (wf-type ,env ,u))
           (judgment-holds (subtype ,env ,s ,t)) (judgment-holds (subtype ,env ,t ,u)))
      (begin
        (printf "trying ~a ~a ~a ~a\n" env s t u)
        (judgment-holds (subtype ,env ,s ,u)))
      #t))

#;
(redex-check dot (S T U) (subtyping-transitive (term (() ())) (term S) (term T) (term U)))

#;
(redex-check dot (env S T U) (subtyping-transitive (term env) (term S) (term T) (term U)))

;; (subtyping-transitive (term (([x (refinement Top self (: (label-class L) Bottom (sel self (label-class L))))]) ())) (term (sel x (label-class L))) (term Top) (term (refinement Top z)))
;; (preservation (term (valnew (u ((refinement Top self (: (label-class L) Bottom (sel self (label-class L)))))) (λ (x Top) x))))
#;
(typecheck (term (() ())) (term (valnew (u ((refinement Top self (: (label-class L) Bottom (sel self (label-class L)))))) ((λ (x Top) x)
((λ (a (-> (sel u (label-class L)) (refinement Top z))) a)
 ((λ (b (-> (sel u (label-class L)) Top)) b)
  (λ (c (sel u (label-class L))) c)))
))))
#;
(preservation (term (valnew (u ((refinement Top self (: (label-class L) Bottom (sel self (label-class L)))))) ((λ (x Top) x)
((λ (a (-> (sel u (label-class L)) (refinement Top z))) a)
 ((λ (b (-> (sel u (label-class L)) Top)) b)
  (λ (c (sel u (label-class L))) c)))
))))
#;
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                                                        (: (label-abstract-type L1) Bottom (sel self (label-abstract-type L1)))
                                                        (: (label-abstract-type L2) Bottom (refinement Top z (: (label-abstract-type L3) Bottom Top)))
                                                        (: (label-abstract-type L4) (intersection (sel self (label-abstract-type L2)) (sel self (label-abstract-type L1))) (sel self (label-abstract-type L2))))))
                                        ((λ (x Top) x)
((λ (a (-> (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))) (refinement Top z (: (label-abstract-type L3) Bottom Top)))) a)
 ((λ (b (-> (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))) (sel u (label-abstract-type L4)))) b)
  (λ (c (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1)))) c)))
))))
#;
(preservation (term (valnew (u ((refinement Top self 
                                                        (: (label-abstract-type L1) Bottom (sel self (label-abstract-type L1)))
                                                        (: (label-abstract-type L2) Bottom (refinement Top z (: (label-abstract-type L3) Bottom Top)))
                                                        (: (label-abstract-type L4) (intersection (sel self (label-abstract-type L2)) (sel self (label-abstract-type L1))) (sel self (label-abstract-type L2))))))
                                        ((λ (x Top) x)
((λ (a (-> (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))) (refinement Top z (: (label-abstract-type L3) Bottom Top)))) a)
 ((λ (b (-> (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1))) (sel u (label-abstract-type L4)))) b)
  (λ (c (intersection (sel u (label-abstract-type L2)) (sel u (label-abstract-type L1)))) c)))
))))
#;
(let ([env (term (([u (refinement Top self 
                                  (: (label-class Bad) Bottom (sel self (label-class Bad))) 
                                  (: (label-class BadBounds) Top (sel self (label-class Bad))) 
                                  (: (label-class Mix) (sel self (label-class BadBounds)) Top))])
                  ()))]
      [s (term (sel u (label-class BadBounds)))]
      [t (term (sel u (label-class Mix)))]
      [u (term (refinement (sel u (label-class Mix)) z))])
  (subtyping-transitive env s t u))
#;
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
#;
(let ([Tc (term (refinement Top self
                            (: (label-class Bad) Bottom (sel self (label-class Bad)))
                            (: (label-class Good) (refinement Top z (: (label-class L) Bottom Top)) (refinement Top z (: (label-class L) Bottom Top)))
                            (: (label-class Lower) (intersection (sel self (label-class Bad)) (sel self (label-class Good))) (sel self (label-class Good)))
                            (: (label-class Upper) (sel self (label-class Good)) (union (sel self (label-class Bad)) (sel self (label-class Good))))
                            (: (label-class X) (sel self (label-class Lower)) (sel self (label-class Upper)))))]
      [s (term (intersection (sel u (label-class Bad)) (sel u (label-class Good))))]
      [t (term (sel u (label-class Lower)))]
      [u (term (refinement (sel u (label-class X)) z (: (label-class L) Bottom Top)))])
  (preservation (term (valnew (u (,Tc)) ((λ (x Top) x)
    ((λ (f (-> ,s ,u)) f)
     ((λ (f (-> ,s ,t)) f)
      ((λ (f (-> ,s ,s)) f) 
       (λ (x ,s) x)))))))))
#;
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                              (: (label-class Bar) Bottom (refinement Top self (: (label-class T) Bottom Top)))
                              (: (label-class Foo) Bottom (refinement (sel self (label-class Bar)) z (: (label-class T) Bottom (sel self (label-class Foo)))))
                              (: (label-value foo) (-> Top (sel self (label-class Foo)))))
              ((label-value foo) (λ (x Top) (valnew (foo ((sel u (label-class Foo)))) foo)))))
              ((λ (x Top) x)
               (sel u (label-value foo))))))
#;
(typecheck (term (() ())) (term (valnew (u ((refinement Top self 
                              (: (label-class Bar) Bottom (refinement Top self (: (label-class T) Bottom Top) (: (label-value some) (sel self (label-class T)))))
                              (: (label-class Foo) Bottom (refinement (sel self (label-class Bar)) z (: (label-class T) (sel self (label-class Foo)) Top)))
                              (: (label-value foo) (-> Top (sel self (label-class Foo)))))
              ((label-value foo) (λ (x Top) (valnew (foo ((sel u (label-class Foo)) ((label-value some) foo))) foo)))))
              ((λ (x Top) x)
               (sel u (label-value foo))))))
