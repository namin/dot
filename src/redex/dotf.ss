#lang racket
(require redex)
(require rackunit)

(define-language dot
  ((x y z) variable-not-otherwise-mentioned)
  (l (label-value variable-not-otherwise-mentioned))
  (m (label-method variable-not-otherwise-mentioned))
  (i natural)
  (loc (location i))
  (v loc)
  (vx v x)
  (e vx (valnew (x c) e) (sel e l) (sel e m e))
  (p x loc (sel p l))
  (c (Tc (l vx) ... (m x e) ...))
  (Gamma ([x T] ...))
  (store (c ...))
  (env (Gamma store))
  (Lt Lc La)
  (Lc (label-class variable-not-otherwise-mentioned))
  (La (label-abstract-type variable-not-otherwise-mentioned))
  ((S T U V W) (sel p Lt) (refinement T z DLt ... Dl ... Dm ...) (intersection T T) (union T T) Top Bottom)
  ((Sc Tc) (sel p Lc) (refinement Tc z DLt ... Dl ... Dm ...) (intersection Tc Tc) Top)
  (DLt (: Lt S U))
  (Dl (: l T))
  (Dm (: m S U))
  (D DLt Dl Dm)
  (ec hole (sel ec l) (sel ec m e) (sel v m ec))
  (bool #t #f)
  (DLm DLt Dm)
  (Lm Lt m)
  (Lany Lt l m))

(check-true (redex-match? dot e (term (valnew (u (Top)) u))))
(check-true (redex-match? dot e (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l))))))

(define-metafunction dot
  subst : any x any -> any
  ;; 1. x_1 bound
  [(subst (m_1 x_1 any_1) x_1 any_2)
   (m_1 x_1 any_1)]
  [(subst (valnew (x_1 c_1) any_1) x_1 any_2)
   (valnew (x_1 c_1) any_1)]
  [(subst (refinement T_1 x_1 D_1 ...) x_1 any_2)
   (refinement (subst T_1 x_1 any_2) x_1 D_1 ...)]
  
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst (m_1 x_1 any_1) x_2 any_2)
   (m_1 x_3
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
  [(subst (label-method variable_1) x_1 any_1) (label-method variable_1)]
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
  [(subst-var (label-method variable_1) x_1 x_2) (label-method variable_1)]
  [(subst-var (label-class variable_1) x_1 x_2) (label-class variable_1)]
  [(subst-var (label-abstract-type variable_1) x_1 x_2) (label-abstract-type variable_1)]

  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

(check-true (redex-match? dot
 (valnew (x_1 ((refinement Top self (: (label-method f) Top Top)) [(label-method f) x_2 x_2])) x_1)
 (term (subst (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method f) x x])) u) x y))))
(check-true (redex-match? dot
 (valnew (x_1 ((refinement Top self (: (label-method f) Top Top)) [(label-method f) (side-condition x_2 (not (equal? 'y (term x_2)))) y])) x_1)
 (term (subst (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method f) y x])) u) x y))))
(check-true (redex-match? dot
 (valnew (x_1 ((refinement Top self (: (label-method f) Top Top)) [(label-method f) (side-condition x_2 (not (equal? 'y (term x_2)))) y])) x_1)
 (term (subst (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method f) z x])) u) x y))))
(check-true (redex-match? dot
 (valnew (x_1 (Top)) y)
 (term (subst (valnew (u (Top)) x) x y))))
(check-true (redex-match? dot
 (valnew ((side-condition x_1 (not (equal? 'u (term x_1)))) (Top)) u)
 (term (subst (valnew (u (Top)) x) x u))))
(check-true (redex-match? dot
 (valnew (x_1 ((refinement Top self (: (label-method mt) Top Top)) [(label-method mt) x_2 x_1])) (sel x_1 (label-method mt) x_1))
 (term (subst (valnew (u ((refinement Top self (: (label-method mt) Top Top)) [(label-method mt) y u])) (sel u (label-method mt) u)) mt x))))

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
  value-label-lookup : c l -> vx or #f
  [(value-label-lookup (Tc (l_req vx_req) (l_after vx_after) ... (m_ignore x_ignore e_ignore) ...) l_req) vx_req]
  [(value-label-lookup (Tc (l_first vx_first) (l_after vx_after) ... (m_ignore x_ignore e_ignore) ...) l_req)
   (value-label-lookup (Tc (l_after vx_after) ...) l_req)]
  [(value-label-lookup (Tc (m_ignore x_ignore e_ignore) ...) l_req) #f])

(define-metafunction dot
  method-label-lookup : c m -> (x e) or #f
  [(method-label-lookup (Tc (l_ignore vx_ignore) ... (m_req x_req e_req) (m_after x_after e_after) ...) m_req) (x_req e_req)]
  [(method-label-lookup (Tc (l_ignore vx_ignore) ... (m_first x_first e_first) (m_after x_after e_after) ...) m_req)
   (method-label-lookup (Tc (m_after x_after e_after) ...) m_req)]
  [(method-label-lookup (Tc (l_ignore vx_ignore) ...) m_req) #f])

(define-judgment-form dot
  #:mode (found I O)
  #:contract (found any bool)
  [(found #f #f)]
  [(found (side-condition any (term any)) #t)])

(define-judgment-form dot
  #:mode (red I I O O)
  #:contract (red store e e store)
  [(red store (in-hole ec (sel (location i) m v)) (in-hole ec (subst e x v)) store) ;; (Sel/βv)
   (where c (store-lookup store i))
   (found c #t)
   (where any_lookup (method-label-lookup c m))
   (found any_lookup #t)
   (where (x e) any_lookup)]
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

;(trace-dot (term (valnew (u ((refinement Top self (: (label-value l) Top)) [(label-value l) u])) (sel u (label-value l)))))

(define-metafunction dot
  ev : store e -> (v store)
  [(ev store v) (v store)]
  [(ev store_i (sel e_i1 m_i e_i2)) (v_f store_f)
   (where ((location i_1) store_1) (ev store_i e_i1))
   (where c_1 (store-lookup store_1 i_1))
   (judgment-holds (found c_1 #t))
   (where any_lookup (method-label-lookup c_1 m_i))
   (judgment-holds (found any_lookup #t))
   (where (x e_11) any_lookup)
   (where (v_2 store_2) (ev store_1 e_i2))
   (where (v_f store_f) (ev store_2 (subst e_11 x v_2)))]
  [(ev store_i (valnew (x_i c_i) e_i)) (v_f store_f)
   (where loc_new (store-fresh-location store_i))
   (where e_s (subst e_i x_i loc_new))
   (where store_s (store-extend store_i (subst c_i x_i loc_new)))
   (where (v_f store_f) (ev store_s e_s))]
  [(ev store_i (sel e_i l_i)) (v_f store_f)
   (where ((location i_f) store_f) (ev store_i e_i))
   (where c_f (store-lookup store_f i_f))
   (judgment-holds (found c_f #t))
   (where v_f (value-label-lookup c_f l_i))
   (judgment-holds (found v_f #t))])

;(term (ev () (valnew (u (Top)) u)))
;(term (ev () (valnew (u ((refinement Top self (: (label-method f) Top Top)) [(label-method l) x x])) (sel u (label-method l) u))))
;(term (ev () (valnew (u ((refinement Top self (: (label-method l) Top Top)) [(label-method l) x u])) (sel u (label-method l) u))))

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
  [(fn (m_1 x_1 any_1) x_1) #f]
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
  [(wf-decl env (: Lm S U))
   (wf-type env S)
   (wf-type env U)])

(define-metafunction dot
  is_wfe-type : (T ...) env T -> bool
  [(is_wfe-type (T_p ...) env T) #t
   (side-condition (term (is_wf-type (T_p ...) env T)))
   (judgment-holds (expansion env z T ((DLt ...) (Dl ...) (Dm ...))))]
  [(is_wfe-type (T_p ...) env T) #f])

(define-metafunction dot
  is_wf-type : (T ...) env T -> bool
  [(is_wf-type (T_p ...) env Top) #t]
  [(is_wf-type (T_p ...) env (-> T_1 T_2)) #t
   (side-condition (term (is_wf-type (T_p ...) env T_1)))
   (side-condition (term (is_wf-type (T_p ...) env T_2)))]
  [(is_wf-type (T_p ...) (Gamma store) (refinement T z D ...)) #t
   (side-condition (term (is_wf-type (T_p ...) (Gamma store) T)))
   (where env_extended ((gamma-extend Gamma z (refinement T z D ...)) store))
   (side-condition (andmap (lambda (d) (judgment-holds (wf-decl env_extended ,d))) (term (D ...))))]
  [(is_wf-type (T_p ...) env (sel p Lt)) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S U) any_bound)
   (judgment-holds (subtype env S Bottom))]
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
  #:mode (wfe-type I I)
  #:contract (wfe-type env T)
  [(wfe-type env T) (found (is_wfe-type () env T) #t)])

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
  sorted-method-assigns : ((m x e) ...) -> ((m x e) ...)
  [(sorted-method-assigns ((m_1 x_1 e_1) ...)) ,(sort-assigns (term ((m_1 x_1 e_1) ...)))])

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
  [(decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(cons (term (: Lm (union S_1 S_2) (intersection U_1 U_2)))
          (term (decl-intersection (DLm_1 ...) (DLm_2 ...))))]
  [(decl-intersection ((: Lm S_1 U_1) DLm_1 ...) (DLm_before ... (: Lm S_2 U_2) DLm_2 ...))
   ,(append (term (DLm_before ...))
            (term (decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))))]
  [(decl-intersection (DLm_before ... (: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(append (term (DLm_before ...))
            (term (decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))))]
  [(decl-intersection (Dl_1 ...) (Dl_2 ...))
   (Dl_1 ... Dl_2 ...)]
  [(decl-intersection (DLm_1 ...) (DLm_2 ...))
   (DLm_1 ... DLm_2 ...)])

(define-metafunction dot
  decl-union : (D ...) (D ...) -> (D ...)
  [(decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(cons (term (: l (union T_1 T_2)))
          (term (decl-union (Dl_1 ...) (Dl_2 ...))))]
  [(decl-union ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(cons (term (: Lm (intersection S_1 S_2) (union U_1 U_2)))
          (term (decl-union (DLm_1 ...) (DLm_2 ...))))]
  [(decl-union ((: Lm S_1 U_1) DLm_1 ...) (DLm_before ... (: Lm S_2 U_2) DLm_2 ...))
   (decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))]
  [(decl-union (DLm_before ... (: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   (decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))]
  [(decl-union (Dl_1 ...) (Dl_2 ...))
   ()]
  [(decl-union (DLm_1 ...) (DLm_2 ...))
   ()])

(define-metafunction dot
  membership-type-lookup : env e Lt -> (S U) or #f
  [(membership-type-lookup env_1 p_1 Lt_1)
   (subst (S_1 U_1) z_1 p_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((D_before ... (: Lt_1 S_1 U_1) D_after ...) (Dl ...) (Dm ...))))]
  [(membership-type-lookup env_1 e_1 Lt_1)
   (S_1 U_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((D_before ... (: Lt_1 S_1 U_1) D_after ...) (Dl ...) (Dm ...))))
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
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (D_before ... (: l_1 T_1) D_after ...) (Dm ...))))]
  [(membership-value-lookup env_1 e_1 l_1)
   T_1
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (D_before ... (: l_1 T_1) D_after ...) (Dm ...))))
   (judgment-holds (found (fn T_1 z_1) #f))]
  [(membership-value-lookup env_1 e_1 l_1)
   Bottom
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bottom))]
  [(membership-value-lookup env_1 e_1 l_1)
   #f])

(define-metafunction dot
  membership-method-lookup : env e m -> (S U) or #f
  [(membership-method-lookup env_1 p_1 m_1)
   (subst (S_1 U_1) z_1 p_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 p_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (Dl ...) (D_before ... (: m_1 S_1 U_1) D_after ...))))]
  [(membership-method-lookup env_1 e_1 m_1)
   (S_1 U_1)
   (where z_1 ,(variable-not-in (term (env_1 e_1 T_e)) 'z))
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (expansion env_1 z_1 T_e ((DLt ...) (Dl ...) (D_before ... (: m_1 S_1 U_1) D_after ...))))
   (judgment-holds (found (fn (S_1 U_1) z_1) #f))]
  [(membership-method-lookup env_1 e_1 m_1)
   (Top Bottom)
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bottom))]
  [(membership-method-lookup env_1 e_1 m_1)
   #f])

(define max-iter 100)

(define-judgment-form dot
  #:mode (expansion-iter I I I I O)
  #:contract (expansion-iter (T ...) env z T ((DLt ...) (Dl ...) (Dm ...)))
  [(expansion-iter (T_p ...) env z Top (() () ()))]
  [(expansion-iter (T_p ...) env z (-> S T) (() () ()))]
  [(expansion-iter (T_p ...) env z_1 (refinement T_1 z_2 DLt_1 ... Dl_1 ... Dm_1 ...)
                   ((decl-intersection (sorted-decls (subst (DLt_1 ...) z_2 z_1)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dl_1 ...) z_2 z_1)) (sorted-decls (Dl_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dm_1  ...) z_2 z_1)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (T_p ... (refinement T_1 z_2 DLt_1 ... Dl_1 ... Dm_1 ...)) env z_1 T_1 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (T_p ...) env z (intersection T_1 T_2)
                   ((decl-intersection (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...)))
                    (decl-intersection (sorted-decls (Dm_1  ...)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (T_p ... (intersection T_1 T_2)) env z T_1 ((DLt_1 ...) (Dl_1 ...) (Dm_1 ...)))
   (expansion-iter (T_p ... (intersection T_1 T_2)) env z T_2 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (T_p ...) env z (union T_1 T_2)
                   ((decl-union (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-union (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...)))
                    (decl-union (sorted-decls (Dm_1  ...)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (T_p ... (union T_1 T_2)) env z T_1 ((DLt_1 ...) (Dl_1 ...) (Dm_1 ...)))
   (expansion-iter (T_p ... (union T_1 T_2)) env z T_2 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (T_p ...) env z (sel p Lt) ((DLt_u ...) (Dl_u ...) (Dm_u ...)))
   (where any_bound (membership-type-lookup env p Lt))
   (found any_bound #t)
   (where (S_p (side-condition U_p (and (not (member (term U_p) (term (T_p ... (sel p Lt)))))
                                        (< (length (term (T_p ...))) max-iter))))
          any_bound)
   (expansion-iter (T_p ... (sel p Lt)) env z U_p ((DLt_u ...) (Dl_u ...) (Dm_u ...)))]
  [(expansion-iter (T_p ...) env z Bottom (((: (label-abstract-type kludge) Top Bottom)) () ()))]) ;; kludge

(define-judgment-form dot
  #:mode (expansion I I I O)
  #:contract (expansion env z T ((DLt ...) (Dl ...) (Dm ...)))
  [(expansion env z T ((DLt ...) (Dl ...) (Dm ...)))
   (expansion-iter () env z T ((DLt ...) (Dl ...) (Dm ...)))])

(define-judgment-form dot
  #:mode (subdecl I I I)
  #:contract (subdecl env D D)
  [(subdecl env (: Lm_1 S_1 T_1) (: Lm_1 S_2 T_2))
   (subtype env S_2 S_1)
   (subtype env T_1 T_2)]
  [(subdecl env (: l_1 T_1) (: l_1 T_2))
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
  [(is_subtype ((T_a T_b) ...) env T T) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env T Top) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env Bottom T) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env S (refinement T z DLt ... Dl ... Dm ...)) #t
   (judgment-holds (wfe-type env (refinement T z DLt ... Dl ... Dm ...)))
   (side-condition (term (is_subtype ((T_a T_b) ... (S (refinement T z DLt ... Dl ... Dm ...))) env S T)))
   (judgment-holds (expansion env z S ((DLt_s ...) (Dl_s ...) (Dm_s ...))))
   (where (Gamma store) env)
   (where Gamma_z (gamma-extend Gamma z S))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (DLt_s ...)) (sorted-decls (DLt ...))))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (Dl_s ...)) (sorted-decls (Dl ...))))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (Dm_s ...)) (sorted-decls (Dm ...))))]
  [(is_subtype ((T_a T_b) ...) env (refinement T_1 z DLt ... Dl ... Dm ...) T_2) #t
   (judgment-holds (wfe-type env (refinement T_1 z DLt ... Dl ... Dm ...)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((refinement T_1 z DLt ... Dl ... Dm ...) T_2)) env T_1 T_2)))]
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
   (judgment-holds (wfe-type env T_2))
   (side-condition (term (is_subtype ((T_a T_b) ... ((intersection T_1 T_2) T_o)) env T_1 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (intersection T_1 T_2) T_o) #t
   (judgment-holds (wfe-type env T_1))
   (side-condition (term (is_subtype ((T_a T_b) ... ((intersection T_1 T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (union T_1 T_2) T_o) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((union T_1 T_2) T_o)) env T_1 T_o)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((union T_1 T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env T_o (union T_1 T_2)) #t
   (judgment-holds (wfe-type env T_2))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (union T_1 T_2))) env T_o T_1)))]
  [(is_subtype ((T_a T_b) ...) env T_o (union T_1 T_2)) #t
   (judgment-holds (wfe-type env T_1))
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
  [(typeof (Gamma store) (valnew (x (Tc (l vx) ... (m x_m e_m) ...)) e) T)
   (wfe-type (Gamma store) Tc)
   (expansion (Gamma store) x Tc (((: Lt S U) ...) (Dl ...) (Dm ...)))
   (where ((l_s vx_s) ...) (sorted-assigns ((l vx) ...)))
   (where ((: l_s V_d) ...) (sorted-decls (Dl ...)))
   (where ((m_s y_ms e_ms) ...) (sorted-method-assigns ((m x_m e_m) ...)))
   (where ((: m_s V_md W_md) ...) (sorted-decls (Dm ...)))
   (where Gamma_Tc (gamma-extend Gamma x Tc))
   (wfe-type (Gamma_Tc store) V_md) ...
   (subtype (Gamma_Tc store) S U) ...
   (typeof (Gamma_Tc store) vx_s V_s) ...
   (subtype (Gamma_Tc store) V_s V_d) ...
   (typeof ((gamma-extend Gamma_Tc y_ms V_md) store) e_ms W_ms) ...
   (subtype ((gamma-extend Gamma_Tc y_ms V_md) store) W_ms W_md) ...
   (typeof (Gamma_Tc store) e T)
   (found (fn T x) #f)]
  [(typeof (Gamma store) (location i) Tc)
   (where c (store-lookup store i))
   (found c #t)
   (where Tc (constructor-type-lookup c))]
  [(typeof env (sel e_1 l_1) T_1)
   (where T_1 (membership-value-lookup env e_1 l_1))
   (found T_1 #t)]
  [(typeof env (sel e_1 m_1 e_2) T_1)
   (where any_lookup (membership-method-lookup env e_1 m_1))
   (found any_lookup #t)
   (where (S_1 T_1) any_lookup)
   (typeof env e_2 T_2)
   (subtype env T_2 S_1)])

(define (typecheck env e)
  (match (judgment-holds (typeof ,env ,e T) T)
    [(list) #f]
    [(list T) T]
    [_ (error 'typecheck
              "multiple typing derivations for term ~a in environment ~a"
              e env)]))

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

(define-metafunction dot
  arrow- : x (DLt ...) S T -> W
  [(arrow- x (DLt ...) S T) (refinement Top x
                              DLt ...
                              (: (label-method apply) S T))])

(define-metafunction dot
  fun- : x (DLt ...) (x S) T e -> e
  [(fun- x_f (DLt ...) (x S) T e) (valnew
                         (x_f ((arrow- x_f (DLt ...) S T)
                               [(label-method apply) x e]))
                         x_f)])

(define-metafunction dot
  arrow : S T -> W
  [(arrow S T) (arrow- x_self () S T)
   (where x_self ,(variable-not-in (term (S T)) 'self))])

(define-metafunction dot
  fun : (x S) T e -> e
  [(fun (x S) T e) (fun- x_f () (x S) T e)
   (where x_f ,(variable-not-in (term (x S T e)) 'f))])

(define-metafunction dot
  app : e e -> e
  [(app e_1 e_2) (sel e_1 (label-method apply) e_2)])

(define-metafunction dot
  cast : T e -> e
  [(cast T e) (app (fun (x T) T x) e)
   (where x ,(variable-not-in (term (T e)) 'id))])

(define-metafunction dot
  as : T e -> e
  [(as T e) (cast T e)])

(test-equal (typecheck (term (() ())) (term (fun (x Top) Top x)))
            (term (refinement Top f (: (label-method apply) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (d (Top)) (fun (x Top) Top x))))
            (term (refinement Top f (: (label-method apply) Top Top))))
(test-equal (typecheck (term (() ())) (term (valnew (d (Top)) (app (fun (x Top) Top x) d))))
            'Top)

(define (dotExample)
  (term (valnew (dummy (Top)) (valnew (root ((refinement
                        Top rootThis
                        (: (label-class UnitClass) Bottom Top)
                        (: (label-class BooleanClass) Bottom (refinement
                                                              Top this
                                                              (: (label-method ifNat) Top
                                                                 (arrow (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass)))
                                                                        (arrow (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass)))
                                                                               (sel rootThis (label-class NatClass)))))))
                        (: (label-class NatClass) Bottom (refinement
                                                          Top this
                                                          (: (label-method isZero) Top
                                                             (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class BooleanClass))))
                                                          (: (label-method pred) Top
                                                             (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass))))
                                                          (: (label-method succ) Top
                                                             (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass))))))
                        (: (label-method unit) Top (arrow Top (sel rootThis (label-class UnitClass))))
                        (: (label-method false) Top (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class BooleanClass))))
                        (: (label-method true) Top (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class BooleanClass))))
                        (: (label-method zero) Top (arrow (sel rootThis (label-class UnitClass)) (sel rootThis (label-class NatClass))))
                        (: (label-method successor) Top (arrow (sel rootThis (label-class NatClass)) (sel rootThis (label-class NatClass)))))
                       [(label-method unit) dummy (fun (x Top) (sel root (label-class UnitClass)) (valnew (u ((refinement (sel root (label-class UnitClass)) this))) u))]
                       [(label-method false) dummy
                        (fun (u (sel root (label-class UnitClass))) (sel root (label-class BooleanClass))
                          (valnew (ff ((refinement (sel root (label-class BooleanClass)) this)
                                       [(label-method ifNat) dummy
                                                            (fun (t (arrow (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                                 (arrow (arrow (sel root (label-class UnitClass)) (sel root (label-class NatClass))) (sel root (label-class NatClass)))
                                                              (fun (e (arrow (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                                   (sel root (label-class NatClass))
                                                                (app e (app (sel root (label-method unit) dummy) (sel root (label-method unit) dummy)))))]))
                                  ff))]
                       [(label-method true) dummy
                        (fun (u (sel root (label-class UnitClass))) (sel root (label-class BooleanClass))
                          (valnew (tt ((refinement (sel root (label-class BooleanClass)) this)
                                       [(label-method ifNat) dummy
                                                            (fun (t (arrow (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                                 (arrow (arrow (sel root (label-class UnitClass)) (sel root (label-class NatClass))) (sel root (label-class NatClass)))
                                                              (fun (e (arrow (sel root (label-class UnitClass)) (sel root (label-class NatClass))))
                                                                   (sel root (label-class NatClass))
                                                                (app t (app (sel root (label-method unit) dummy) (sel root (label-method unit) dummy)))))]))
                                  tt))]
                       [(label-method zero) dummy
                        (fun (u (sel root (label-class UnitClass))) (sel root (label-class NatClass))
                          (valnew (zz ((refinement (sel root (label-class NatClass)) this)
                                       [(label-method isZero) dummy (fun (u (sel root (label-class UnitClass))) (sel root (label-class BooleanClass))
                                                                              (app (sel root (label-method true) dummy) (app (sel root (label-method unit) dummy) (sel root (label-method unit) dummy))))]
                                       [(label-method succ) dummy (fun (u (sel root (label-class UnitClass))) (sel root (label-class NatClass))
                                                                            (app (sel root (label-method successor) dummy) zz))]
                                       [(label-method pred) dummy (fun (u (sel root (label-class UnitClass))) (sel root (label-class NatClass)) zz)]))
                                  zz))]
                       [(label-method successor) dummy
                        (fun (n (sel root (label-class NatClass))) (sel root (label-class NatClass))
                          (valnew (ss ((refinement (sel root (label-class NatClass)) this)
                                       [(label-method isZero) dummy (fun (u (sel root (label-class UnitClass))) (sel root (label-class BooleanClass)) 
                                                                              (app (sel root (label-method false) dummy) (app (sel root (label-method unit) dummy) (sel root (label-method unit) dummy))))]
                                       [(label-method succ) dummy (fun (u (sel root (label-class UnitClass))) (sel root (label-class NatClass))
                                                                            (app (sel root (label-method successor) dummy) ss))]
                                       [(label-method pred) dummy (fun (u (sel root (label-class UnitClass))) (sel root (label-class NatClass)) n)]))
                                  ss))]))
                (app (fun (x Top) Top x)
                 (app (fun (unit (sel root (label-class UnitClass))) (sel root (label-class BooleanClass))
                    (app (sel (app (sel (app (sel (app (sel root (label-method zero) dummy) unit)
                                                  (label-method succ) dummy) unit)
                                        (label-method pred) dummy) unit)
                              (label-method isZero) dummy) unit)
                    ) (app (sel root (label-method unit) dummy) (sel root (label-method unit) dummy))))))))

;(typecheck (term (() ())) (dotExample))

(define-metafunction dot
  wf-prog : any -> bool
  [(wf-prog (refinement T z DLt ... Dl ... Dm ...)) #f
   (side-condition (not (equal? (term (DLt ... Dl ... Dm ...)) (remove-duplicates (term (DLt ... Dl ... Dm ...)) #:key cadadr))))]
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
        ;(printf "preservation: trying ~a\n" e)
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

(define (big-step-preservation e)
  (if (and (well-formed? e) (typecheck (term (() ())) e))
      (begin
        ;(printf "big-step preservation: trying ~a\n" e)
        (redex-let dot ([(e_ev store_ev) (term (ev () ,e))])
          (let ([t_e  (typecheck (term (() ())) e)]
                [t_ev (typecheck (term (() store_ev)) (term e_ev))])
            (and t_ev
                 (judgment-holds (subtype (() store_ev) ,t_ev ,t_e))
                 (term e_ev)))))
      #t))

(define (type-safety e)
  (if (and (well-formed? e) (typecheck (term (() ())) e))
      (begin
        ;(printf "type-safety: trying ~a\n" e)
        (let loop ((e e) (store (term ())))
          (if (value? e) e
              (match (steps-to store e)
                [(list store_to e_to)
                 (loop e_to store_to)]
                [_ (error 'type-safety "expect match")]))))
      #t))

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

(define (subtyping-transitive env s t u)
  (if (and (judgment-holds (wfe-type ,env ,s)) (judgment-holds (wfe-type ,env ,t)) (judgment-holds (wfe-type ,env ,u))
           (judgment-holds (subtype ,env ,s ,t)) (judgment-holds (subtype ,env ,t ,u)))
      (begin
        ;(printf "trying ~a ~a ~a ~a\n" env s t u)
        (judgment-holds (subtype ,env ,s ,u)))
      #t))

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

(check-not-false
(type-safety
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
)

(check-not-false
(big-step-preservation
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
)

(check-not-false
(type-safety
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
)

(check-not-false
(big-step-preservation
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
)

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

(check-not-false
(preservation
 (term
  (valnew (v ((refinement Top z (: (label-class L) Bottom (refinement Top z (: (label-abstract-type A) Top Bottom))))))
          (app (fun (x (refinement Top z (: (label-class L) Bottom (refinement Top z (: (label-abstract-type A) Bottom Top)))))
                    Top
                    (valnew (z ((sel x (label-class L)))) (cast Top z)))
               v))))
)

(check-not-false
(type-safety
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
)

(check-not-false
(type-safety
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
)

(check-not-false
(type-safety
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
)

(check-not-false
(preservation
 (term
  (valnew (v ((refinement Top z (: (label-abstract-type L) Bottom Top) (: (label-value l) (refinement Top z (: (label-abstract-type L) Bottom Top))))
              ((label-value l) v)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-value l) Top)) v) (label-value l))))))
)

(check-not-false
(preservation
 (term
  (valnew (v ((refinement Top z (: (label-method m) Top Top))
              ((label-method m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-method m) (refinement Top z (: (label-method m) Top Top)) Top)) v)
            (label-method m)
            v)))))
)

(check-not-false
(preservation
 (term
  (valnew (v ((refinement Top z
                          (: (label-abstract-type A) Top Top)
                          (: (label-method m) (refinement Top z (: (label-abstract-type A) Top Top)) (refinement Top z (: (label-abstract-type A) Top Top))))
             ((label-method m) x x)))
  (app (fun (x Top) Top x)
       (sel (as (refinement Top z (: (label-method m) (refinement Top z (: (label-abstract-type A) Top Top)) Top)) v)
            (label-method m)
            (as (refinement Top z (: (label-abstract-type A) Top Top)) v))))))
)

(check-not-false
(preservation
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
)

(check-not-false
(type-safety
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
)

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

(check-not-false
(preservation
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
)

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