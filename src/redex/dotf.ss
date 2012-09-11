#lang racket
(require redex)
(provide (all-defined-out))

(define-language dot
  ((x y z) variable-not-otherwise-mentioned)
  (l (cv variable-not-otherwise-mentioned))
  (m (cm variable-not-otherwise-mentioned))
  (i natural)
  (loc (location i))
  (v loc)
  (vx v x)
  (e vx (val x = new c in e) (sel e l) (sel e m e))
  (p x loc (sel p l))
  (c (Tc (l vx) ... (m x e) ...))
  (Gamma ([x T] ...))
  (store (c ...))
  (env (Gamma store))
  (Lt Lc La)
  (Lc (cc variable-not-otherwise-mentioned))
  (La (ca variable-not-otherwise-mentioned))
  ((S T U V W) (sel p Lt) (rfn T z DLt ... Dl ... Dm ...) (T ∧ T) (T ∨ T) Top Bot)
  ((Sc Tc) (sel p Lc) (rfn Tc z DLt ... Dl ... Dm ...) (Tc ∧ Tc) Top)
  (DLt (: Lt S U))
  (Dl (: l T))
  (Dm (: m S U))
  (D DLt Dl Dm)
  (ec hole (sel ec l) (sel ec m e) (sel v m ec))
  (bool #t #f)
  (DLm DLt Dm)
  (Lm Lt m)
  (Lany Lt l m))

(define-metafunction dot
  subst : any x any -> any
  ;; 1. x_1 bound
  [(subst (m_1 x_1 any_1) x_1 any_2)
   (m_1 x_1 any_1)]
  [(subst (val x_1 = new c_1 in any_1) x_1 any_2)
   (val x_1 = new c_1 in any_1)]
  [(subst (rfn T_1 x_1 D_1 ...) x_1 any_2)
   (rfn (subst T_1 x_1 any_2) x_1 D_1 ...)]
  
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst (m_1 x_1 any_1) x_2 any_2)
   (m_1 x_3
        (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (val x_1 = new c_1 in any_1) x_2 any_2)
   (val x_3 = new (subst (subst-var c_1 x_1 x_3) x_2 any_2) in
        (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 c_1 any_1 any_2))
                                (term x_1)))]
  [(subst (rfn T_1 x_1 D_1 ...) x_2 any_2)
   (rfn (subst T_1 x_2 any_2) x_3 (subst (subst-var D_1 x_1 x_3) x_2 any_2) ...)
   (where x_3 ,(variable-not-in (term (D_1 ... x_2 any_2))
                                (term x_1)))]

  ;; do not treat labels as variables
  [(subst (cv variable_1) x_1 any_1) (cv variable_1)]
  [(subst (cm variable_1) x_1 any_1) (cm variable_1)]
  [(subst (cc variable_1) x_1 any_1) (cc variable_1)]
  [(subst (ca variable_1) x_1 any_1) (ca variable_1)]

  ;; 3. replace x_1 with any_1
  [(subst x_1 x_1 any_1) any_1]
  
  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2])

(define-metafunction dot
  subst-var : any x x -> any
  [(subst-var (cv variable_1) x_1 x_2) (cv variable_1)]
  [(subst-var (cm variable_1) x_1 x_2) (cm variable_1)]
  [(subst-var (cc variable_1) x_1 x_2) (cc variable_1)]
  [(subst-var (ca variable_1) x_1 x_2) (ca variable_1)]

  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

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
  [(red store (in-hole ec (val x = new c in e)) (in-hole ec (subst e x loc_new)) (store-extend store (subst c x loc_new)))
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
  [(ev store_i (val x_i = new c_i in e_i)) (v_f store_f)
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
  [(fn (val x_1 = new c_1 in any_1) x_1) #f]
  [(fn (rfn T_1 x_1 D_1 ...) x_1) (fn T_1 x_1)]

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
  [(is_wf-type (T_p ...) (Gamma store) (rfn T z D ...)) #t
   (side-condition (term (is_wf-type (T_p ...) (Gamma store) T)))
   (where env_extended ((gamma-extend Gamma z (rfn T z D ...)) store))
   (side-condition (andmap (lambda (d) (judgment-holds (wf-decl env_extended ,d))) (term (D ...))))]
  [(is_wf-type (T_p ...) env (sel p Lt)) #t
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S U) any_bound)
   (judgment-holds (subtype env S Bot))]
  [(is_wf-type (T_p ...) env (sel p Lt)) #t
   (side-condition (not (member (term (sel p Lt)) (term (T_p ...)))))
   (where any_bound (membership-type-lookup env p Lt))
   (judgment-holds (found any_bound #t))
   (where (S U) any_bound)
   (side-condition (term (is_wf-type ((sel p Lt) T_p ...) env S)))
   (side-condition (term (is_wf-type ((sel p Lt) T_p ...) env U)))]
  [(is_wf-type (T_p ...) env (T_1 ∧ T_2)) #t
   (side-condition (term (is_wf-type (T_p ...) env T_1)))
   (side-condition (term (is_wf-type (T_p ...) env T_2)))]
  [(is_wf-type (T_p ...) env (T_1 ∨ T_2)) #t
   (side-condition (term (is_wf-type (T_p ...) env T_1)))
   (side-condition (term (is_wf-type (T_p ...) env T_2)))]
  [(is_wf-type (T_p ...) env Bot) #t]
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
   ,(cons (term (: l (T_1 ∧ T_2)))
          (term (decl-intersection (Dl_1 ...) (Dl_2 ...))))]
  [(decl-intersection ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   ,(append (term (Dl_before ...))
            (term (decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))))]
  [(decl-intersection (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   ,(append (term (Dl_before ...))
            (term (decl-intersection ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))))]
  [(decl-intersection ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(cons (term (: Lm (S_1 ∨ S_2) (U_1 ∧ U_2)))
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
   ,(cons (term (: l (T_1 ∨ T_2)))
          (term (decl-union (Dl_1 ...) (Dl_2 ...))))]
  [(decl-union ((: l T_1) Dl_1 ...) (Dl_before ... (: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union (Dl_before ... (: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))
   (decl-union ((: l T_1) Dl_1 ...) ((: l T_2) Dl_2 ...))]
  [(decl-union ((: Lm S_1 U_1) DLm_1 ...) ((: Lm S_2 U_2) DLm_2 ...))
   ,(cons (term (: Lm (S_1 ∧ S_2) (U_1 ∨ U_2)))
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
   (Top Bot)
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bot))]  
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
   Bot
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bot))]
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
   (Top Bot)
   (judgment-holds (typeof env_1 e_1 T_e))
   (judgment-holds (subtype env_1 T_e Bot))]
  [(membership-method-lookup env_1 e_1 m_1)
   #f])

(define max-iter 100)

(define-judgment-form dot
  #:mode (expansion-iter I I I I O)
  #:contract (expansion-iter (T ...) env z T ((DLt ...) (Dl ...) (Dm ...)))
  [(expansion-iter (T_p ...) env z Top (() () ()))]
  [(expansion-iter (T_p ...) env z (-> S T) (() () ()))]
  [(expansion-iter (T_p ...) env z_1 (rfn T_1 z_2 DLt_1 ... Dl_1 ... Dm_1 ...)
                   ((decl-intersection (sorted-decls (subst (DLt_1 ...) z_2 z_1)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dl_1 ...) z_2 z_1)) (sorted-decls (Dl_2 ...)))
                    (decl-intersection (sorted-decls (subst (Dm_1  ...) z_2 z_1)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (T_p ... (rfn T_1 z_2 DLt_1 ... Dl_1 ... Dm_1 ...)) env z_1 T_1 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (T_p ...) env z (T_1 ∧ T_2)
                   ((decl-intersection (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-intersection (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...)))
                    (decl-intersection (sorted-decls (Dm_1  ...)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (T_p ... (T_1 ∧ T_2)) env z T_1 ((DLt_1 ...) (Dl_1 ...) (Dm_1 ...)))
   (expansion-iter (T_p ... (T_1 ∧ T_2)) env z T_2 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (T_p ...) env z (T_1 ∨ T_2)
                   ((decl-union (sorted-decls (DLt_1 ...)) (sorted-decls (DLt_2 ...)))
                    (decl-union (sorted-decls (Dl_1  ...)) (sorted-decls (Dl_2  ...)))
                    (decl-union (sorted-decls (Dm_1  ...)) (sorted-decls (Dm_2  ...)))))
   (expansion-iter (T_p ... (T_1 ∨ T_2)) env z T_1 ((DLt_1 ...) (Dl_1 ...) (Dm_1 ...)))
   (expansion-iter (T_p ... (T_1 ∨ T_2)) env z T_2 ((DLt_2 ...) (Dl_2 ...) (Dm_2 ...)))]
  [(expansion-iter (T_p ...) env z (sel p Lt) ((DLt_u ...) (Dl_u ...) (Dm_u ...)))
   (where any_bound (membership-type-lookup env p Lt))
   (found any_bound #t)
   (where (S_p (side-condition U_p (and (not (member (term U_p) (term (T_p ... (sel p Lt)))))
                                        (< (length (term (T_p ...))) max-iter))))
          any_bound)
   (expansion-iter (T_p ... (sel p Lt)) env z U_p ((DLt_u ...) (Dl_u ...) (Dm_u ...)))]
  [(expansion-iter (T_p ...) env z Bot (((: (ca kludge) Top Bot)) () ()))]) ;; kludge

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
  [(is_subtype ((T_a T_b) ...) env Bot T) #t
   (judgment-holds (wfe-type env T))]
  [(is_subtype ((T_a T_b) ...) env S (rfn T z DLt ... Dl ... Dm ...)) #t
   (judgment-holds (wfe-type env (rfn T z DLt ... Dl ... Dm ...)))
   (side-condition (term (is_subtype ((T_a T_b) ... (S (rfn T z DLt ... Dl ... Dm ...))) env S T)))
   (judgment-holds (expansion env z S ((DLt_s ...) (Dl_s ...) (Dm_s ...))))
   (where (Gamma store) env)
   (where Gamma_z (gamma-extend Gamma z S))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (DLt_s ...)) (sorted-decls (DLt ...))))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (Dl_s ...)) (sorted-decls (Dl ...))))
   (judgment-holds (subdecls (Gamma_z store) (sorted-decls (Dm_s ...)) (sorted-decls (Dm ...))))]
  [(is_subtype ((T_a T_b) ...) env (rfn T_1 z DLt ... Dl ... Dm ...) T_2) #t
   (judgment-holds (wfe-type env (rfn T_1 z DLt ... Dl ... Dm ...)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((rfn T_1 z DLt ... Dl ... Dm ...) T_2)) env T_1 T_2)))]
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
  [(is_subtype ((T_a T_b) ...) env T_o (T_1 ∧ T_2)) #t
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∧ T_2))) env T_o T_1)))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∧ T_2))) env T_o T_2)))]
  [(is_subtype ((T_a T_b) ...) env (T_1 ∧ T_2) T_o) #t
   (judgment-holds (wfe-type env T_2))
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∧ T_2) T_o)) env T_1 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (T_1 ∧ T_2) T_o) #t
   (judgment-holds (wfe-type env T_1))
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∧ T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env (T_1 ∨ T_2) T_o) #t
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∨ T_2) T_o)) env T_1 T_o)))
   (side-condition (term (is_subtype ((T_a T_b) ... ((T_1 ∨ T_2) T_o)) env T_2 T_o)))]
  [(is_subtype ((T_a T_b) ...) env T_o (T_1 ∨ T_2)) #t
   (judgment-holds (wfe-type env T_2))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∨ T_2))) env T_o T_1)))]
  [(is_subtype ((T_a T_b) ...) env T_o (T_1 ∨ T_2)) #t
   (judgment-holds (wfe-type env T_1))
   (side-condition (term (is_subtype ((T_a T_b) ... (T_o (T_1 ∨ T_2))) env T_o T_2)))]
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
  [(typeof (Gamma store) (val x = new (Tc (l vx) ... (m x_m e_m) ...) in e) T)
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

(define-metafunction dot
  arrow- : x (DLt ...) S T -> W
  [(arrow- x (DLt ...) S T) (rfn Top x
                              DLt ...
                              (: (cm apply) S T))])

(define-metafunction dot
  fun- : x (DLt ...) (x S) T e -> e
  [(fun- x_f (DLt ...) (x S) T e)
   (val x_f = new ((arrow- x_f (DLt ...) S T) [(cm apply) x e]) in x_f)])

(define-metafunction dot
  arrow : S T -> W
  [(arrow S T) (arrow- x_self () S T)
   (where x_self ,(variable-not-in (term (S T)) 'self))])

(define-metafunction dot
  fun : x S T e -> e
  [(fun x S T e) (fun- x_f () (x S) T e)
   (where x_f ,(variable-not-in (term (x S T e)) 'f))])

(define-metafunction dot
  app : e e -> e
  [(app e_1 e_2) (sel e_1 (cm apply) e_2)])

(define-metafunction dot
  cast : T e -> e
  [(cast T e) (app (fun x T T x) e)
   (where x ,(variable-not-in (term (T e)) 'id))])

(define-metafunction dot
  as : T e -> e
  [(as T e) (cast T e)])

(define (dotExample)
  (term (val dummy = new (Top) in
        (val root = new ((rfn
                          Top rootThis
                          (: (cc UnitClass) Bot Top)
                          (: (cc BooleanClass) Bot (rfn
                                                    Top this
                                                    (: (cm ifNat) Top
                                                       (arrow (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc NatClass)))
                                                              (arrow (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc NatClass)))
                                                                     (sel rootThis (cc NatClass)))))))
                          (: (cc NatClass) Bot (rfn
                                                Top this
                                                (: (cm isZero) Top
                                                   (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc BooleanClass))))
                                                (: (cm pred) Top
                                                   (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc NatClass))))
                                                (: (cm succ) Top
                                                   (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc NatClass))))))
                          (: (cm unit) Top (arrow Top (sel rootThis (cc UnitClass))))
                          (: (cm false) Top (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc BooleanClass))))
                          (: (cm true) Top (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc BooleanClass))))
                          (: (cm zero) Top (arrow (sel rootThis (cc UnitClass)) (sel rootThis (cc NatClass))))
                          (: (cm successor) Top (arrow (sel rootThis (cc NatClass)) (sel rootThis (cc NatClass)))))
                         [(cm unit) dummy (fun x Top (sel root (cc UnitClass)) (val u = new ((rfn (sel root (cc UnitClass)) this)) in u))]
                         [(cm false) dummy
                                     (fun u (sel root (cc UnitClass)) (sel root (cc BooleanClass))
                                          (val ff = new ((rfn (sel root (cc BooleanClass)) this)
                                                         [(cm ifNat) dummy
                                                                     (fun t (arrow (sel root (cc UnitClass)) (sel root (cc NatClass)))
                                                                          (arrow (arrow (sel root (cc UnitClass)) (sel root (cc NatClass))) (sel root (cc NatClass)))
                                                                          (fun e (arrow (sel root (cc UnitClass)) (sel root (cc NatClass)))
                                                                               (sel root (cc NatClass))
                                                                               (app e (app (sel root (cm unit) dummy) (sel root (cm unit) dummy)))))]) in ff))]
                         [(cm true) dummy
                                    (fun u (sel root (cc UnitClass)) (sel root (cc BooleanClass))
                                         (val tt = new ((rfn (sel root (cc BooleanClass)) this)
                                                        [(cm ifNat) dummy
                                                                    (fun t (arrow (sel root (cc UnitClass)) (sel root (cc NatClass)))
                                                                         (arrow (arrow (sel root (cc UnitClass)) (sel root (cc NatClass))) (sel root (cc NatClass)))
                                                                         (fun e (arrow (sel root (cc UnitClass)) (sel root (cc NatClass)))
                                                                              (sel root (cc NatClass))
                                                                              (app t (app (sel root (cm unit) dummy) (sel root (cm unit) dummy)))))]) in tt))]
                         [(cm zero) dummy
                                    (fun u (sel root (cc UnitClass)) (sel root (cc NatClass))
                                         (val zz = new ((rfn (sel root (cc NatClass)) this)
                                                        [(cm isZero) dummy (fun u (sel root (cc UnitClass)) (sel root (cc BooleanClass))
                                                                                (app (sel root (cm true) dummy) (app (sel root (cm unit) dummy) (sel root (cm unit) dummy))))]
                                                        [(cm succ) dummy (fun u (sel root (cc UnitClass)) (sel root (cc NatClass))
                                                                              (app (sel root (cm successor) dummy) zz))]
                                                        [(cm pred) dummy (fun u (sel root (cc UnitClass)) (sel root (cc NatClass)) zz)]) in zz))]
                         [(cm successor) dummy
                                         (fun n (sel root (cc NatClass)) (sel root (cc NatClass))
                                              (val ss = new ((rfn (sel root (cc NatClass)) this)
                                                             [(cm isZero) dummy (fun u (sel root (cc UnitClass)) (sel root (cc BooleanClass)) 
                                                                                     (app (sel root (cm false) dummy) (app (sel root (cm unit) dummy) (sel root (cm unit) dummy))))]
                                                             [(cm succ) dummy (fun u (sel root (cc UnitClass)) (sel root (cc NatClass))
                                                                                   (app (sel root (cm successor) dummy) ss))]
                                                             [(cm pred) dummy (fun u (sel root (cc UnitClass)) (sel root (cc NatClass)) n)]) in ss))]) in
(app (fun x Top Top x)
     (app (fun unit (sel root (cc UnitClass)) (sel root (cc BooleanClass))
               (app (sel (app (sel (app (sel (app (sel root (cm zero) dummy) unit)
                                             (cm succ) dummy) unit)
                                   (cm pred) dummy) unit)
                         (cm isZero) dummy) unit)
               ) (app (sel root (cm unit) dummy) (sel root (cm unit) dummy))))))))

(define-metafunction dot
  wf-prog : any -> bool
  [(wf-prog (rfn T z DLt ... Dl ... Dm ...)) #f
   (side-condition (not (equal? (term (DLt ... Dl ... Dm ...)) (remove-duplicates (term (DLt ... Dl ... Dm ...)) #:key cadadr))))]
  [(wf-prog (any_1 ...))
   ,(andmap (lambda (x) x) (term ((wf-prog any_1) ...)))]
  [(wf-prog any_1) #t]) 

(define-metafunction dot
  lc-decls : any -> (variable ...)
  [(lc-decls (: (cc variable_1) S_1 U_1))
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
                [_ #f]))))
      #t))

(define (subtyping-transitive env s t u)
  (if (and (judgment-holds (wfe-type ,env ,s)) (judgment-holds (wfe-type ,env ,t)) (judgment-holds (wfe-type ,env ,u))
           (judgment-holds (subtype ,env ,s ,t)) (judgment-holds (subtype ,env ,t ,u)))
      (begin
        ;(printf "trying ~a ~a ~a ~a\n" env s t u)
        (judgment-holds (subtype ,env ,s ,u)))
      #t))
