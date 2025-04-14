/- Layout of this File: -/
/-
  The user writes programs in a subset of the jaxpr language. Jaxpr expressions
  are first preprocessed into ATL programs. Then ATL programs are normalized
  into the SSA form. Operational semantics is defined for the SSA form of ATL.
  After normalization, we just run the SSA form program based on the operational
  semantics.

  The file contains the following sections:
  - Syntax of ATL in SSA form
  - Functions for transforming jaxpr into ATL SSA form
    (and jaxpr's syntax, which is just a few lines since
     it's very similar to ATL)
  - Operational semantics of ATL in SSA form
    (including "built in" primitive functions for jaxpr implementd in ATL)
-/

/- modifications to jax: 
   - no named arguments for primitive functions, only simple let bindings,
     only one variable on lhs, one expression on right
   - 
-/

/-************** ATL Syntax in Single-Static-Assignment Form *******************-/
inductive stmt_var
| stmtV : String → Nat → stmt_var
/- since ATL is in normal form, index variables can be standardized into only 4 possible cases -/
inductive ind_var
| gen : Nat → ind_var
| sums : Nat → ind_var
| sum0 : Nat → ind_var
| sum1 : Nat → ind_var

inductive ind_exp 
| var : ind_var → ind_exp
| const : Nat → ind_exp
| add : ind_exp → ind_exp → ind_exp
| mult : ind_exp → ind_exp → ind_exp 
| sub : ind_exp → ind_exp → ind_exp
| div : ind_exp → ind_exp → ind_exp 

inductive pred 
| true
| false
| eq : ind_exp → ind_exp → pred
| le : ind_exp → ind_exp → pred
| lt : ind_exp → ind_exp → pred
| and : pred → pred → pred
| or : pred → pred → pred

inductive binPrim
| add
| mult
| sub
| div
inductive uniPrim
| neg
/- scalar expressions -/
inductive exp  
| const : Nat → exp
| binOp : 
  pred → stmt_var → binPrim →
  pred → stmt_var → exp
| uniOp : 
  pred → uniPrim → stmt_var → exp
| binTenSum : 
  List Nat → List Nat → List Nat →
  pred → stmt_var → stmt_var → exp
| uniTenSum :
  List Nat → List Nat →
  pred → stmt_var → exp

inductive tenVal
| val : List Nat → List Nat → tenVal

inductive genIndBound
| const : Nat → genIndBound
| var : stmt_var → Nat → genIndBound
| max : stmt_var → Nat → stmt_var → Nat → genIndBound
/- tensor expession -/
inductive unitTenExp  
| gen : List genIndBound → exp → unitTenExp
| var : stmt_var → unitTenExp
| val : tenVal → unitTenExp
inductive tenStmt
| stmt : stmt_var → unitTenExp → tenStmt
| skip
inductive tenExp
| letList : List tenStmt → stmt_var → tenExp
/- functions taking tensors as input and returns a tensor, SSA without structs -/
/- list of input vars (vars that don't occur in lhs before they occur in rhs) 
   and list of statements -/
inductive tenFunc 
| func : List stmt_var → tenExp → tenFunc

/-******************** Jaxpr and Lowering it to ATL ********************-/
inductive jStmt
| stmt : stmt_var → String → List stmt_var → jStmt
| skip
inductive jaxpr_body 
| letList : List jStmt → stmt_var → jaxpr_body
inductive jaxpr  
| func : List stmt_var → jaxpr_body → jaxpr

def subst_lst_gen paras args (suf : Nat) :=
  match paras, args with
  | [], _ => []
  | _, [] => []
  | (stmt_var.stmtV para _) :: rstparas, 
    arg :: rstargs =>
    (tenStmt.stmt (stmt_var.stmtV para suf) (unitTenExp.var arg)) :: 
    subst_lst_gen rstparas rstargs suf
def var_suf_set stVar suf :=
  match stVar with
  | stmt_var.stmtV var _ => stmt_var.stmtV var suf
def exp_suf_update (suf : Nat) : exp → exp
  | exp.const c => exp.const c
  | exp.binOp p1 var1 op
               p2 var2 =>
    exp.binOp p1 (var_suf_set var1 suf) op
               p2 (var_suf_set var2 suf)
  | exp.uniOp p f var =>
    exp.uniOp p f (var_suf_set var suf)
  | exp.binTenSum indLst1 indLst2 indLst3
                   p var1 var2 =>
    exp.binTenSum indLst1 indLst2 indLst3 p
                   (var_suf_set var1 suf) (var_suf_set var2 suf)
  | exp.uniTenSum indLst1 indLst2 p var =>
    exp.uniTenSum indLst1 indLst2 p (var_suf_set var suf)
def suf_update suf 
  | tenStmt.stmt varLHS (unitTenExp.var varRHS) =>
    tenStmt.stmt (var_suf_set varLHS suf) (unitTenExp.var (var_suf_set varRHS suf))
  | tenStmt.stmt svar (unitTenExp.gen indList e) =>
    tenStmt.stmt (var_suf_set svar suf) (unitTenExp.gen indList (exp_suf_update suf e))
  | tenStmt.stmt svar (unitTenExp.val val) =>
    tenStmt.stmt svar (unitTenExp.val val)
  | tenStmt.skip => tenStmt.skip
def inline_prims stmts (env : String → tenFunc) (var_suf : Nat) :=
  match stmts with
  | [] => []
  | jStmt.stmt target_var prim_name arg_vars :: rst =>
    match env prim_name with
    | tenFunc.func inp_vars (tenExp.letList fstmts (stmt_var.stmtV outName _)) =>
      subst_lst_gen inp_vars arg_vars var_suf ++
      (List.map (suf_update var_suf) fstmts) ++
      tenStmt.stmt target_var (unitTenExp.var (stmt_var.stmtV outName var_suf)) ::
        inline_prims rst env (1 + var_suf)
  | jStmt.skip :: rst => tenStmt.skip :: inline_prims rst env var_suf
/- transform a jaxpr into an ATL, by inlining primitives from environment -/
def body_trans env body :=
  match body with
  | jaxpr_body.letList stmts out_var =>
    tenExp.letList (inline_prims stmts env 1) out_var
def jax_to_ATL p env :=
  match p with
  | jaxpr.func inp_vars body => 
    tenFunc.func inp_vars (body_trans env body)

/-********************* ATL Semantics in Single-Static-Assignment Form ********************-/
/- given statement list and input environment, 
   return final environment after statements execute -/

/- Helper Functions for Updating Index Variable Environment -/
def ivar_env := ind_var → Nat
def empty_ienv := fun (_ : ind_var) => 0
def ivar_eq
  | ind_var.gen a, ind_var.gen b => a == b
  | ind_var.sums a, ind_var.sums b => a == b
  | ind_var.sum0 a, ind_var.sum0 b => a == b
  | ind_var.sum1 a, ind_var.sum1 b => a == b
  | _, _ => false
def update_ienv (env : ivar_env) (para : ind_var) (arg : Nat) :=
  fun x => if ivar_eq x para then arg else env x
def update_ienv_star env (paras : List ind_var) (args : List Nat) :=
  match paras, args with
  | _, [] => env
  | [], _ => env
  | para :: paras', arg :: args' =>
    update_ienv_star (update_ienv env para arg) paras' args'
/- https://www.leanprover.cn/mp-lean-zh/main/05_syntax.html -/
notation (name := env_update) para:arg "!->i" arg:arg ";" env:arg =>
  (update_ienv env para arg)
notation (name := env_updates) paras:arg "!->i*" args:arg ";" env:arg =>
  (update_ienv_star env paras args)

/- Helper Functions for Updating Statement Variable Environment -/
def svar_env := stmt_var → tenVal
def empty_senv : svar_env :=
  fun _ => tenVal.val [] []
def svar_eq
  | stmt_var.stmtV str1 n1, stmt_var.stmtV str2 n2 =>
    Bool.and (str1 == str2) (n1 == n2)
def update_senv {A} (env : stmt_var → A) (para : stmt_var) (arg : A) :=
  fun x => if svar_eq x para then arg else env x
def update_senv_star {A} (env : stmt_var → A) (paras : List stmt_var) (args : List A) :=
  match paras, args with
  | _, [] => env
  | [], _ => env
  | para :: paras', arg :: args' =>
    update_senv_star (update_senv env para arg) paras' args'
notation (name := senv_update) para:arg "!->s" arg:arg ";" env:arg =>
  (update_senv env para arg)
notation (name := senv_updates) paras:arg "!->s*" args:arg ";" env:arg =>
  (update_senv_star env paras args)
/- Helper Functions for Working with Indices and Predicates -/
def ind_incr ivar :=
  match ivar with
  | ind_var.gen n => 
    ind_var.gen (Nat.succ n)
  | ind_var.sums n => 
    ind_var.sums (Nat.succ n)
  | ind_var.sum1 n => 
    ind_var.sum1 (Nat.succ n)
  | ind_var.sum0 n => 
    ind_var.sum0 (Nat.succ n)
def sum_ind_incr bound_s bound1
  | ind_var.gen n => 
    ind_var.gen (Nat.succ n)
  | ind_var.sums n => 
    if bound_s < n then ind_var.sum1 0
    else ind_var.sums (Nat.succ n)
  | ind_var.sum1 n => 
    if bound1 < n then ind_var.sum0 0
    else ind_var.sum1 (Nat.succ n)
  | ind_var.sum0 n => 
    ind_var.sum0 (Nat.succ n)
def eval_ind ie (env : ivar_env) :=
  match ie with
  | ind_exp.var ivar => env ivar
  | ind_exp.const c => c
  | ind_exp.add ie1 ie2 => 
    (eval_ind ie1 env) + (eval_ind ie2 env) 
  | ind_exp.mult ie1 ie2 =>
    (eval_ind ie1 env) * (eval_ind ie2 env)
  | ind_exp.sub ie1 ie2 => 
    (eval_ind ie1 env) - (eval_ind ie2 env) 
  | ind_exp.div ie1 ie2 => 
    (eval_ind ie1 env) / (eval_ind ie2 env) 
def eval_pred_bool p env :=
  match p with
  | pred.true => true
  | pred.false => false
  | pred.eq ie1 ie2 => 
    (eval_ind ie1 env) == (eval_ind ie2 env)
  | pred.le ie1 ie2 => 
    (eval_ind ie1 env) ≤ (eval_ind ie2 env)
  | pred.lt ie1 ie2 => 
    (eval_ind ie1 env) < (eval_ind ie2 env)
  | pred.and p1 p2 => 
    if eval_pred_bool p1 env 
    then eval_pred_bool p2 env else false
  | pred.or p1 p2 => 
    if eval_pred_bool p1 env 
    then true else eval_pred_bool p2 env
def eval_pred p env :=
  match eval_pred_bool p env with
  | true => 1
  | false => 0
/- Evaluating Scalar Expressions -/
/- recursively update the three lists, decrement them, and the expression
  we have below is the expression for each iteration. The arguments
  ind_lst* correspond to the exact state of the counter -/
def decr_lst
  | [] => []
  | 0 :: lst' => 0 :: (decr_lst lst')
  | Nat.succ n :: lst' => n :: lst'
/- true if all zeros or empty list -/
def is_all_zeros
  | [] => true
  | 0 :: lst' => is_all_zeros lst'
  | Nat.succ _ :: _ => false 


/-
def sum_2lst ind_lst1 ind_lst2 e env :=
  let summand := (eval_var_acc e 
  (var_lst1 !->i* ind_lst1; 
  (var_lst2 !->i* ind_lst2; env)))
  match is_all_zeros ind_lst1, is_all_zeros ind_lst2 with
  | false, _ => summand + (sum_2lst (decr_lst ind_lst1) ind_lst2 e env)
  | true, false => summand + (sum_2lst ind_lst1 (decr_lst ind_lst2) e env)
  | true, true => summand
def sum_3lst ind_lst1 ind_lst2 ind_lst3 e env :=
  let summand := (eval_var_acc e 
  (var_lst1 !->i* ind_lst1; 
  (var_lst2 !->i* ind_lst2; 
  (var_lst3 !->i* ind_lst3; env))))
  match is_all_zeros ind_lst1, is_all_zeros ind_lst2, is_all_zeros ind_lst3 with
  | false, _, _ => summand + (sum_3lst (decr_lst ind_lst1) ind_lst2 ind_lst3 e env)
  | true, false, _ => summand + (sum_3lst ind_lst1 (decr_lst ind_lst2) ind_lst3 e env)
  | true, true, false => summand + (sum_3lst ind_lst1 ind_lst2 (decr_lst ind_lst3) e env)
  | true, true, true => summand
-/
def ten_val_acc (shape : List Nat) (content : List Nat) (ind_lst : List Nat) begin_ptr end_ptr :=
  match shape, ind_lst with
  | [], [] => content.getD begin_ptr 0
  | n :: rst_shape, i :: rst_ind_lst =>
    let one_slice := (List.length content) / n
    let new_begin := one_slice * i
    let new_end := one_slice * (1 + i)
    ten_val_acc rst_shape content rst_ind_lst new_begin new_end
  | _, _ => 0 /- other cases impossible -/
def access (senv : svar_env) (ienv : ivar_env) var (acc_lst : List ind_var) :=
  match senv var with
  | tenVal.val shape content =>
    ten_val_acc shape content 
      (List.map ienv acc_lst) 0 (List.length content)
def bin_op_app op (n1 n2 : Nat) :=
  match op with
  | binPrim.add => n1 + n2
  | binPrim.sub => n1 - n2
  | binPrim.mult => n1 * n2
  | binPrim.div => n1 / n2
def uni_op_app op (n : Nat) :=
  match op with
  | uniPrim.neg => 0 - n
def sum_tensor_h (sum_inds : List Nat) f senv ienv cur_ind (incr : ind_var -> ind_var) :=
  match sum_inds with
  | []  => f senv ienv
  | n :: rst_sum_inds =>
    sum_list cur_ind n f ienv senv rst_sum_inds incr
where sum_list (cur_ind : ind_var) length (f : svar_env -> ivar_env -> Nat) 
(ienv : ivar_env) (senv : svar_env) (sum_inds : List Nat) (incr: ind_var -> ind_var) :=
  match length with
  | 0 => 0
  | Nat.succ n => 
    (sum_list cur_ind n f ienv senv sum_inds incr) +
    (sum_tensor_h sum_inds f senv (cur_ind !->i n ; ienv) (incr cur_ind) incr)
def sum_1tens sum_ind sum_ind_tens p var ind_acc senv ienv :=
  let f := fun senv ienv => 
           if eval_pred_bool p ienv 
           then access senv ienv var ind_acc
           else 0
  let incr := sum_ind_incr (List.length sum_ind) 0
  sum_tensor_h (sum_ind ++ sum_ind_tens) f senv ienv (ind_var.sums 0) incr
def sum_2tens sum_ind1 sum_ind2 sum_ind3 p var1 ind_acc1 var2 ind_acc2 senv ienv :=
  let f := fun senv ienv => 
           if eval_pred_bool p ienv then
           (access senv ienv var1 ind_acc1) * (access senv ienv var2 ind_acc2)
           else 0
  let incr := sum_ind_incr (List.length sum_ind1) (List.length sum_ind2)
  sum_tensor_h (sum_ind1 ++ sum_ind2 ++ sum_ind3) f senv ienv (ind_var.sums 0) incr
def iota 
  | 0 => []
  | Nat.succ n =>  (iota n) ++ [n]
def eval_exp (senv : svar_env) (ienv : ivar_env) (gen_ind_acc : List ind_var) : exp → Nat
  | exp.const c => c
  | exp.binOp p1 var1 op p2 var2 =>
    let arg1 := if eval_pred_bool p1 ienv
                then access senv ienv var1 gen_ind_acc 
                else 0 
    let arg2 := if eval_pred_bool p2 ienv
                then access senv ienv var2 gen_ind_acc
                else 0 
    bin_op_app op arg1 arg2
  | exp.uniOp p f var =>
    if eval_pred_bool p ienv
    then uni_op_app f (access senv ienv var gen_ind_acc)
    else 0
  | exp.binTenSum n0 n1 ns p var0 var1 =>
    let ind_acc0 := List.map ind_var.sums (iota (List.length n0))
    let ind_acc1 := List.map ind_var.sum1 (iota (List.length n1))
    sum_2tens n0 n1 ns p var0 ind_acc0 var1 ind_acc1 senv ienv
  | exp.uniTenSum n nS p var =>
    let ind_acc := List.map ind_var.sums (iota (List.length n))
    sum_1tens n nS p var ind_acc senv ienv
    
/- Evaluating Tensor Expressions -/
/-  
/- environment gives 0 by default, so shape list can be shrunk and information not lost-/
def gen_tensor_h (shape counter : List Nat) (e : exp) senv ienv :=
  let element := (eval_exp senv ((gen_ind_lst (List.length counter)) !->i* counter; ienv) e)
  match counter with
  | [] => [element]
  | 0 :: lst' => gen_tensor_h shape lst' e senv ienv
  | Nat.succ n :: lst' => 
    (gen_tensor_h shape (n :: lst') e senv ienv) ++ [element]
  
/- turn the last index to front -/
def gen_tensor shape e senv := 
  tenVal.TVal shape (gen_tensor_h (List.reverse shape) (List.reverse shape) e senv empty_ienv)
-/

def gen_ind_lst
  | 0 => []
  | Nat.succ n =>  (gen_ind_lst n) ++ [ind_var.gen n]

/- gen tensor is gen list applied many times-/
def gen_tensor_h (shape : List Nat) e senv ienv cur_ind (gen_ind_lst : List ind_var) :=
  match shape with
  | []  => [eval_exp senv ienv gen_ind_lst e]
  | n :: rst_shape =>
    gen_list cur_ind n e ienv senv rst_shape gen_ind_lst
where gen_list cur_ind_var length (e : exp) (ienv : ivar_env) 
      (senv : svar_env) (shape : List Nat) (gen_ind_lst : List ind_var) :=
  match length with
  | 0 => []
  | Nat.succ n => 
    (gen_list cur_ind_var n e ienv senv shape gen_ind_lst) ++
    gen_tensor_h shape e senv (cur_ind_var !->i n ; ienv) (ind_incr cur_ind_var) gen_ind_lst

def gen_tensor shape e senv := 
  let gen_ind_lst := List.map ind_var.gen (iota (List.length shape))
  tenVal.val shape (gen_tensor_h shape e senv empty_ienv (ind_var.gen 0) gen_ind_lst)
def get_shape_tm (senv : svar_env) var :=
  match senv var with
  | tenVal.val shape _ => shape

def eval_shape {X} (get_shape : (svar → X) → stmt_var → List Nat) env
  | [] => []
  | genIndBound.const n :: rst_shape => n :: (eval_shape get_shape env rst_shape)
  | genIndBound.var name ind :: rst_shape =>
    (get_shape env name).getD ind 0 :: (eval_shape get_shape env rst_shape)
  | genIndBound.max name1 ind1 name2 ind2 :: rst_shape =>
    let n1 := (get_shape env name1).getD ind1 0
    let n2 := (get_shape env name2).getD ind2 0
    max n1 n2 :: (eval_shape get_shape env rst_shape)
def eval_shape_tm env shape := eval_shape get_shape_tm env shape
def eval_texp e senv := 
  match e with
  | unitTenExp.gen shape e' =>
    gen_tensor (eval_shape_tm senv shape) e' senv
  | unitTenExp.var var =>
    senv var
  | unitTenExp.val val => val
/- Evaluating Programs Expressions -/
/- given start environment, return environment after statements execute -/

def eval_stmts (env : svar_env) :
  List tenStmt → svar_env
  | [] => env
  | (tenStmt.stmt x e) :: rst_stmts =>
    let new_env := x !->s (eval_texp e env) ; env
    eval_stmts new_env rst_stmts
  | tenStmt.skip :: rst_stmts =>
    eval_stmts env rst_stmts

def eval_prog prog args fenv :=
  match jax_to_ATL prog fenv with
  | tenFunc.func inp_vars (tenExp.letList stmts out) =>
    (eval_stmts (inp_vars !->s* args ; empty_senv) stmts) out
/- ************ Small Step Operational Semantics ************* -/
inductive step_stmt : svar_env × tenStmt →
                      svar_env × tenStmt → Prop where
| stp_stmt : ∀ env var exp,
  val = eval_texp exp env →
  new_env = var !->s val ; env →
  step_stmt (env, (tenStmt.stmt var exp)) (new_env, tenStmt.skip)
inductive step_stmts : svar_env × List tenStmt →
                       svar_env × List tenStmt → Prop where
| stp_skip : ∀ env some_stmts,
  step_stmts (env, tenStmt.skip :: some_stmts) (env, some_stmts)
| stp_stmts : ∀ env new_env stmt new_stmt some_stmts,
  step_stmt (env, stmt) (new_env, new_stmt) →
  step_stmts (env, stmt :: some_stmts) (new_env, new_stmt :: some_stmts)
inductive step_fun_body : svar_env × tenExp →
                          svar_env × tenExp → Prop where
| stp_letList : ∀ env new_env stmts new_stmts out,
  step_stmts (env,stmts) (new_env, new_stmts) →
  step_fun_body (env, tenExp.letList stmts out) (new_env, tenExp.letList new_stmts out)
/-
take a program and get an absmachine initial state is not
part of stepping semantics

inductive steps_prog prog args fenv result
| stps_prog : ∀ inp_vars stmts out final_env,
  jax_to_ATL prog fenv = tenFunc.func inp_vars (tenExp.letList stmts out) →
  steps_stmts (inp_vars !->s* args ; empty_senv) stmts final_env →
  final_env out = result →
  steps_prog prog args fenv result-/
/- ************* Type System & Soundness Proof *************** -/
/- ************* Type Syntax *************** -/
inductive ty_unitTenExp  
| gen : List genIndBound → ty_unitTenExp
| val : List Nat → ty_unitTenExp
| var : stmt_var → ty_unitTenExp

inductive ty_tenStmt
| stmt : stmt_var → ty_unitTenExp → ty_tenStmt
| skip

inductive ty_tenExp
| letList : List ty_tenStmt → stmt_var → ty_tenExp

inductive ty_tenFunc 
| func : List stmt_var → ty_tenExp → ty_tenFunc

/- type of an array value is its shape -/
inductive ty_tenVal
| val : List Nat → ty_tenVal

inductive ty_jStmt
| stmt : stmt_var → String → List stmt_var → ty_jStmt
| skip

inductive ty_jaxpr_body 
| letList : List ty_jStmt → stmt_var → ty_jaxpr_body

inductive ty_jaxpr  
| func : List stmt_var → ty_jaxpr_body → ty_jaxpr
/- ************* Small Step Type Reduction *************** -/
/- type environment -/
def ty_env := stmt_var → ty_tenVal
def empty_tyenv : ty_env :=
  fun _ => ty_tenVal.val []
def lift_senv (senv : svar_env) :=
  fun x => 
  match senv x with
  | tenVal.val shape _ => ty_tenVal.val shape
/- reduction rules -/
def get_shape_ty (senv : ty_env) var :=
  match senv var with
  | ty_tenVal.val shape => shape
def eval_shape_ty env shape := eval_shape get_shape_ty env shape
def eval_ty_texp (senv : ty_env) 
  | ty_unitTenExp.val shape =>
    ty_tenVal.val shape
  | ty_unitTenExp.gen shape =>
    ty_tenVal.val (eval_shape_ty senv shape)
  | ty_unitTenExp.var var => senv var
inductive ty_step_stmt : ty_env × ty_tenStmt →
                         ty_env × ty_tenStmt → Prop where
| stp_stmt : ∀ env var exp_ty,
  val = eval_ty_texp env exp_ty →
  new_env = var !->s val ; env →
  ty_step_stmt (env, (ty_tenStmt.stmt var exp_ty)) (new_env, ty_tenStmt.skip)
inductive ty_step_stmts : ty_env × List ty_tenStmt →
                          ty_env × List ty_tenStmt → Prop where
| stp_skip : ty_step_stmts (env, ty_tenStmt.skip :: some_stmts) (env, some_stmts)
| stp_stmts : ∀ env new_env stmt,
  ty_step_stmt (env, stmt) (new_env, new_stmt) →
  ty_step_stmts (env, stmt :: some_stmts) (new_env, new_stmt :: some_stmts)
inductive ty_step_fun_body : ty_env × ty_tenExp →
                             ty_env × ty_tenExp → Prop where
| stp_letList : ∀ env new_env stmts new_stmts out,
  ty_step_stmts (env,stmts) (new_env, new_stmts) →
  ty_step_fun_body 
    (env, ty_tenExp.letList stmts out) 
    (new_env, ty_tenExp.letList new_stmts out)
inductive ty_step_fun_body_star : ty_env × ty_tenExp →
                                  ty_env × ty_tenExp → Prop where
| no_stp : ∀ env ty, ty_step_fun_body_star (env, ty) (env, ty)
| stps  : ∀ env ty env' ty' env'' ty'', 
  ty_step_fun_body_star (env, ty) (env', ty') →
  ty_step_fun_body (env', ty') (env'', ty'') →
  ty_step_fun_body_star (env, ty) (env'', ty'')
/- ************* Typing Rules *************** -/
inductive has_ty_unitTenExp : unitTenExp → ty_unitTenExp → Prop where
| gen : ∀ gen_tm gen_ty,
  gen_tm = unitTenExp.gen shape e →
  gen_ty = ty_unitTenExp.gen shape →
  has_ty_unitTenExp gen_tm gen_ty
| var : ∀ var_tm var_ty,
  var_tm = unitTenExp.var var →
  var_ty = ty_unitTenExp.var var →
  has_ty_unitTenExp var_tm var_ty
| val : ∀ val_tm val_ty,
  val_tm = unitTenExp.val (tenVal.val shape content) →
  val_ty = ty_unitTenExp.val shape →
  has_ty_unitTenExp val_tm val_ty
inductive has_ty_tenStmt : tenStmt → ty_tenStmt → Prop where
| stmt : ∀ stmt_tm stmt_ty var_tm var_ty exp_tm exp_ty,
  stmt_tm = tenStmt.stmt var_tm exp_tm →
  stmt_ty = ty_tenStmt.stmt var_ty exp_ty →
  svar_eq var_tm var_ty = true →
  has_ty_unitTenExp exp_tm exp_ty →
  has_ty_tenStmt stmt_tm stmt_ty
def has_ty_stmtLst 
  | [], [] => True
  | stmt_tm :: tm_lst, 
    stmt_ty :: ty_lst =>
    has_ty_tenStmt stmt_tm stmt_ty ∧
    has_ty_stmtLst tm_lst ty_lst
  | _, _ => False
inductive has_ty_tenExp : tenExp → ty_tenExp → Prop where
| letList : ∀ letList_tm letList_ty tm_lst ty_lst out_tm out_ty,
  letList_tm = tenExp.letList tm_lst out_tm →
  letList_ty = ty_tenExp.letList ty_lst out_ty →
  svar_eq out_tm out_ty = true →
  has_ty_stmtLst tm_lst ty_lst → 
  has_ty_tenExp letList_tm letList_ty
def svar_lst_eq
  | [], [] => true
  | v1 :: lst1, v2 :: lst2 =>
    if svar_eq v1 v2 then svar_lst_eq lst1 lst2
    else false
  | _, _ => false
inductive has_ty_tenFunc : tenFunc → ty_tenFunc → Prop where
| func : ∀ func_tm func_ty inps_tm inps_ty body_tm body_ty,
  func_tm = tenFunc.func inps_tm body_tm →
  func_ty = ty_tenFunc.func inps_ty body_ty → 
  svar_lst_eq inps_tm inps_ty →
  has_ty_tenExp body_tm body_ty →
  has_ty_tenFunc func_tm func_ty

inductive has_ty_tenVal : tenVal → ty_tenVal → Prop where
| val : ∀ val_tm val_ty,
  val_tm = tenVal.val shape content →
  val_ty = ty_tenVal.val shape →
  has_ty_tenVal val_tm val_ty
inductive has_ty_jStmt : jStmt → ty_jStmt → Prop where
| stmt : ∀ stmt_tm stmt_ty var_tm var_ty 
           prim_tm prim_ty args_tm args_ty,
  stmt_tm = jStmt.stmt var_tm prim_tm args_tm →
  stmt_ty = ty_jStmt.stmt var_ty prim_ty args_ty →
  svar_eq var_tm var_ty = true →
  (prim_tm == prim_ty) = true →
  svar_lst_eq args_tm args_ty →
  has_ty_jStmt stmt_tm stmt_ty
def has_ty_jStmtLst 
  | [], [] => True
  | stmt_tm :: tm_lst,
    stmt_ty :: ty_lst =>
    has_ty_jStmt stmt_tm stmt_ty ∧
    has_ty_jStmtLst tm_lst ty_lst
  | _, _ => False

inductive has_ty_jaxpr_body : jaxpr_body → ty_jaxpr_body → Prop where
| letList : ∀ letList_tm letList_ty 
              tm_lst ty_lst out_tm out_ty,
  letList_tm = jaxpr_body.letList tm_lst out_tm →
  letList_ty = ty_jaxpr_body.letList ty_lst out_ty →
  svar_eq out_tm out_ty = true →
  has_ty_jStmtLst tm_lst ty_lst →
  has_ty_jaxpr_body letList_tm letList_ty

inductive has_ty_jaxpr : jaxpr → ty_jaxpr → Prop where
| func : ∀ func_tm func_ty inps_tm inps_ty body_tm body_ty,
  func_tm = jaxpr.func inps_tm body_tm →
  func_ty = ty_jaxpr.func inps_ty body_ty → 
  svar_lst_eq inps_tm inps_ty →
  has_ty_jaxpr_body body_tm body_ty →
  has_ty_jaxpr func_tm func_ty

inductive is_terminal : tenExp → Prop where
| is_term : ∀ tm out,
  tm = tenExp.letList [] out →
  is_terminal tm

def ty_eq env1 ty1 env2 ty2 :=
  ∃ env ty, 
  ty_step_fun_body_star (env1, ty1) (env, ty) ∧
  ty_step_fun_body_star (env2, ty2) (env, ty)
/-
inductive has_type_atl : tenFunc → ty → Prop where
| T_atl : ∀ body inp_shapes, 
  type_of_free_vars body = inp_shapes →
  has_type_atl_body body out_shapes →
  has_type_atl 
    (tenFunc.TFunc inp_vars body)
    (func_ty inp_shapes out_shapes)
inductive has_type_j_body
inductive has_type_j : jaxpr → ty → Prop where
| T_prog : ∀ jbody inp_shapes, 
  type_of_free_vars jbody = inp_shapes →
  has_type_jbody jbody out_shapes →
  has_type_j 
    (jaxpr.func inp_vars jbody)
    (func_ty inp_shapes out_shapes) -/
/- type abs and app for shapes and ranks -/
/- function type should give info for how to compute a shape when given a list of shapes -/
/- shapes of inputs and shape of output -/
/-
inductive ty 
| func_ty : List (List Nat) → List Nat → ty
| val_ty : List Nat → ty
def type_of_free_vars seen_vars : List (stmt_var × String × List stmt_var) → List (List Nat)
  | jaxpr_body.JLetList [] out => []
  | jaxpr_body.JLetList ((var, prim_func, arg_lst) :: stmt_lst) out =>
    if List.filter seen_vars arg_lst = []
    type_of_free_vars stmt_lst

    
theorem progress : eval_prog simple_prog [arg1,arg2,arg3] prim_env = 
             tenVal.TVal [2,2] [8, 9, 8, 9] := by simp-/
/- ************* Type Soundness *************** -/

theorem progress : ∀ tm env ty,
  has_ty_tenExp tm ty →
  is_terminal tm ∨
  ∃ env' tm', step_fun_body (env, tm) (env', tm') := by
  intros tm env ty H
  cases tm with
  | letList stmts out =>
    cases stmts
    . apply Or.inl; apply is_terminal.is_term ; rfl
    case cons stmt rst_stmts => 
      apply Or.inr
      cases stmt
      case skip => 
        exists env, tenExp.letList rst_stmts out
        apply step_fun_body.stp_letList
        apply step_stmts.stp_skip
      case stmt var exp =>
        exists var !->s (eval_texp exp env) ; env
        exists tenExp.letList (tenStmt.skip :: rst_stmts) out
        apply step_fun_body.stp_letList
        apply step_stmts.stp_stmts
        apply step_stmt.stp_stmt
        . rfl
        . rfl
  
theorem preservation : ∀ tm env tm' env' ty,
  step_fun_body (env, tm) (env', tm') →
  has_ty_tenExp tm ty →
  ∃ ty', 
    has_ty_tenExp tm' ty' ∧
    ty_eq (lift_senv env) ty (lift_senv env') ty' := by
  intros tm env tm' env' ty H_step H_ty
  cases H_step with
  | stp_letList env env' stmts stmts' out H_stp_stmts =>
  cases H_stp_stmts with
  | stp_skip env some_stmts => 
    cases H_ty with
    | letList letList_tm letList_ty out_tm out_ty
              H_tm H_ty H_var_eq H_stmts_ty =>
      subst_vars
      cases H_tm
      cases letList_ty with
      | nil => contradiction
      | cons stmt_ty rst_stmts_ty =>
      exists (ty_tenExp.letList rst_stmts_ty out_ty)
      apply And.intro
      . apply has_ty_tenExp.letList <;> try rfl
        apply H_var_eq
        cases H_stmts_ty with
        | intro left right => apply right
      . 
      unfold has_ty_stmtLst at H_stmts_ty
      simp at H_stmts_ty
      

| letList : ∀ letList_tm letList_ty tm_lst ty_lst out_tm out_ty,
  letList_tm = tenExp.letList tm_lst out_tm →
  letList_ty = ty_tenExp.letList ty_lst out_ty →
  svar_eq out_tm out_ty = true →
  has_ty_stmtLst tm_lst ty_lst → 
  has_ty_tenExp letList_tm letList_ty


  | stp_stmts env env' stmt new_stmt some_stmts H_stp_stmt => 
      
  
    


  cases tm with
  | letList stmts out =>
  cases ty with
  | letList stmts_ty out_ty =>
  cases stmts with
  | nil => contradiction
  | cons stmt rst_stmts =>
  cases stmts_ty with
  | nil => contradiction
  | cons stmt_ty rst_stmts_ty =>
  cases stmt with
  | skip =>
    cases stmt_ty with
    | skip => 
      exists (ty_tenExp.letList rst_stmts_ty out_ty)
      apply And.intro
      . 
    | stmt var exp_ty =>
  | stmt var exp =>
    cases stmt_ty with
    | skip =>
    | stmt var_ty exp_ty =>
       
      
  cases H_step with
  | stp_letList env env' stmts stmts' out H_stp_stmts =>
    cases H_stp_stmts with
    | stp_stmts env env' stmt new_stmt some_stmts H_stp_stmt => 
      
    | stp_skip env some_stmts=> 
    
    
stp_stmts : ∀ env new_env stmt new_stmt some_stmts,
| stp_skip : step_stmts (env, tenStmt.skip :: some_stmts) (env, some_stmts)
| stp_stmts : ∀ env new_env stmt,
  step_stmt (env, stmt) (new_env, new_stmt) →
  step_stmts (env, stmt :: some_stmts) (new_env, new_stmt :: some_stmts)


: ∀ env new_env stmts new_stmts out,
  step_stmts (env,stmts) (new_env, new_stmts) →
  step_fun_body (env, tenExp.letList stmts out) (new_env, tenExp.letList new_stmts out) 
/- ********************* Example  **************************** -/
notation (name := var_name) "!" name:arg => stmt_var.stmtV name 0

def simple_prog :=
  jaxpr.func [!"x", !"y", !"z"]
  (jaxpr_body.letList 
    [(! "a", "add", [!"x",  !"y"]), 
    (!"b", "add", [! "a",  !"z"])] 
    (!"b"))
def add_func :=
  let p := pred.true
  let X1 := stmt_var.stmtV (!"x")
  let X2 := stmt_var.stmtV (!"y")
  tenFunc.func [!"x",  !"y"]
    (tenExp.letList [(! "a", unitTenExp.gen [2, 2] 
                      (exp.binOp p X1 binPrim.add p X2))] (! "a"))
def arg1 := tenVal.val [2,2] [1, 2, 3, 4]
def arg2 := tenVal.val [2,2] [6, 5, 2, 1]
def arg3 := tenVal.val [2,2] [1, 2, 3, 4]
def prim_env
  | "add" => add_func
  | _ => tenFunc.func [] (tenExp.letList [] (! "a"))

theorem eg : eval_prog simple_prog [arg1,arg2,arg3] prim_env = 
             tenVal.val [2,2] [8, 9, 8, 9] := by
 /- converting jax to ATL -/
 unfold eval_prog
 unfold jax_to_ATL
 unfold simple_prog
 unfold body_trans
 simp
 unfold inline_prims
 unfold inline_prims
 unfold inline_prims
 unfold prim_env
 unfold add_func
 simp
 unfold suf_update
 simp
 unfold exp_suf_update
 simp
 unfold var_suf_set
 simp
 unfold subst_lst_gen subst_lst_gen subst_lst_gen
 simp
 /- running the code -/
 unfold update_senv_star update_senv_star update_senv_star update_senv_star
 unfold update_senv
 unfold eval_stmts update_senv eval_texp
 simp
 unfold eval_stmts eval_stmts eval_stmts 
 unfold eval_stmts eval_stmts eval_stmts eval_stmts eval_stmts
 unfold update_senv
 unfold svar_eq
 simp
 simp
 unfold update_senv
 unfold jax_to_ATL
 simp
 unfold body_trans
/-
start from let bindings with calls to primitive functions on tensors
we can replace primitive function f's call to argument variables x_1 to x_n by
f's own definition, with its free variables replaced by x_1 to x_n
then we get a program whose areguments are also programs. do the simplifications
on let lifting etc, we get it in the desired form
thus Jax is syntactic sugar for a subset of ATL, and this subset of ATL can
then be transformed into SSA
The abstract machine takes a jax program as input, first do transformation,
then use ATL's semantics to evaluate. This syntactic sugar is part of the
language so it doesn't need proof. Although in principle we want to prove
the algorithms implemented this way and see if they are correct
-/

