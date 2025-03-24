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
/------------------------- Syntax of Core ATL -----------------------------------/

/-
inductive scalar_exp :=
| Sconst :  real -> scalar_exp
| SVar : var -> scalar_exp
| SAdd : scalar_exp -> scalar_exp -> scalar_exp
| SMult : scalar_exp -> scalar_exp -> scalar_exp
| SSub : scalar_exp -> scalar_exp -> scalar_exp
| SDiv : scalar_exp -> scalar_exp -> scalar_exp
| SPrimFun : List scalar_exp -> scalar_exp
| SAccess : var -> List ind_exp -> scalar_exp
inductive atl_exp :=
| EScalar : scalar_exp -> atl_exp
| ESum : var -> ind_exp -> ind_exp -> atl_exp -> atl_exp
| EGen : var -> ind_exp -> ind_exp -> atl_exp -> atl_exp
| EGuard : pred -> atl_exp -> atl_exp
| ELet : var -> atl_exp -> atl_exp -> atl_exp-/
/----------------ATL Syntax in Single-Static-Assignment Form---------------------/
def real := Nat
inductive stmt_var := stmtV : var → Nat → stmt_var
/- since ATL is in normal form, index variables can be standardized into only 4 possible cases -/
inductive ind_var := 
| genIV : Nat → ind_var
| sumIV : Nat → ind_var
| sumIV1 : Nat → ind_var
| sumIV2 : Nat → ind_var

inductive ind_exp :=
| IVar : ind_var → ind_exp
| IConst : real → ind_exp
| IAdd : ind_exp → ind_exp → ind_exp
| IMult : ind_exp → ind_exp → ind_exp 
| ISub : ind_exp → ind_exp → ind_exp
| IDiv : ind_exp → ind_exp → ind_exp 
| ICeilDiv : ind_exp → ind_exp → ind_exp
| IMod : ind_exp → ind_exp → ind_exp 
inductive pred :=
| PTrue
| PFalse
| PEq : ind_exp → ind_exp → pred
| PLeq : ind_exp → ind_exp → pred
| PLe : ind_exp → ind_exp → predicatae
| PAnd : pred → pred → pred


inductive stmt_var_acc :
| stmtVA : stmt_var → List ind_var → stmt_var_acc

/- scalar expressions -/
inductive exp := 
| EConst : real → exp
| EBinOp : 
  pred → stmt_var_acc → binPrim
  pred → stmt_var_acc → exp
| EUniOp : 
  pred → uniPrim → stmt_var_acc → exp
| EBinTensorSum : 
  List Nat → List Nat → List ind_var →
  pred → stmt_var_acc → stmt_var_acc → exp
| EUniTensorSum :
  List ind_var → List ind_var →
  pred → stmt_var_acc → exp
/- tensor expession -/
inductive genTenExp :=
| GScalar : exp → genTenExp
| Gen : Nat → genTenExp → genTenExp /- shape and expression for each entry -/
inductive unitTenExp := 
| TGen : genTenExp → unitTenExp
| TVar : stmt_var → unitTenExp
inductive tenExp
| TLetList : List (stmt_var * unitTenExp) * stmt_var → tenExp
/- functions taking tensors as input and returns a tensor, SSA without structs -/
/- list of input vars (vars that don't occur in lhs before they occur in rhs) 
   and list of statements -/
inductive tenFunc :=
| TFunc : List stmt_var -> tenExp -> tenFunc

/---------------- Jaxpr and Lowering it to ATL ---------------------/
inductive jaxpr_body :=
| JLetList : List (stmt_var * var * List stmt_var) * stmt_var → jaxpr_body
inductive jaxpr := 
| JFunc : List stmt_var → jaxpr_body -> jaxpr

def subst_lst_gen paras args suf :=
  match paras, args with
  | [], _ → []
  | _, [] → []
  | (stmtV para sufp) :: rstparas, 
    arg :: rstargs →
    ((stmtV para suf), TVar arg) :: 
    subst_lst_gen rstparas rstargs suf
def var_suf_set stVar suf :=
  match stVar with
  | stmtV var suf' → stmtV var suf
def suf_update suf stmt :=
  match stmt with
  | (varLHS, TVar varRHS) →
    ((var_suf_set varLHS suf), TVar (var_suf_set varRHS suf))
  | (svar, gen indList e) →
    match e with
    | EConst c → e
    | EBinOp p1 (stmtVA var1 accLst1) op
            p2 (stmtVA var2 accLst2) →
      EBinOp p1 (stmtVA (var_suf_set var1 suf) accLst1) op
            p2 (stmtVA (var_suf_set var2 suf) accLst2) 
    | EUniOp p f (stmtVA var accLst) →
      EUniOp p f (stmtVA (var_suf_set var suf) accLst)
    | EBinTensorSum indLst1 indLst2 indLst3 p
                   (stmtVA var1 accLst1)
                   (stmtVA var2 accLst2) →
      EBinTensorSum indLst1 indLst2 indLst3 p
                   (stmtVA (var_suf_set var1 suf) accLst1)
                   (stmtVA (var_suf_set var2 suf) accLst2)
    | EUniTensorSum indLst1 indLst2 p
                   (stmtVA var1 accLst1) →
      EUniTensorSum indLst1 indLst2 p
                   (stmtVA (var_suf_set var1 suf) accLst1)
def inline_prims stmts env var_suf :=
  match stmts with
  | [] → []
  | (target_var, prim_name, arg_vars) :: rst →
    match env prim_name with
    | TFunc inp_vars (TLetList fstmts (stmtV outName outSuf)) →
      subst_lst_gen inp_vars arg_vars var_suf ++
      (map (suf_update var_suf) fstmts) ++
      (target_var, TVar (stmtV outName var_suf)) ::
        inline_prims rst env (1 + var_suf)
/- transform a jaxpr into an ATL, by inlining primitives from environment -/
def body_trans env body :=
  match body with
  | JLetList stmts out_var →
    FLetList (inline_prims stmts env 1) out_var
def jax_to_ATL p env :=
  match p with
  | JFunc inp_vars body → 
    func inp_vars (body_trans env body)

/----------------ATL Semantics in Single-Static-Assignment Form---------------------/
/- given statement list and input environment, 
   return final environment after statements execute -/
def empty_env := []
def update_env env para arg :=
  fun x → if x = para then arg else env x
def update_env_star env paras args :=
  match paras, args with
  | _, [] → env
  | [], _ → env
  | para :: paras', arg :: args' →
    update_env_star (update_env env para arg) paras' args'
/- https://www.leanprover.cn/mp-lean-zh/main/05_syntax.html -/
notation (name := env_update) para:arg "!->" arg:arg ";" env:arg =>
  (update_env env para arg)
notation (name := env_updates) paras:arg "!->*" args:arg ";" env:arg =>
  (update_env_star env paras args)

def gen_list_h ind_var length e env :=
  match length with
  | 0 → []
  | S n → 
    (gen_tensor e (ind_var !-> n ; env)) ::
    gen_list_h ind_var n e env
def gen_list ind_var length e env :=
  rev (gen_list_h ind_var length e env)
/- gen tensor is gen list applied many times-/
def gen_tensor_h e env cur_ind :=
  match e with
  | GScalar → eval_exp e env
  | Gen n e' →
    (gen_list cur_ind n 
      (gen_tensor rst_shape e env (1 + cur_ind)) env)
    
def gen_tensor e env := gen_tensor_h e env 0
def eval_texp e env := 
  match e with
  | TGen e' →
    gen_tensor e' env
  | TVar v →
    (env v)
def eval_stmts stmts env :=
  match stmts with
  | [] → env
  | (x, e) :: rst_stmts →
    let new_env = x !-> (eval_texp e env) ; env in
    eval_stmts rst_stmts new_env

List (stmt_var * unitTenExp) 
def eval_prog prog args fenv :=
  match jaxToATL prog fenv with
  | func inp_vars (letList stmts out) →
    eval_stmts stmts (updateEnv empty_env inp_vars args)
 
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

