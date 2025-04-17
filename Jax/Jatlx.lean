/-************** ATL Syntax in Single-Static-Assignment Form *******************-/
/- name, suffix for counting # calls, differentiation level, counter for use within autodiff -/
inductive stmt_var
| stmtV : String → Nat → Nat → Nat → stmt_var
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
inductive uniPrim
| neg

inductive ind_bound
| const : Nat → ind_bound
| var : stmt_var → Nat → ind_bound
| max : ind_bound → ind_bound → ind_bound
| add : ind_bound → ind_bound → ind_bound
| mult : ind_bound → ind_bound → ind_bound
| sub : ind_bound → ind_bound → ind_bound
| div : ind_bound → ind_bound → ind_bound

/- scalar expressions -/
inductive exp  
| const : Nat → exp
| binOp : 
  pred → stmt_var → binPrim →
  pred → stmt_var → exp
| uniOp : 
  pred → uniPrim → stmt_var → exp
| binTenSum : 
  List ind_bound → List ind_bound → List ind_bound →
  pred → stmt_var → stmt_var → exp
| uniTenSum :
  List ind_bound → List ind_bound →
  pred → stmt_var → exp

inductive tenVal
| val : List Nat → List Nat → tenVal

/- tensor expession -/
inductive unitTenExp  
| gen : List ind_bound → exp → unitTenExp
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


/-********************* ATL Semantics in Single-Static-Assignment Form ********************-/
/- given statement list and input environment, 
   return final environment after statements execute -/
/- Helper Functions for Updating Statement Variable Environment -/
def svar_env := stmt_var → tenVal
def empty_senv : svar_env :=
  fun _ => tenVal.val [] []
def svar_eq
  | stmt_var.stmtV str1 n1 n1' n1'', stmt_var.stmtV str2 n2 n2' n2'' =>
    Bool.and (str1 == str2)
      (Bool.and  (n1 == n2) (Bool.and (n1' == n2') (n1'' == n2'')))
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
theorem svar_eq_trans_true :
  ∀ var1 var2 var3,
    svar_eq var1 var2 = true →
    svar_eq var2 var3 = true →
    svar_eq var1 var3 = true := by
  intros var1 var2 var3 H1 H2
  cases var1
  case stmtV name1 n1 n1' n1'' =>
  cases var2
  case stmtV name2 n2 n2' n2'' =>
  cases var3
  case stmtV name3 n3 n3' n3'' =>
  unfold svar_eq at *
  simp at *
  cases H1 with
  | intro str12_eq n12_eq =>
  cases n12_eq with
  | intro n12_eq n12_eq' =>
  cases n12_eq' with
  | intro n12_eq' n12_eq'' =>
  cases H2 with
  | intro str23_eq n23_eq =>
  cases n23_eq with
  | intro n23_eq n23_eq' =>
  cases n23_eq' with
  | intro n23_eq' n23_eq'' =>
  subst_vars
  apply And.intro
  rfl
  apply And.intro
  rfl
  apply And.intro
  rfl
  rfl
theorem svar_eq_trans_false :
  ∀ var1 var2 var3,
    svar_eq var1 var2 = false →
    svar_eq var2 var3 = true →
    svar_eq var1 var3 = false := by
  intros var1 var2 var3 H1 H2
  cases var1
  case stmtV name1 n1 n1' n1'' =>
  cases var2
  case stmtV name2 n2 n2' n2'' =>
  cases var3
  case stmtV name3 n3 n3' n3'' =>
  unfold svar_eq at *
  simp at *
  intro H_names H13 H13'
  cases H2 with
  | intro str23_eq n23_eq =>
  cases n23_eq with
  | intro n23_eq n23_eq' =>
  cases n23_eq' with
  | intro n23_eq' n23_eq'' =>
  subst_vars
  apply H1 <;> rfl

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
notation (name := env_update) para:arg "!->i" arg:arg ";" env:arg =>
  (update_ienv env para arg)
notation (name := env_updates) paras:arg "!->i*" args:arg ";" env:arg =>
  (update_ienv_star env paras args)

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

def eval_bound {X} (get_shape : (svar → X) → stmt_var → List Nat) env
  | ind_bound.const n => n
  | ind_bound.var name ind =>
    (get_shape env name).getD ind 0 
  | ind_bound.max arg1 arg2 =>
    let n1 := eval_bound get_shape env arg1
    let n2 := eval_bound get_shape env arg2
    max n1 n2
  | ind_bound.add arg1 arg2 =>
    let n1 := eval_bound get_shape env arg1
    let n2 := eval_bound get_shape env arg2
    n1 + n2
  | ind_bound.mult arg1 arg2 =>
    let n1 := eval_bound get_shape env arg1
    let n2 := eval_bound get_shape env arg2
    n1 * n2
  | ind_bound.sub arg1 arg2 =>
    let n1 := eval_bound get_shape env arg1
    let n2 := eval_bound get_shape env arg2
    n1 - n2
  | ind_bound.div arg1 arg2 =>
    let n1 := eval_bound get_shape env arg1
    let n2 := eval_bound get_shape env arg2
    n1 / n2
def get_shape_tm (senv : svar_env) var :=
  match senv var with
  | tenVal.val shape _ => shape

def eval_shape {X} (get_shape : (svar → X) → stmt_var → List Nat) env
  | [] => []
  | some_bound :: rst_shape => 
    (eval_bound get_shape env some_bound) 
    :: (eval_shape get_shape env rst_shape)

def eval_shape_tm env shape := eval_shape get_shape_tm env shape

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
  | exp.binTenSum ind_lst0 ind_lst1 ind_lst_s p var0 var1 =>
    let n0 := eval_shape_tm senv ind_lst0
    let n1 := eval_shape_tm senv ind_lst1
    let ns := eval_shape_tm senv ind_lst_s
    let ind_acc0 := List.map ind_var.sums (iota (List.length n0))
    let ind_acc1 := List.map ind_var.sum1 (iota (List.length n1))
    sum_2tens n0 n1 ns p var0 ind_acc0 var1 ind_acc1 senv ienv
  | exp.uniTenSum ind_lst ind_lst_s p var =>
    let n := eval_shape_tm senv ind_lst
    let ns := eval_shape_tm senv ind_lst_s
    let ind_acc := List.map ind_var.sums (iota (List.length n))
    sum_1tens n ns p var ind_acc senv ienv
    
/- Evaluating Tensor Expressions -/
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

def eval_ATL_body init_env
  | tenExp.letList stmts out =>
    (eval_stmts init_env stmts, out)
def eval_ATL args
  | tenFunc.func inp_vars expr =>
    match eval_ATL_body (inp_vars !->s* args ; empty_senv) expr with
    | (final_env, out) => final_env out

/- ************ ATL Small Step Operational Semantics ************* -/
inductive step_stmt : svar_env × tenStmt →
                      svar_env × tenStmt → Prop where
| stp_stmt : ∀ env var exp val,
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
inductive step_fun_body_star : svar_env × tenExp →
                               svar_env × tenExp → Prop where
| no_stp : ∀ env tm, step_fun_body_star (env, tm) (env, tm)
| stps  : ∀ env tm env' tm' env'' tm'', 
  step_fun_body (env, tm) (env', tm') →
  step_fun_body_star (env', tm') (env'', tm'') →
  step_fun_body_star (env, tm) (env'', tm'')

/- ************* Proof that Small Step Correctly Simulates Denotational *************** -/

theorem small_sim_deno : ∀ env env' expr out,
  eval_ATL_body env expr = (env', out) →
  step_fun_body_star (env, expr) (env', tenExp.letList [] out) := by
  intros env env' expr out
  intro H
  cases expr with
  | letList stmts out' =>
  cases H
  revert env
  induction stmts with
  | nil => 
    intro env 
    apply step_fun_body_star.no_stp
  | cons head tail IH =>
  cases head with
  | skip =>
    intro env
    apply step_fun_body_star.stps
    apply step_fun_body.stp_letList
    . apply step_stmts.stp_skip
    . unfold eval_stmts; apply IH
  | stmt var exp =>
    intro env
    apply step_fun_body_star.stps
    apply step_fun_body.stp_letList
    . apply step_stmts.stp_stmts
      apply step_stmt.stp_stmt <;> rfl
    . apply step_fun_body_star.stps
      apply step_fun_body.stp_letList
      . apply step_stmts.stp_skip
      . unfold eval_stmts
        simp
        apply IH

theorem deno_sim_small : ∀ env env' expr out,
  step_fun_body_star (env, expr) (env', tenExp.letList [] out) →
  eval_ATL_body env expr = (env', out) := by
  intros env env' expr out
  intro H
  unfold eval_ATL_body
  cases expr with
  | letList stmts out' =>
  simp
  apply And.intro
  case right =>
    revert env
    induction stmts with
    | nil => 
      intro env H
      cases H
      . rfl
      case stps env' tm' H_one_stp H_stps =>
        cases H_one_stp
        case stp_letList stmts H_stmts =>
        cases H_stmts
    | cons head tail IH =>
      intro env H
      cases H
      case stps env_mid tm' H_one_stp H_stps =>
      cases H_one_stp
      case stp_letList stmts H_stmts =>
      cases H_stmts
      . have IH' := IH env H_stps
        apply IH'
      case stp_stmts new_stmt H_stmt =>
        cases H_stmt
        case stp_stmt env var exp val =>
        subst_vars
        cases H_stps
        case stps env_mid tm' H_one_stp H_stps =>
        cases H_one_stp
        case stp_letList stmts H_stmts =>
        cases H_stmts 
        . apply IH
          apply H_stps
        case stp_stmts new_stmt H_stmt =>
        cases H_stmt
  case left =>
    revert env
    induction stmts with
    | nil => 
      intro env H
      cases H
      . rfl
      case stps env' tm' H_one_stp H_stps =>
        cases H_one_stp
        case stp_letList stmts H_stmts =>
        cases H_stmts
    | cons head tail IH =>
      intro env H
      cases H
      case stps env_mid tm' H_one_stp H_stps =>
      cases H_one_stp
      case stp_letList stmts H_stmts =>
      cases H_stmts
      . have IH' := IH env H_stps
        apply IH'
      case stp_stmts new_stmt H_stmt =>
        cases H_stmt
        case stp_stmt env var exp val =>
        subst_vars
        cases H_stps
        case stps env_mid tm' H_one_stp H_stps =>
        cases H_one_stp
        case stp_letList stmts H_stmts =>
        cases H_stmts 
        . apply IH
          apply H_stps
        case stp_stmts new_stmt H_stmt =>
        cases H_stmt

theorem small_deno_agree : ∀ env env' expr out,
  step_fun_body_star (env, expr) (env', tenExp.letList [] out) iff
  eval_ATL_body env expr = (env', out) := by
/- ************* ATL Type System & Soundness Proof *************** -/
/- ************* Type Syntax *************** -/
inductive ty_unitTenExp  
| gen : List ind_bound → ty_unitTenExp
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

theorem lift_env_same_shape : ∀ env x,
  (env x).1 = (lift_senv env x).1 := by
  intros env x
  unfold lift_senv
  simp
theorem eval_shape_lift_eq : ∀ env shape,
  eval_shape_tm env shape = eval_shape_ty (lift_senv env) shape := by
  intros env shape
  induction shape with
  | nil => rfl
  | cons head tail IH =>
    unfold eval_shape_tm eval_shape_ty
    unfold eval_shape get_shape_tm get_shape_ty
    simp
    induction head with
    | const n => 
      apply And.intro
      . unfold eval_bound ; rfl
      . apply IH      
    | var name suffix =>
      apply And.intro
      . unfold eval_bound; rfl
      . apply IH
    | max arg1 arg2 IH1 IH2 =>
      cases IH1 with
      | intro IH1 IH_tail =>
      cases IH2 with
      | intro IH2 IH_tail =>
      apply And.intro
      . unfold eval_bound
        rewrite [IH1]
        rewrite [IH2]
        rfl
      . apply IH_tail
    | add arg1 arg2 IH1 IH2 =>
      cases IH1 with
      | intro IH1 IH_tail =>
      cases IH2 with
      | intro IH2 IH_tail =>
      apply And.intro
      . unfold eval_bound
        rewrite [IH1]
        rewrite [IH2]
        rfl
      . apply IH_tail
    | mult arg1 arg2 IH1 IH2 =>
      cases IH1 with
      | intro IH1 IH_tail =>
      cases IH2 with
      | intro IH2 IH_tail =>
      apply And.intro
      . unfold eval_bound
        rewrite [IH1]
        rewrite [IH2]
        rfl
      . apply IH_tail
    | sub arg1 arg2 IH1 IH2 =>
      cases IH1 with
      | intro IH1 IH_tail =>
      cases IH2 with
      | intro IH2 IH_tail =>
      apply And.intro
      . unfold eval_bound
        rewrite [IH1]
        rewrite [IH2]
        rfl
      . apply IH_tail
    | div arg1 arg2 IH1 IH2 =>
      cases IH1 with
      | intro IH1 IH_tail =>
      cases IH2 with
      | intro IH2 IH_tail =>
      apply And.intro
      . unfold eval_bound
        rewrite [IH1]
        rewrite [IH2]
        rfl
      . apply IH_tail

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
  ty_step_fun_body (env, ty) (env', ty') →
  ty_step_fun_body_star (env', ty') (env'', ty'') →
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
| skip : has_ty_tenStmt tenStmt.skip ty_tenStmt.skip
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

inductive is_terminal : tenExp → Prop where
| is_term : ∀ tm out,
  tm = tenExp.letList [] out →
  is_terminal tm

inductive ty_is_terminal : ty_tenExp → Prop where
| is_term : ∀ ty out,
  ty = ty_tenExp.letList [] out →
  ty_is_terminal ty

def unstuck tm env :=
  is_terminal tm ∨
  ∃ env' tm', step_fun_body (env, tm) (env', tm')
def ty_eq env1 ty1 env2 ty2 :=
  ty_step_fun_body_star (env1, ty1) (env2, ty2) ∨
  ty_step_fun_body_star (env2, ty2) (env1, ty1)

theorem ty_step_fun_body_star_concat : ∀ env ty env' ty' env'' ty'',
  ty_step_fun_body_star (env, ty) (env', ty') →
  ty_step_fun_body_star (env', ty') (env'', ty'') →
  ty_step_fun_body_star (env, ty) (env'', ty'') := by
  intros env ty env' ty' env'' ty'' H_steps1 H_steps2
  generalize H1 : (env, ty) = pair1
  generalize H2 : (env', ty') = pair2
  rw [H1, H2] at H_steps1
  revert ty ty ty' env env' env'' ty''
  induction H_steps1 with
  | no_stp env ty =>
    intros env1 ty1 env' ty' env'' ty'' H_steps2 H1 H2
    cases H1
    cases H2
    apply H_steps2
  | stps env ty env' ty' env'' ty'' H_stp_one H_stps_star IH =>
    intros env1 ty1 env''1 ty''1 env''' ty''' H_steps2 H1 H2
    cases H1
    cases H2
    have IH' := IH env' ty' env'' ty'' env''' ty''' H_steps2 rfl rfl
    apply ty_step_fun_body_star.stps
    . apply H_stp_one
    . apply IH'

/- ************* Type Soundness *************** -/

theorem progress : ∀ tm env ty,
  has_ty_tenExp tm ty → unstuck tm env := by
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

theorem preservation_strong : ∀ tm env tm' env' ty,
  has_ty_tenExp tm ty →
  step_fun_body (env, tm) (env', tm') →
  ∃ ty', 
    has_ty_tenExp tm' ty' ∧
    ty_step_fun_body_star (lift_senv env, ty) (lift_senv env', ty') := by
  intros tm env tm' env' ty H_ty H_step
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
      cases H_stmts_ty with
      | intro left right =>
      apply And.intro
      . apply has_ty_tenExp.letList <;> try rfl
        apply H_var_eq
        apply right
      . apply ty_step_fun_body_star.stps
        . cases left
          . apply ty_step_fun_body.stp_letList
            apply ty_step_stmts.stp_skip
          . contradiction
        . apply ty_step_fun_body_star.no_stp
  | stp_stmts env env' stmt new_stmt some_stmts H_stp_stmt => 
    cases H_ty with
    | letList letList_tm letList_ty out_tm out_ty
              H_tm H_ty H_var_eq H_stmts_ty =>
      subst_vars
      cases H_tm
      cases letList_ty with
      | nil => contradiction
      | cons stmt_ty rst_stmts_ty =>
      cases H_stmts_ty with
      | intro left right =>
      cases H_stp_stmt with
      | stp_stmt env var exp val H_val H_env =>
      subst_vars
      exists (ty_tenExp.letList (ty_tenStmt.skip :: rst_stmts_ty) out_ty)
      apply And.intro
      . apply has_ty_tenExp.letList <;> try rfl
        apply H_var_eq
        unfold has_ty_stmtLst
        apply And.intro
        apply has_ty_tenStmt.skip
        apply right
      . apply ty_step_fun_body_star.stps <;> try (apply ty_step_fun_body_star.no_stp)
        cases left with
        | stmt stmt_tm stmt_ty var_tm var_ty exp_tm exp_ty
               H_tm H_ty H_var_eq' H_unitTen =>
          apply ty_step_fun_body.stp_letList
          apply ty_step_stmts.stp_stmts
          subst_vars
          apply ty_step_stmt.stp_stmt <;> try rfl
          unfold lift_senv update_senv
          funext x
          simp
          cases H_tm
          cases eqn : (svar_eq x var)
          . rewrite [svar_eq_trans_false]
            simp
            apply var
            apply eqn
            apply H_var_eq'
          . rewrite [svar_eq_trans_true] 
            . simp
              cases H_unitTen <;> subst_vars <;> unfold eval_texp <;> 
                unfold eval_ty_texp <;> simp
              case a.stmt.a.a.a.h.refl.true.gen shape e =>
                unfold gen_tensor
                simp
                apply eval_shape_lift_eq
            . apply var
            . apply eqn
            . apply H_var_eq'
        
theorem preservation : ∀ tm env tm' env' ty,
  has_ty_tenExp tm ty →
  step_fun_body (env, tm) (env', tm') →
  ∃ ty', 
    has_ty_tenExp tm' ty' ∧
    ty_eq (lift_senv env) ty (lift_senv env') ty' := by
  intros tm env tm' env' ty H_ty H_step
  have H := preservation_strong tm env tm' env' ty H_ty H_step
  cases H with
  | intro ty' H =>
  cases H with
  | intro left right =>
  exists ty'
  apply And.intro
  . apply left
  . unfold ty_eq
    apply Or.inl
    apply right

theorem type_safety_h : ∀ tm1 env1 tm2 env2 ty1,
  has_ty_tenExp tm1 ty1 →
  step_fun_body_star (env1, tm1) (env2, tm2) →
  ∃ ty2,
    has_ty_tenExp tm2 ty2 ∧
    ty_step_fun_body_star (lift_senv env1, ty1) (lift_senv env2, ty2) := by
  intros tm1 env1 tm2 env2 ty H_has_ty H_steps 
  generalize H1 : (env1, tm1) = pair1
  rw [H1] at H_steps
  generalize H2 : (env2, tm2) = pair2
  rw [H2] at H_steps
  revert ty tm1 tm2 env1 env2
  induction H_steps with
  | no_stp env tm =>
    intro tm1 env1 tm2 env2 ty H_has_ty H_p1 H_p2
    cases H_p1
    cases H_p2
    exists ty
    apply And.intro
    . apply H_has_ty
    . apply ty_step_fun_body_star.no_stp
  | stps env tm env' tm' env'' tm'' H_stp_one H_stps_star IH =>
    intro tm1 env1 tm2 env2 ty H_has_ty H_p1 H_p2
    cases H_p1
    cases H_p2
    
    have H_pres := preservation_strong tm env tm' env' ty H_has_ty H_stp_one
    cases H_pres with
    | intro ty1 H_pres =>
    cases H_pres with
    | intro H_pres1 H_pres2 =>
    have IH' := IH tm' env' tm'' env'' ty1 H_pres1 rfl rfl
    cases IH' with
    | intro ty2 IH =>
    cases IH with
    | intro IH1 IH2 =>
    exists ty2
    apply And.intro
    . apply IH1
    . apply ty_step_fun_body_star_concat
      apply H_pres2
      apply IH2 

theorem type_safety : ∀ tm1 env1 tm2 env2 ty,
  has_ty_tenExp tm1 ty →
  step_fun_body_star (env1, tm1) (env2, tm2) →
  unstuck tm2 env2 := by
  intros tm1 env1 tm2 env2 ty H_has_ty H_steps 
  have H := type_safety_h tm1 env1 tm2 env2 ty H_has_ty H_steps
  cases H with
  | intro ty2 H =>
  cases H with
  | intro left right =>
  apply progress
  apply left

/-************************ Forward Mode Autodiff on ATL ***********************-/
def var_diff
  | stmt_var.stmtV name suf diff_level diff_counter =>
    stmt_var.stmtV name suf (Nat.succ diff_level) diff_counter
def diff_temp_gen
  | stmt_var.stmtV name suf diff_level diff_counter =>
    stmt_var.stmtV name suf diff_level (Nat.succ diff_counter)
def forward_diff_exp target_var shape expr :=
  let stmt_wrapper_h the_var x := tenStmt.stmt (var_diff the_var)
                                               (unitTenExp.gen shape x)
  let stmt_wrapper x := stmt_wrapper_h target_var x
  let temp1 := diff_temp_gen target_var
  let temp2 := diff_temp_gen temp1
  match expr with
  | exp.const _ => [stmt_wrapper (exp.const 0)]
  | exp.binOp pred1 var1 binPrim.add pred2 var2 =>
    [stmt_wrapper (exp.binOp pred1 (var_diff var1) binPrim.add pred2 (var_diff var2))]
  | exp.binOp pred1 var1 binPrim.sub pred2 var2 =>
    [stmt_wrapper (exp.binOp pred1 (var_diff var1) binPrim.sub pred2 (var_diff var2))]
  | exp.binOp pred1 var1 binPrim.mult pred2 var2 =>
    stmt_wrapper_h temp1 (exp.binOp pred1 (var_diff var1) binPrim.mult pred2 var2) ::
    stmt_wrapper_h temp2 (exp.binOp pred1 var1 binPrim.mult pred2 (var_diff var2)) ::
    [stmt_wrapper (exp.binOp pred1 temp1 binPrim.add pred2 temp2)]
  | exp.uniOp p uniPrim.neg var =>
    [stmt_wrapper (exp.uniOp p uniPrim.neg (var_diff var))]
  | exp.binTenSum bound_lst1 bound_lst2 bound_lst_s
                  p var1 var2 =>
    stmt_wrapper_h temp1 
      (exp.binTenSum bound_lst1 bound_lst2 bound_lst_s p (var_diff var1) var2) ::
    stmt_wrapper_h temp2 
      (exp.binTenSum bound_lst1 bound_lst2 bound_lst_s p var1 (var_diff var2)) ::
    [stmt_wrapper (exp.binOp pred.true temp1 binPrim.add pred.true temp2)]
  | exp.uniTenSum bound_lst1 bound_lst2 p var =>
    [stmt_wrapper (exp.uniTenSum bound_lst1 bound_lst2 p (var_diff var))]
       
def forward_diff_tenExp target_var
  | unitTenExp.var var => 
    [tenStmt.stmt (var_diff target_var) (unitTenExp.var (var_diff var))]
  | unitTenExp.val (tenVal.val shape content) =>
    [tenStmt.stmt (var_diff target_var) 
      (unitTenExp.val (tenVal.val shape (List.map (fun _ => 0) content)))]
  | unitTenExp.gen shape exp =>
    forward_diff_exp target_var shape exp
/- solve the issue by using return type list -/
def forward_diff_stmt_lst env
  | [] => []
  | tenStmt.skip :: rst => forward_diff_stmt_lst env rst
  | tenStmt.stmt var exp :: rst =>
    let new_env := var !->s (var_diff var) ; env
    tenStmt.stmt var exp ::
    forward_diff_tenExp var exp ++
    forward_diff_stmt_lst new_env rst
def forward_diff
  | tenFunc.func inp_vars (tenExp.letList stmts out) =>
    let empty_var_env := fun _ => stmt_var.stmtV "" 0 0 0
    tenFunc.func inp_vars (tenExp.letList (forward_diff_stmt_lst empty_var_env stmts) out)
def forward_many_diff expr
  | 0 => expr
  | Nat.succ n => forward_many_diff (forward_diff expr) n

/-******************** Jaxpr and Lowering it to ATL ********************-/
inductive jStmt
| stmt : stmt_var → String → Nat → List stmt_var → jStmt
| skip
inductive jaxpr_body 
| letList : List jStmt → stmt_var → jaxpr_body
inductive jaxpr  
| func : List stmt_var → jaxpr_body → jaxpr

/- *********** Jax Type System ****************** -/

inductive ty_jStmt
| stmt : stmt_var → String → Nat → List stmt_var → ty_jStmt
| skip

inductive ty_jaxpr_body 
| letList : List ty_jStmt → stmt_var → ty_jaxpr_body

inductive ty_jaxpr  
| func : List stmt_var → ty_jaxpr_body → ty_jaxpr

inductive has_ty_jStmt : jStmt → ty_jStmt → Prop where
| stmt : ∀ stmt_tm stmt_ty var_tm var_ty 
           prim_tm prim_ty args_tm args_ty diff_tm diff_ty,
  stmt_tm = jStmt.stmt var_tm prim_tm diff_tm args_tm →
  stmt_ty = ty_jStmt.stmt var_ty prim_ty diff_ty args_ty →
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


/- ***** lowering to ATL ***** -/
def var_suf_incr stVar suf :=
  match stVar with
  | stmt_var.stmtV var original_suf diff count => 
    stmt_var.stmtV var (suf + original_suf) diff count

def subst_lst_gen paras args (suf : Nat) :=
  match paras, args with
  | [], _ => []
  | _, [] => []
  | var :: rstparas, 
    arg :: rstargs =>
    (tenStmt.stmt (var_suf_incr var suf) (unitTenExp.var arg)) :: 
    subst_lst_gen rstparas rstargs suf

def exp_suf_update (suf : Nat) : exp → exp
  | exp.const c => exp.const c
  | exp.binOp p1 var1 op
               p2 var2 =>
    exp.binOp p1 (var_suf_incr var1 suf) op
               p2 (var_suf_incr var2 suf)
  | exp.uniOp p f var =>
    exp.uniOp p f (var_suf_incr var suf)
  | exp.binTenSum indLst1 indLst2 indLst3
                   p var1 var2 =>
    exp.binTenSum indLst1 indLst2 indLst3 p
                   (var_suf_incr var1 suf) (var_suf_incr var2 suf)
  | exp.uniTenSum indLst1 indLst2 p var =>
    exp.uniTenSum indLst1 indLst2 p (var_suf_incr var suf)
def suf_update suf 
  | tenStmt.stmt varLHS (unitTenExp.var varRHS) =>
    tenStmt.stmt (var_suf_incr varLHS suf) (unitTenExp.var (var_suf_incr varRHS suf))
  | tenStmt.stmt svar (unitTenExp.gen indList e) =>
    tenStmt.stmt (var_suf_incr svar suf) (unitTenExp.gen indList (exp_suf_update suf e))
  | tenStmt.stmt svar (unitTenExp.val val) =>
    tenStmt.stmt svar (unitTenExp.val val)
  | tenStmt.skip => tenStmt.skip
def inline_one_prim target_var arg_vars var_suf
  | tenFunc.func inp_vars (tenExp.letList fstmts out) =>
      subst_lst_gen inp_vars arg_vars var_suf ++
      (List.map (suf_update var_suf) fstmts) ++
      [tenStmt.stmt target_var (unitTenExp.var (var_suf_incr out var_suf))]
def inline_prims stmts (env : String → tenFunc) (var_suf : Nat) :=
  match stmts with
  | [] => []
  | jStmt.stmt target_var prim_name diff_level arg_vars :: rst =>
    let diffed_prog := forward_many_diff (env prim_name) diff_level
    (inline_one_prim target_var arg_vars var_suf diffed_prog) ++ 
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

def eval_prog prog args fenv :=
  match jax_to_ATL prog fenv with
  | tenFunc.func inp_vars (tenExp.letList stmts out) =>
    (eval_stmts (inp_vars !->s* args ; empty_senv) stmts) out

/- ********************* Library Functions **************************** -/
inductive exp  
| binTenSum : 
  List Nat → List Nat → List Nat →
  pred → stmt_var → stmt_var → exp
| uniTenSum :
  List Nat → List Nat →
  pred → stmt_var → exp

notation "c:" c:60 => exp.const c

notation "〚" pred1:70 "〛" var1:70 "+" "〚" pred2:70 "〛" var2:70 =>
  (exp.binOp pred1 (stmt_var.stmtV var1 0) binPrim.add pred2 (stmt_var.stmtV var2 0))
notation "〚" pred1:70 "〛" var1:70 "-" "〚" pred2:70 "〛" var2:70 =>
  (exp.binOp pred1 (stmt_var.stmtV var1 0) binPrim.sub pred2 (stmt_var.stmtV var2 0))
notation "〚" pred1:70 "〛" var1:70 "*" "〚" pred2:70 "〛" var2:70 =>
  (exp.binOp pred1 (stmt_var.stmtV var1 0) binPrim.mult pred2 (stmt_var.stmtV var2 0))
notation "〚" pred1:70 "〛" var1:70 "/" "〚" pred2:70 "〛" var2:70 =>
  (exp.binOp pred1 (stmt_var.stmtV var1 0) binPrim.div pred2 (stmt_var.stmtV var2 0))

notation "uni:" "〚" pred:70 "〛" "-" var:70 =>
  (exp.uniOp pred uniPrim.neg var)

notation name:60 "←" ind_lst:60 "⊞" exp:60 ";" stmt_lst:60 =>
  (tenStmt.stmt (stmt_var.stmtV name 0) (unitTenExp.gen ind_lst exp))
  :: stmt_lst

notation var1:60 "←" var2:60 ";" stmt_lst:60 =>
  (tenStmt.stmt (stmt_var.stmtV var1 0) (unitTenExp.var (stmt_var.stmtV var2 0)))
  :: stmt_lst

notation name:60 "←" ind_lst:60 exp:60 =>
  name ← ind_lst ⊞ exp ; []

notation var1:60 "←" var2:60 =>
  var1 ← var2 ; []

notation "inp_vars:" inp_var_lst:70 "body:" body_stmts:70 "return:" out:70 =>
  tenFunc.func
    (List.map (fun x => stmt_var.stmtV x 0) inp_var_lst)
    (tenExp.letList body_stmts (stmt_var.stmtV out 0))

def forty_two :=
  inp_vars: ["x", "y"]
  body: "x" ← [] ⊞ c: 42 ;
        "out" ← "x"
  return: "out"

def tensor_add :=
  inp_vars: ["x", "y"]
  body: "x" ← [] ⊞ 〚pred.true〛 "x" + 〚pred.true〛 "y" ;
        "out" ← "x"
  return: "out"
/- ********************* Example **************************** -/

notation name:60 "←" func_name:60 ":" var_lst:60 ";" stmt_lst:61 =>
  (jStmt.stmt 
    (stmt_var.stmtV name 0) 
    func_name
    (List.map (fun x => stmt_var.stmtV x 0) var_lst))
  :: stmt_lst
notation name:60 "←" func_name:60 ":" var_lst:60 =>
  name ← func_name : var_lst ; []

notation "jaxpr:" inp_var_lst:70 "body:" body_stmts:70 "return:" out:70 =>
  jaxpr.func
    (List.map (fun x => stmt_var.stmtV x 0) inp_var_lst)
    (jaxpr_body.letList body_stmts (stmt_var.stmtV out 0))


def simple_prog :=
  jaxpr: ["x", "y", "z"]
  body:
    "a" ← "add" : ["x", "y"] ;
    "b" ← "add" : ["a", "z"]
  return: "b"
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
 unfold var_suf_incr
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

