/- Abstract Syntax 

def k := Nat
def ind := Nat
inductive ind_exp :=
| Ivar : var → ind_exp
| Inat : ind → ind_exp
| IAdd : ind_exp → ind_exp → ind_exp
| IMult : ind_exp → ind_exp → ind_exp
| ISub : ind_exp → ind_exp → ind_exp
| IDiv : ind_exp → ind_exp → ind_exp
| ICeilDiv : ind_exp → ind_exp → ind_exp
| IMod : ind_exp → ind_exp → ind_exp
inductive bool_exp := 
| PTrue
| PFalse
| PEq : ind_exp → ind_exp → bool_exp
| PLeq : ind_exp → ind_exp → bool_exp
| PLe : ind_exp → ind_exp → bool_exp
| PAnd : bool_exp → bool_exp → bool_exp
inductive scalar_exp :=
| Sreal : real → scalar_exp
| SVar : var → scalar_exp
| SAdd : scalar_exp → scalar_exp → scalar_exp
| SMult : scalar_exp → scalar_exp → scalar_exp
| SSub : scalar_exp → scalar_exp → scalar_exp
| SDiv : scalar_exp → scalar_exp → scalar_exp
| SAccess : var → List ind_exp → scalar_exp

/- need to ensure folding list of nat gives length of list of real
   i.e. correct shape -/
inductive exp :=
| EArray : List Nat → List real → exp
| EGuard : bool_exp → exp → exp

-/

/--------------------------------------------------------------------/
def var := String
def real := Nat

inductive atom :=
| Avar : var → atom
| Aconst : real → atom


/- applying a primitive expression on atomic arguments and named parameters,
   can give a list of output, bound to a list of variables -/   
mutual
inductive jaxpr := 
| jaxpr_prog : 
  List (var * array) →
  List var → 
  jaxpr_run →
  List atom → jaxpr
inductive prim_expr :=
| arith 
| bool
| objects
| cond : List jaxpr → prim_expr
| while jaxpr → jaxpr → prim_expr 
| scan
/- a runtime representation of a jaxpr being evaluated -/
/- var1, var2, ..., varn = prim(var1=atm1,atm2...,varn=atmn, atm,...,atm) -/
inductive jaxpr_run :=
| jpr_run :
  List (List var * prim_expr * List (var * List atom) * List atom) → jaxpr_run

inductive cont :=
| jpr_cont : jaxpr_run → List vars → cont

def env := var → expr

/-------------------------------------------------------------------/
/--------------------- Operational Semantics -----------------------/
/-------------------------------------------------------------------/

/- Definitions of first order primitives -/

/- applying a first order primitive -/

/- environment update-/

/- each step just do one assignment, until everything done
   need to handle higher order primitives like while loops etc  -/
inductive step (prog : jaxpr) (args : List atom) : 
  (jaxpr_run * env * cont) → (jaxpr_run * env * cont) :=
| ∀ rst E K, 
    func ≠ while → func ≠ cond → func ≠ scan →
    func_app func params args = out_lst →
    step 
      (jpr_run ((vars,func,params,args) :: rst), E, K)
      (jpr_run rst, update vars out_lst E, K)
| ∀ rst E K,
    step
      (jpr_run ((vars,cond,params,args) :: rst), E, K)
      (jpr_run rst, E, K)
| ∀ rst E K,
    step
      (jpr_run ((vars,while,params,args) :: rst), E, K)
      (jpr_run rst, E, K)
| ∀ rst E K,
    step
      (jpr_run ((vars,scan,params,args) :: rst), E)
      (jpr_run rst, E, K)      


/- types -/
inductive ty :=
| real_ty
inductive arr_ty :=
| float_arr_ty


def init (prog : jaxpr) := 
  match prog with
  | prog → prog
/- end is when list of equations become zero -/
