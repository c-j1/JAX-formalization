/- Abstract Syntax -/
def var := String
def real := Nat
def k := Nat
def ind := Nat
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
| ELet : var -> atl_exp -> atl_exp -> atl_exp 
-/
inductive ind_exp :=
| Ivar : var -> ind_exp
| Inat : ind -> ind_exp
| SAdd : ind_exp -> ind_exp -> ind_exp
| SMult : ind_exp -> ind_exp -> ind_exp
| SSub : ind_exp -> ind_exp -> ind_exp
| SDiv : ind_exp -> ind_exp -> ind_exp
| SCeilDiv : ind_exp -> ind_exp -> ind_exp
| SMod : ind_exp -> ind_exp -> ind_exp
inductive pred := 
| PTrue
| PFalse
| PEq : ind_exp -> ind_exp -> pred
| PLeq : ind_exp -> ind_exp -> pred
| PLe : ind_exp -> ind_exp -> pred
| PAnd : pred -> pred -> pred
inductive scalar_exp :=
| Sreal : real -> scalar_exp
| SVar : var -> scalar_exp
| SAdd : scalar_exp -> scalar_exp -> scalar_exp
| SMult : scalar_exp -> scalar_exp -> scalar_exp
| SSub : scalar_exp -> scalar_exp -> scalar_exp
| SDiv : scalar_exp -> scalar_exp -> scalar_exp
| SAccess : var -> List ind_exp -> scalar_exp

inductive exp :=
| EScalar : scalar_exp -> exp
| EPadL : k -> exp -> exp
| EPadR : k -> exp -> exp
| ETrunkL : k -> exp -> exp
| ETrunkR : k -> exp -> exp
| ESplit : k -> exp -> exp
| EFlatten : exp -> exp
| ETranspose : exp -> exp
| ESum : var -> ind_exp -> ind_exp -> exp -> exp
| EGen : var -> ind_exp -> ind_exp -> exp -> exp
| EGuard : pred -> exp -> exp
| ELet : var -> exp -> exp -> exp
def env := var -> exp
def v := Nat
def machine := exp * v * env
/- Semantics -/
