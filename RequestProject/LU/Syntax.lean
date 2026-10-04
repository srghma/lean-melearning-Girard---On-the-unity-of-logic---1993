module

public import Mathlib

/-!
# The language of LU (Girard, *On the unity of logic*, 1993)

This file fixes the language of the unified sequent calculus **LU**
(§2 and §6 of the paper):

* atomic predicates come *with a polarity* `+1` (positive), `0` (neutral) or `-1` (negative);
* constants `1, 0` (both positive, also written `V` and `F`) and `⊥, ⊤` (both negative);
* unary connectives `(·)⊥` (linear negation, also written `¬`), `!`, `?`;
* binary connectives `∧, ∨, ⇒, ⊃, ⊗, ⅋, ⊸, ⊕, &`;
* quantifiers `∀x, ∃x` (classical / intuitionistic) and `⋀x, ⋁x` (linear).

Every formula receives a polarity (§2, Tables 1 and 2); the polarity function
`Formula.pol` below is a literal transcription of these tables.

Terms and formulas are *well-scoped by construction* (indexed by the number of free
variables in scope, with de Bruijn indices `Fin n`), and atoms and function applications
always have the number of arguments prescribed by the arity of their symbol: `Term 0` and
`Formula 0` are the closed terms and closed formulas.  The body of a quantifier over
`Formula n` is a `Formula (n + 1)` whose bound variable is the index `0`.
`A[t/x]` (substitution of the term `t` for the bound variable) is `Formula.inst A t`, and the
eigenvariable condition "`x` not free in the context" is expressed by weakening the context
into the larger scope (`Formula.shift`).
-/

@[expose] public section

namespace LU

/-! ## Polarities -/

/-- The three polarities of §2: positive (`+1`), neutral (`0`) and negative (`-1`). -/
inductive Pol where
  | pos
  | neu
  | neg
  deriving DecidableEq, Repr, Fintype

namespace Pol

/-- The polarity of `A⊥` in terms of the polarity of `A` (Table 1). -/
def dual : Pol → Pol
  | pos => neg
  | neu => neu
  | neg => pos

/-! ### Table 1: polarities of the linear connectives -/

/-- Polarity of `A ⊗ B` (Table 1). -/
def tensor : Pol → Pol → Pol
  | pos, pos => pos
  | _, _ => neu

/-- Polarity of `A ⅋ B` (Table 1). -/
def par : Pol → Pol → Pol
  | neg, neg => neg
  | _, _ => neu

/-- Polarity of `A ⊸ B` (Table 1). -/
def lolli : Pol → Pol → Pol
  | pos, neg => neg
  | _, _ => neu

/-- Polarity of `A & B` (Table 1). -/
def with_ : Pol → Pol → Pol
  | neg, neg => neg
  | _, _ => neu

/-- Polarity of `A ⊕ B` (Table 1). -/
def plus : Pol → Pol → Pol
  | pos, pos => pos
  | _, _ => neu

/-- Polarity of `⋀x A` (Table 1). -/
def lall : Pol → Pol
  | neg => neg
  | _ => neu

/-- Polarity of `⋁x A` (Table 1). -/
def lex : Pol → Pol
  | pos => pos
  | _ => neu

/-! ### Table 2: polarities of the classical and intuitionistic connectives -/

/-- Polarity of `A ∧ B` (Table 2). -/
def conj : Pol → Pol → Pol
  | pos, pos => pos
  | neu, pos => pos
  | neg, pos => pos
  | pos, neu => pos
  | neu, neu => neu
  | neg, neu => neu
  | pos, neg => pos
  | neu, neg => neu
  | neg, neg => neg

/-- Polarity of `A ∨ B` (Table 2). -/
def disj : Pol → Pol → Pol
  | pos, pos => pos
  | neu, pos => pos
  | neg, pos => neg
  | pos, neu => pos
  | neu, neu => pos
  | neg, neu => neg
  | pos, neg => neg
  | neu, neg => neg
  | neg, neg => neg

/-- Polarity of the classical implication `A ⇒ B` (Table 2). -/
def imp : Pol → Pol → Pol
  | pos, pos => neg
  | neu, pos => pos
  | neg, pos => pos
  | pos, neu => neg
  | neu, neu => pos
  | neg, neu => pos
  | pos, neg => neg
  | neu, neg => neg
  | neg, neg => neg

/-- Polarity of the intuitionistic implication `A ⊃ B` (Table 2). -/
def iimp : Pol → Pol → Pol
  | _, neg => neg
  | _, _ => neu

end Pol

/-! ## Terms and formulas

Terms and formulas are *well-scoped by construction*: `Term n` and `Formula n` only contain
free variables taken from `Fin n` (de Bruijn indices `0, …, n-1`), and every function or
predicate symbol is applied to exactly as many arguments as its arity.  In particular
`Term 0` is the type of closed terms and `Formula 0` the type of closed formulas.
The body of a quantifier over `Formula n` is a `Formula (n + 1)`, in which the bound variable
is the index `0`. -/

/-- A function symbol: a name and an arity. -/
structure Func where
  name : ℕ
  arity : ℕ
  deriving DecidableEq

/-- First-order terms whose free variables are among `Fin n` (de Bruijn indices).
A function symbol `f` is applied to exactly `f.arity` arguments. -/
inductive Term (n : ℕ) where
  /-- a variable in scope -/
  | var : Fin n → Term n
  /-- `f t₁ … tₖ` with `k = f.arity` -/
  | func (f : Func) : (Fin f.arity → Term n) → Term n

/-- A substitution from scope `n` to scope `m`: a term of scope `m` for each variable. -/
abbrev Subst (n m : ℕ) := Fin n → Term m

namespace Term

instance {n : ℕ} : Inhabited (Term n) := ⟨func ⟨0, 0⟩ Fin.elim0⟩

/-- Renaming of variables along `ρ : Fin n → Fin m`. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : Term n → Term m
  | var i => var (ρ i)
  | func f ts => func f (fun i => (ts i).rename ρ)

/-- Weakening: a term of scope `n` seen in scope `n + 1` (all variables lifted by one). -/
def shift {n : ℕ} (t : Term n) : Term (n + 1) := t.rename Fin.succ

/-- Simultaneous substitution of `σ i` for each variable `i`. -/
def subst {n m : ℕ} (σ : Subst n m) : Term n → Term m
  | var i => σ i
  | func f ts => func f (fun i => (ts i).subst σ)

@[simp] theorem rename_var {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    (var i).rename ρ = var (ρ i) := rfl

@[simp] theorem subst_var {n m : ℕ} (σ : Subst n m) (i : Fin n) : (var i).subst σ = σ i := rfl

@[simp] theorem shift_var {n : ℕ} (i : Fin n) : (var i).shift = var i.succ := rfl

theorem rename_rename {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    ∀ t : Term n, (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ)
  | var i => rfl
  | func f ts => by
    simp only [rename]; congr 1; funext i; exact rename_rename ρ ρ' (ts i)

theorem subst_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Subst m k) :
    ∀ t : Term n, (t.rename ρ).subst σ = t.subst (σ ∘ ρ)
  | var i => rfl
  | func f ts => by
    simp only [rename, subst]; congr 1; funext i; exact subst_rename ρ σ (ts i)

theorem rename_subst {n m k : ℕ} (σ : Subst n m) (ρ : Fin m → Fin k) :
    ∀ t : Term n, (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ)
  | var i => rfl
  | func f ts => by
    simp only [rename, subst]; congr 1; funext i; exact rename_subst σ ρ (ts i)

theorem subst_subst {n m k : ℕ} (σ : Subst n m) (τ : Subst m k) :
    ∀ t : Term n, (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
  | var i => rfl
  | func f ts => by
    simp only [subst]; congr 1; funext i; exact subst_subst σ τ (ts i)

@[simp] theorem subst_var_eq {n : ℕ} : ∀ t : Term n, t.subst var = t
  | var i => rfl
  | func f ts => by
    simp only [subst]; congr 1; funext i; exact subst_var_eq (ts i)

theorem rename_eq_subst {n m : ℕ} (ρ : Fin n → Fin m) :
    ∀ t : Term n, t.rename ρ = t.subst (fun i => var (ρ i))
  | var i => rfl
  | func f ts => by
    simp only [rename, subst]; congr 1; funext i; exact rename_eq_subst ρ (ts i)

@[simp] theorem shift_subst_cons {n m : ℕ} (σ : Subst n m) (s : Term m) (t : Term n) :
    t.shift.subst (Fin.cons s σ) = t.subst σ := by
  simp only [shift, subst_rename]; rfl

theorem shift_subst {n m : ℕ} (σ : Subst n m) (t : Term n) :
    (t.subst σ).shift = t.subst (fun i => (σ i).shift) := by
  simp only [shift, rename_subst]

end Term

namespace Subst

/-- The identity substitution. -/
abbrev id (n : ℕ) : Subst n n := Term.var

/-- Lifting a substitution under a binder: the bound variable `0` is kept, the other
variables are substituted and then weakened. -/
def lift {n m : ℕ} (σ : Subst n m) : Subst (n + 1) (m + 1) :=
  Fin.cons (Term.var 0) (fun i => (σ i).shift)

/-- The weakening substitution `i ↦ i + 1` (used for the eigenvariable condition). -/
def weaken (n : ℕ) : Subst n (n + 1) := fun i => Term.var i.succ

/-- `[t/0]`: substitute `t` for the variable `0` and lower the other variables. -/
def single {n : ℕ} (t : Term n) : Subst (n + 1) n := Fin.cons t Term.var

@[simp] theorem lift_zero {n m : ℕ} (σ : Subst n m) : lift σ 0 = Term.var 0 := rfl

@[simp] theorem lift_succ {n m : ℕ} (σ : Subst n m) (i : Fin n) :
    lift σ i.succ = (σ i).shift := rfl

@[simp] theorem single_zero {n : ℕ} (t : Term n) : single t 0 = t := rfl

@[simp] theorem single_succ {n : ℕ} (t : Term n) (i : Fin n) : single t i.succ = Term.var i :=
  rfl

@[simp] theorem weaken_apply {n : ℕ} (i : Fin n) : weaken n i = Term.var i.succ := rfl

@[simp] theorem lift_id {n : ℕ} : lift (Term.var : Subst n n) = Term.var := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

/-- Lifting commutes with composition of substitutions. -/
theorem lift_comp {n m k : ℕ} (σ : Subst n m) (τ : Subst m k) :
    (fun i => (lift σ i).subst (lift τ)) = lift (fun i => (σ i).subst τ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [lift_succ, Term.shift]
  rw [Term.subst_rename, Term.rename_subst]; rfl

end Subst

/-- A predicate symbol: a name, an arity and a polarity
("atomic predicates are given with their polarity", §6). -/
structure Pred where
  name : ℕ
  arity : ℕ
  pol : Pol
  deriving DecidableEq

/-- The formulas of LU (§6) whose free variables are among `Fin n`.
Quantifiers bind the variable `0` of a body in scope `n + 1`;
an atom `p t₁ … tₖ` has exactly `k = p.arity` arguments. -/
inductive Formula : ℕ → Type where
  /-- atomic formula `p t₁ … tₖ`, with `k = p.arity` -/
  | atom {n : ℕ} (p : Pred) (ts : Fin p.arity → Term n) : Formula n
  /-- the constant `1` (also denoted `V`) -/
  | one {n : ℕ} : Formula n
  /-- the constant `0` (also denoted `F`) -/
  | zero {n : ℕ} : Formula n
  /-- the constant `⊥` -/
  | bot {n : ℕ} : Formula n
  /-- the constant `⊤` -/
  | top {n : ℕ} : Formula n
  /-- linear negation `A⊥` (also denoted `¬A`) -/
  | neg {n : ℕ} : Formula n → Formula n
  /-- `!A` -/
  | bang {n : ℕ} : Formula n → Formula n
  /-- `?A` -/
  | quest {n : ℕ} : Formula n → Formula n
  /-- `A ⊗ B` -/
  | tensor {n : ℕ} : Formula n → Formula n → Formula n
  /-- `A ⅋ B` -/
  | par {n : ℕ} : Formula n → Formula n → Formula n
  /-- `A ⊸ B` -/
  | lolli {n : ℕ} : Formula n → Formula n → Formula n
  /-- `A & B` -/
  | with_ {n : ℕ} : Formula n → Formula n → Formula n
  /-- `A ⊕ B` -/
  | plus {n : ℕ} : Formula n → Formula n → Formula n
  /-- conjunction `A ∧ B` (classical and intuitionistic) -/
  | conj {n : ℕ} : Formula n → Formula n → Formula n
  /-- disjunction `A ∨ B` (classical and intuitionistic) -/
  | disj {n : ℕ} : Formula n → Formula n → Formula n
  /-- classical implication `A ⇒ B` -/
  | imp {n : ℕ} : Formula n → Formula n → Formula n
  /-- intuitionistic implication `A ⊃ B` -/
  | iimp {n : ℕ} : Formula n → Formula n → Formula n
  /-- linear universal quantifier `⋀x A` (the body binds the variable `0`) -/
  | lall {n : ℕ} : Formula (n + 1) → Formula n
  /-- linear existential quantifier `⋁x A` -/
  | lex {n : ℕ} : Formula (n + 1) → Formula n
  /-- classical universal quantifier `∀x A` -/
  | call {n : ℕ} : Formula (n + 1) → Formula n
  /-- existential quantifier `∃x A` (classical and intuitionistic) -/
  | cex {n : ℕ} : Formula (n + 1) → Formula n

/-- Closed formulas (no free variable). -/
abbrev ClosedFormula := Formula 0

namespace Formula

instance {n : ℕ} : Inhabited (Formula n) := ⟨one⟩

/-- Simultaneous substitution of terms for the free variables of a formula
(capture-avoiding by construction: the substitution is lifted under binders). -/
def subst {n m : ℕ} : Formula n → Subst n m → Formula m
  | atom p ts, σ => atom p (fun i => (ts i).subst σ)
  | one, _ => one
  | zero, _ => zero
  | bot, _ => bot
  | top, _ => top
  | neg A, σ => neg (A.subst σ)
  | bang A, σ => bang (A.subst σ)
  | quest A, σ => quest (A.subst σ)
  | tensor A B, σ => tensor (A.subst σ) (B.subst σ)
  | par A B, σ => par (A.subst σ) (B.subst σ)
  | lolli A B, σ => lolli (A.subst σ) (B.subst σ)
  | with_ A B, σ => with_ (A.subst σ) (B.subst σ)
  | plus A B, σ => plus (A.subst σ) (B.subst σ)
  | conj A B, σ => conj (A.subst σ) (B.subst σ)
  | disj A B, σ => disj (A.subst σ) (B.subst σ)
  | imp A B, σ => imp (A.subst σ) (B.subst σ)
  | iimp A B, σ => iimp (A.subst σ) (B.subst σ)
  | lall A, σ => lall (A.subst (Subst.lift σ))
  | lex A, σ => lex (A.subst (Subst.lift σ))
  | call A, σ => call (A.subst (Subst.lift σ))
  | cex A, σ => cex (A.subst (Subst.lift σ))

/-- Weakening: a formula of scope `n` seen in scope `n + 1` (used for the eigenvariable
condition: a formula of the context cannot mention the fresh variable `0`). -/
def shift {n : ℕ} (A : Formula n) : Formula (n + 1) := A.subst (Subst.weaken n)

/-- `A[t/x]`: instantiate the bound variable (index `0`) of a quantifier body. -/
def inst {n : ℕ} (A : Formula (n + 1)) (t : Term n) : Formula n := A.subst (Subst.single t)

theorem subst_subst {n m k : ℕ} (A : Formula n) (σ : Subst n m) (τ : Subst m k) :
    (A.subst σ).subst τ = A.subst (fun i => (σ i).subst τ) := by
  induction A generalizing m k with
  | atom p ts => simp only [subst, Term.subst_subst]
  | lall A ih => simp only [subst, ih, Subst.lift_comp]
  | lex A ih => simp only [subst, ih, Subst.lift_comp]
  | call A ih => simp only [subst, ih, Subst.lift_comp]
  | cex A ih => simp only [subst, ih, Subst.lift_comp]
  | _ => simp_all [subst]

@[simp] theorem subst_id {n : ℕ} (A : Formula n) : A.subst Term.var = A := by
  induction A with
  | atom p ts => simp [subst]
  | _ => simp_all [subst]

theorem subst_congr {n m : ℕ} (A : Formula n) {σ τ : Subst n m} (h : ∀ i, σ i = τ i) :
    A.subst σ = A.subst τ := by
  rw [funext h]

/-- Weakening commutes with substitution. -/
theorem shift_subst {n m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).shift = A.shift.subst (Subst.lift σ) := by
  simp only [shift, subst_subst]
  apply subst_congr
  intro i
  simp only [Subst.weaken_apply, Term.subst_var, Subst.lift_succ, Term.shift,
    Term.rename_eq_subst]
  rfl

/-- Instantiation commutes with substitution. -/
theorem inst_subst {n m : ℕ} (A : Formula (n + 1)) (t : Term n) (σ : Subst n m) :
    (A.inst t).subst σ = (A.subst (Subst.lift σ)).inst (t.subst σ) := by
  simp only [inst, subst_subst]
  apply subst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp [Subst.single, Subst.lift]

/-- Instantiating a weakened formula does nothing. -/
@[simp] theorem shift_inst {n : ℕ} (A : Formula n) (t : Term n) : A.shift.inst t = A := by
  simp only [shift, inst, subst_subst]
  exact subst_id A

/-- Instantiating with the fresh variable `0` a body lifted under a binder gives it back. -/
@[simp] theorem subst_lift_weaken_inst {n : ℕ} (A : Formula (n + 1)) :
    (A.subst (Subst.lift (Subst.weaken n))).inst (Term.var 0) = A := by
  simp only [inst, subst_subst]
  convert subst_id A using 2
  funext i
  refine Fin.cases rfl (fun j => rfl) i

/-- The polarity of a formula (§2, Tables 1 and 2). -/
def pol {n : ℕ} : Formula n → Pol
  | atom p _ => p.pol
  | one => .pos
  | zero => .pos
  | bot => .neg
  | top => .neg
  | neg A => A.pol.dual
  | bang _ => .pos
  | quest _ => .neg
  | tensor A B => Pol.tensor A.pol B.pol
  | par A B => Pol.par A.pol B.pol
  | lolli A B => Pol.lolli A.pol B.pol
  | with_ A B => Pol.with_ A.pol B.pol
  | plus A B => Pol.plus A.pol B.pol
  | conj A B => Pol.conj A.pol B.pol
  | disj A B => Pol.disj A.pol B.pol
  | imp A B => Pol.imp A.pol B.pol
  | iimp A B => Pol.iimp A.pol B.pol
  | lall A => Pol.lall A.pol
  | lex A => Pol.lex A.pol
  | call _ => .neg
  | cex _ => .pos

@[simp] theorem pol_subst {n m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).pol = A.pol := by
  induction A generalizing m <;> simp_all [subst, pol]

@[simp] theorem pol_shift {n : ℕ} (A : Formula n) : A.shift.pol = A.pol := pol_subst A _

@[simp] theorem pol_inst {n : ℕ} (A : Formula (n + 1)) (t : Term n) : (A.inst t).pol = A.pol :=
  pol_subst A _

end Formula

end LU
