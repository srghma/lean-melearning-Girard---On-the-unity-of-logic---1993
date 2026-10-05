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

The language is not fixed: the function symbols are taken from a signature `TS : TermSig`
and the predicate symbols, each with its arity and its polarity, from a signature
`PS : PredSig`.  Terms `Tm TS n` and `k`-tuples of terms `Tms TS n k` are two mutually
inductive types, so that a tuple is never a term: every term and every atom has a unique
representation.

Terms and formulas are *well-scoped by construction* (indexed by the number of free
variables in scope, with de Bruijn indices `Fin n`), and atoms and function applications
always have the number of arguments prescribed by the arity of their symbol: `Tm TS 0` and
`Formula PS TS 0` are the closed terms and closed formulas.  Formulas have decidable
equality as soon as the symbols of the signatures do (`[DecidableEq PS.Pred]`,
`[DecidableEq TS.Func]`).  The body of a quantifier over `Formula PS TS n` is a
`Formula PS TS (n + 1)` whose bound variable is the index `0`.
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

/-! ## Signatures -/

/-- A signature of function symbols: a type of symbols, each with an arity. -/
structure TermSig where
  /-- the function symbols -/
  Func : Type
  /-- the arity of each function symbol -/
  arity : Func → ℕ

/-- A signature of predicate symbols: a type of symbols, each with an arity and a polarity
("atomic predicates are given with their polarity", §2 and §6). -/
structure PredSig where
  /-- the predicate symbols -/
  Pred : Type
  /-- the arity of each predicate symbol -/
  arity : Pred → ℕ
  /-- the polarity of each predicate symbol -/
  predPol : Pred → Pol

/-! ## Terms and tuples of terms

Terms over a signature `TS` are *well-scoped by construction*: `Tm TS n` only contains free
variables taken from `Fin n` (de Bruijn indices `0, …, n-1`).  `Tms TS n k` is the type of
`k`-tuples of terms.  A function symbol `f` is applied to a tuple of exactly `TS.arity f`
terms.  Terms and tuples are two different (mutually inductive) types, so a tuple can never
be used where a term is expected: every term and every atom has a unique representation. -/

mutual
/-- First-order terms over `TS` whose free variables are among `Fin n`. -/
inductive Tm (TS : TermSig) (n : ℕ) : Type where
  /-- a variable in scope -/
  | var : Fin n → Tm TS n
  /-- `f(t₁, …, tₖ)` with `k = TS.arity f` -/
  | func (f : TS.Func) : Tms TS n (TS.arity f) → Tm TS n
/-- `k`-tuples `(t₁, …, tₖ)` of terms over `TS` whose free variables are among `Fin n`. -/
inductive Tms (TS : TermSig) (n : ℕ) : ℕ → Type where
  /-- the empty tuple -/
  | nil : Tms TS n 0
  /-- `(t, t₁, …, tₖ)` -/
  | cons {k : ℕ} : Tm TS n → Tms TS n k → Tms TS n (k + 1)
end

variable {TS : TermSig}

/-- A substitution from scope `n` to scope `m`: a term of scope `m` for each variable. -/
abbrev Subst (TS : TermSig) (n m : ℕ) := Fin n → Tm TS m

mutual
/-- Renaming of variables along `ρ : Fin n → Fin m`. -/
def Tm.rename {n m : ℕ} (ρ : Fin n → Fin m) : Tm TS n → Tm TS m
  | .var i => .var (ρ i)
  | .func f ts => .func f (ts.rename ρ)
/-- Renaming of variables in a tuple. -/
def Tms.rename {n m : ℕ} (ρ : Fin n → Fin m) : {k : ℕ} → Tms TS n k → Tms TS m k
  | _, .nil => .nil
  | _, .cons t ts => .cons (t.rename ρ) (ts.rename ρ)
end

mutual
/-- Simultaneous substitution of `σ i` for each variable `i`. -/
def Tm.subst {n m : ℕ} (σ : Subst TS n m) : Tm TS n → Tm TS m
  | .var i => σ i
  | .func f ts => .func f (ts.subst σ)
/-- Simultaneous substitution in a tuple. -/
def Tms.subst {n m : ℕ} (σ : Subst TS n m) : {k : ℕ} → Tms TS n k → Tms TS m k
  | _, .nil => .nil
  | _, .cons t ts => .cons (t.subst σ) (ts.subst σ)
end

namespace Tms

/-- The `i`-th component of a tuple. -/
def get {n : ℕ} : {k : ℕ} → Tms TS n k → Fin k → Tm TS n
  | _, .cons t _, ⟨0, _⟩ => t
  | _, .cons _ ts, ⟨i + 1, h⟩ => ts.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp] theorem get_cons_zero {n k : ℕ} (t : Tm TS n) (ts : Tms TS n k) :
    (cons t ts).get 0 = t := rfl

@[simp] theorem get_cons_succ {n k : ℕ} (t : Tm TS n) (ts : Tms TS n k) (i : Fin k) :
    (cons t ts).get i.succ = ts.get i := rfl

theorem get_subst {n m : ℕ} (σ : Subst TS n m) :
    ∀ {k : ℕ} (ts : Tms TS n k) (i : Fin k), (ts.subst σ).get i = (ts.get i).subst σ
  | _, .cons _ _, ⟨0, _⟩ => rfl
  | _, .cons _ ts, ⟨i + 1, h⟩ => get_subst σ ts ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem get_rename {n m : ℕ} (ρ : Fin n → Fin m) :
    ∀ {k : ℕ} (ts : Tms TS n k) (i : Fin k), (ts.rename ρ).get i = (ts.get i).rename ρ
  | _, .cons _ _, ⟨0, _⟩ => rfl
  | _, .cons _ ts, ⟨i + 1, h⟩ => get_rename ρ ts ⟨i, Nat.lt_of_succ_lt_succ h⟩

end Tms

namespace Tm

/-- Weakening: a term of scope `n` seen in scope `n + 1` (all variables lifted by one). -/
def shift {n : ℕ} (t : Tm TS n) : Tm TS (n + 1) := t.rename Fin.succ

@[simp] theorem rename_var {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    (var i : Tm TS n).rename ρ = var (ρ i) := rfl

@[simp] theorem subst_var {n m : ℕ} (σ : Subst TS n m) (i : Fin n) :
    (var i : Tm TS n).subst σ = σ i := rfl

@[simp] theorem shift_var {n : ℕ} (i : Fin n) : (var i : Tm TS n).shift = var i.succ := rfl

end Tm

mutual
theorem Tm.rename_rename {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    ∀ t : Tm TS n, (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ)
  | .var _ => rfl
  | .func f ts => by simp only [Tm.rename, Tms.rename_rename ρ ρ' ts]
theorem Tms.rename_rename {n m k : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    ∀ {j : ℕ} (ts : Tms TS n j), (ts.rename ρ).rename ρ' = ts.rename (ρ' ∘ ρ)
  | _, .nil => rfl
  | _, .cons t ts => by
    simp only [Tms.rename, Tm.rename_rename ρ ρ' t, Tms.rename_rename ρ ρ' ts]
end

mutual
theorem Tm.subst_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Subst TS m k) :
    ∀ t : Tm TS n, (t.rename ρ).subst σ = t.subst (σ ∘ ρ)
  | .var _ => rfl
  | .func f ts => by simp only [Tm.rename, Tm.subst, Tms.subst_rename ρ σ ts]
theorem Tms.subst_rename {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Subst TS m k) :
    ∀ {j : ℕ} (ts : Tms TS n j), (ts.rename ρ).subst σ = ts.subst (σ ∘ ρ)
  | _, .nil => rfl
  | _, .cons t ts => by
    simp only [Tms.rename, Tms.subst, Tm.subst_rename ρ σ t, Tms.subst_rename ρ σ ts]
end

mutual
theorem Tm.rename_subst {n m k : ℕ} (σ : Subst TS n m) (ρ : Fin m → Fin k) :
    ∀ t : Tm TS n, (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ)
  | .var _ => rfl
  | .func f ts => by simp only [Tm.rename, Tm.subst, Tms.rename_subst σ ρ ts]
theorem Tms.rename_subst {n m k : ℕ} (σ : Subst TS n m) (ρ : Fin m → Fin k) :
    ∀ {j : ℕ} (ts : Tms TS n j), (ts.subst σ).rename ρ = ts.subst (fun i => (σ i).rename ρ)
  | _, .nil => rfl
  | _, .cons t ts => by
    simp only [Tms.rename, Tms.subst, Tm.rename_subst σ ρ t, Tms.rename_subst σ ρ ts]
end

mutual
theorem Tm.subst_subst {n m k : ℕ} (σ : Subst TS n m) (τ : Subst TS m k) :
    ∀ t : Tm TS n, (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
  | .var _ => rfl
  | .func f ts => by simp only [Tm.subst, Tms.subst_subst σ τ ts]
theorem Tms.subst_subst {n m k : ℕ} (σ : Subst TS n m) (τ : Subst TS m k) :
    ∀ {j : ℕ} (ts : Tms TS n j), (ts.subst σ).subst τ = ts.subst (fun i => (σ i).subst τ)
  | _, .nil => rfl
  | _, .cons t ts => by
    simp only [Tms.subst, Tm.subst_subst σ τ t, Tms.subst_subst σ τ ts]
end

mutual
@[simp] theorem Tm.subst_var_eq {n : ℕ} : ∀ t : Tm TS n, t.subst Tm.var = t
  | .var _ => rfl
  | .func f ts => by simp only [Tm.subst, Tms.subst_var_eq ts]
@[simp] theorem Tms.subst_var_eq {n : ℕ} : ∀ {j : ℕ} (ts : Tms TS n j), ts.subst Tm.var = ts
  | _, .nil => rfl
  | _, .cons t ts => by simp only [Tms.subst, Tm.subst_var_eq t, Tms.subst_var_eq ts]
end

mutual
theorem Tm.rename_eq_subst {n m : ℕ} (ρ : Fin n → Fin m) :
    ∀ t : Tm TS n, t.rename ρ = t.subst (fun i => Tm.var (ρ i))
  | .var _ => rfl
  | .func f ts => by simp only [Tm.rename, Tm.subst, Tms.rename_eq_subst ρ ts]
theorem Tms.rename_eq_subst {n m : ℕ} (ρ : Fin n → Fin m) :
    ∀ {j : ℕ} (ts : Tms TS n j), ts.rename ρ = ts.subst (fun i => Tm.var (ρ i))
  | _, .nil => rfl
  | _, .cons t ts => by
    simp only [Tms.rename, Tms.subst, Tm.rename_eq_subst ρ t, Tms.rename_eq_subst ρ ts]
end

mutual
/-- Renaming along an injective map is injective. -/
theorem Tm.rename_injective {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) :
    ∀ s t : Tm TS n, s.rename ρ = t.rename ρ → s = t
  | .var i, .var j, h => by simp only [Tm.rename, Tm.var.injEq] at h; rw [hρ h]
  | .func f ts, .func g us, h => by
    simp only [Tm.rename, Tm.func.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Tms.rename_injective hρ ts us (eq_of_heq h)]
  | .var _, .func _ _, h => by simp [Tm.rename] at h
  | .func _ _, .var _, h => by simp [Tm.rename] at h
/-- Renaming a tuple along an injective map is injective. -/
theorem Tms.rename_injective {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) :
    ∀ {j : ℕ} (ss ts : Tms TS n j), ss.rename ρ = ts.rename ρ → ss = ts
  | _, .nil, .nil, _ => rfl
  | _, .cons s ss, .cons t ts, h => by
    simp only [Tms.rename, Tms.cons.injEq] at h
    rw [Tm.rename_injective hρ s t h.1, Tms.rename_injective hρ ss ts h.2]
end

namespace Tm

@[simp] theorem shift_subst_cons {n m : ℕ} (σ : Subst TS n m) (s : Tm TS m) (t : Tm TS n) :
    t.shift.subst (Fin.cons s σ) = t.subst σ := by
  simp only [shift, subst_rename]; rfl

theorem shift_subst {n m : ℕ} (σ : Subst TS n m) (t : Tm TS n) :
    (t.subst σ).shift = t.subst (fun i => (σ i).shift) := by
  simp only [shift, rename_subst]

end Tm

/-! ### Decidable equality of terms -/

section DecEq

variable [DecidableEq TS.Func]

mutual
/-- Decidable equality of terms (given decidable equality of function symbols). -/
def Tm.decEq {n : ℕ} : (s t : Tm TS n) → Decidable (s = t)
  | .var i, .var j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .var _, .func _ _ => isFalse (by intro e; cases e)
  | .func _ _, .var _ => isFalse (by intro e; cases e)
  | .func f ts, .func g us =>
    if hf : f = g then
      match g, hf, us with
      | _, rfl, us =>
        match Tms.decEq ts us with
        | isTrue h => isTrue (h ▸ rfl)
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hf rfl)
/-- Decidable equality of tuples of terms. -/
def Tms.decEq {n : ℕ} : {k : ℕ} → (ss ts : Tms TS n k) → Decidable (ss = ts)
  | _, .nil, .nil => isTrue rfl
  | _, .cons s ss, .cons t ts =>
    match Tm.decEq s t, Tms.decEq ss ts with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
end

instance {n : ℕ} : DecidableEq (Tm TS n) := Tm.decEq
instance {n k : ℕ} : DecidableEq (Tms TS n k) := Tms.decEq

end DecEq

namespace Subst

/-- The identity substitution. -/
abbrev id (TS : TermSig) (n : ℕ) : Subst TS n n := Tm.var

/-- Lifting a substitution under a binder: the bound variable `0` is kept, the other
variables are substituted and then weakened. -/
def lift {n m : ℕ} (σ : Subst TS n m) : Subst TS (n + 1) (m + 1) :=
  Fin.cons (Tm.var 0) (fun i => (σ i).shift)

/-- The weakening substitution `i ↦ i + 1` (used for the eigenvariable condition). -/
def weaken (n : ℕ) : Subst TS n (n + 1) := fun i => Tm.var i.succ

/-- `[t/0]`: substitute `t` for the variable `0` and lower the other variables. -/
def single {n : ℕ} (t : Tm TS n) : Subst TS (n + 1) n := Fin.cons t Tm.var

@[simp] theorem lift_zero {n m : ℕ} (σ : Subst TS n m) : lift σ 0 = Tm.var 0 := rfl

@[simp] theorem lift_succ {n m : ℕ} (σ : Subst TS n m) (i : Fin n) :
    lift σ i.succ = (σ i).shift := rfl

@[simp] theorem single_zero {n : ℕ} (t : Tm TS n) : single t 0 = t := rfl

@[simp] theorem single_succ {n : ℕ} (t : Tm TS n) (i : Fin n) : single t i.succ = Tm.var i :=
  rfl

@[simp] theorem weaken_apply {n : ℕ} (i : Fin n) : weaken (TS := TS) n i = Tm.var i.succ := rfl

@[simp] theorem lift_id {n : ℕ} : lift (Tm.var : Subst TS n n) = Tm.var := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

/-- Lifting commutes with composition of substitutions. -/
theorem lift_comp {n m k : ℕ} (σ : Subst TS n m) (τ : Subst TS m k) :
    (fun i => (lift σ i).subst (lift τ)) = lift (fun i => (σ i).subst τ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [lift_succ, Tm.shift]
  rw [Tm.subst_rename, Tm.rename_subst]; rfl

end Subst

/-- The formulas of LU (§6) whose free variables are among `Fin n`.
Quantifiers bind the variable `0` of a body in scope `n + 1`;
an atom `p(t₁, …, tₖ)` has a tuple of exactly `k = PS.arity p` arguments. -/
inductive Formula (PS : PredSig) (TS : TermSig) : ℕ → Type where
  /-- atomic formula `p(t₁, …, tₖ)`, with `k = PS.arity p` -/
  | atom {n : ℕ} (p : PS.Pred) (ts : Tms TS n (PS.arity p)) : Formula PS TS n
  /-- the constant `1` (also denoted `V`) -/
  | one {n : ℕ} : Formula PS TS n
  /-- the constant `0` (also denoted `F`) -/
  | zero {n : ℕ} : Formula PS TS n
  /-- the constant `⊥` -/
  | bot {n : ℕ} : Formula PS TS n
  /-- the constant `⊤` -/
  | top {n : ℕ} : Formula PS TS n
  /-- linear negation `A⊥` (also denoted `¬A`) -/
  | neg {n : ℕ} : Formula PS TS n → Formula PS TS n
  /-- `!A` -/
  | bang {n : ℕ} : Formula PS TS n → Formula PS TS n
  /-- `?A` -/
  | quest {n : ℕ} : Formula PS TS n → Formula PS TS n
  /-- `A ⊗ B` -/
  | tensor {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- `A ⅋ B` -/
  | par {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- `A ⊸ B` -/
  | lolli {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- `A & B` -/
  | with_ {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- `A ⊕ B` -/
  | plus {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- conjunction `A ∧ B` (classical and intuitionistic) -/
  | conj {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- disjunction `A ∨ B` (classical and intuitionistic) -/
  | disj {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- classical implication `A ⇒ B` -/
  | imp {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- intuitionistic implication `A ⊃ B` -/
  | iimp {n : ℕ} : Formula PS TS n → Formula PS TS n → Formula PS TS n
  /-- linear universal quantifier `⋀x A` (the body binds the variable `0`) -/
  | lall {n : ℕ} : Formula PS TS (n + 1) → Formula PS TS n
  /-- linear existential quantifier `⋁x A` -/
  | lex {n : ℕ} : Formula PS TS (n + 1) → Formula PS TS n
  /-- classical universal quantifier `∀x A` -/
  | call {n : ℕ} : Formula PS TS (n + 1) → Formula PS TS n
  /-- existential quantifier `∃x A` (classical and intuitionistic) -/
  | cex {n : ℕ} : Formula PS TS (n + 1) → Formula PS TS n

variable {PS : PredSig}

/-- Closed formulas (no free variable). -/
abbrev ClosedFormula (PS : PredSig) (TS : TermSig) := Formula PS TS 0

namespace Formula

section DecEq

variable [DecidableEq PS.Pred] [DecidableEq TS.Func]

set_option maxHeartbeats 1000000 in
/-- Decidable equality of formulas, given decidable equality of the function and predicate
symbols. -/
def decEq : {n : ℕ} → (A B : Formula PS TS n) → Decidable (A = B)
  | _, A, B => by
    cases A <;> cases B
    case atom.atom p ts q us =>
      exact if h : p = q then by subst h; exact decidable_of_iff (ts = us) (by simp)
        else isFalse (by intro e; cases e; exact h rfl)
    all_goals first
      | (apply isFalse; intro e; cases e; done)
      | (apply isTrue; rfl)
      | (rename_i A A' B B'
         haveI := decEq A B; haveI := decEq A' B'
         refine decidable_of_iff (A = B ∧ A' = B') ⟨?_, ?_⟩
         · rintro ⟨rfl, rfl⟩; rfl
         · intro e; cases e; exact ⟨rfl, rfl⟩)
      | (rename_i A B
         haveI := decEq A B
         refine decidable_of_iff (A = B) ⟨?_, ?_⟩
         · rintro rfl; rfl
         · intro e; cases e; rfl)

instance {n : ℕ} : DecidableEq (Formula PS TS n) := decEq

end DecEq

instance {n : ℕ} : Inhabited (Formula PS TS n) := ⟨one⟩

/-- Simultaneous substitution of terms for the free variables of a formula
(capture-avoiding by construction: the substitution is lifted under binders). -/
def subst {n m : ℕ} : Formula PS TS n → Subst TS n m → Formula PS TS m
  | atom p ts, σ => atom p (ts.subst σ)
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
def shift {n : ℕ} (A : Formula PS TS n) : Formula PS TS (n + 1) := A.subst (Subst.weaken n)

/-- `A[t/x]`: instantiate the bound variable (index `0`) of a quantifier body. -/
def inst {n : ℕ} (A : Formula PS TS (n + 1)) (t : Tm TS n) : Formula PS TS n :=
  A.subst (Subst.single t)

theorem subst_subst {n m k : ℕ} (A : Formula PS TS n) (σ : Subst TS n m) (τ : Subst TS m k) :
    (A.subst σ).subst τ = A.subst (fun i => (σ i).subst τ) := by
  induction A generalizing m k with
  | atom p ts => simp only [subst, Tms.subst_subst]
  | lall A ih => simp only [subst, ih, Subst.lift_comp]
  | lex A ih => simp only [subst, ih, Subst.lift_comp]
  | call A ih => simp only [subst, ih, Subst.lift_comp]
  | cex A ih => simp only [subst, ih, Subst.lift_comp]
  | _ => simp_all [subst]

@[simp] theorem subst_id {n : ℕ} (A : Formula PS TS n) : A.subst Tm.var = A := by
  induction A with
  | atom p ts => simp [subst]
  | _ => simp_all [subst]

theorem subst_congr {n m : ℕ} (A : Formula PS TS n) {σ τ : Subst TS n m}
    (h : ∀ i, σ i = τ i) :
    A.subst σ = A.subst τ := by
  rw [funext h]

/-- Weakening commutes with substitution. -/
theorem shift_subst {n m : ℕ} (A : Formula PS TS n) (σ : Subst TS n m) :
    (A.subst σ).shift = A.shift.subst (Subst.lift σ) := by
  simp only [shift, subst_subst]
  apply subst_congr
  intro i
  simp only [Subst.weaken_apply, Tm.subst_var, Subst.lift_succ, Tm.shift,
    Tm.rename_eq_subst]
  rfl

/-- Instantiation commutes with substitution. -/
theorem inst_subst {n m : ℕ} (A : Formula PS TS (n + 1)) (t : Tm TS n) (σ : Subst TS n m) :
    (A.inst t).subst σ = (A.subst (Subst.lift σ)).inst (t.subst σ) := by
  simp only [inst, subst_subst]
  apply subst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp [Subst.single, Subst.lift]

/-- Instantiating a weakened formula does nothing. -/
@[simp] theorem shift_inst {n : ℕ} (A : Formula PS TS n) (t : Tm TS n) : A.shift.inst t = A := by
  simp only [shift, inst, subst_subst]
  exact subst_id A

/-- Instantiating with the fresh variable `0` a body lifted under a binder gives it back. -/
@[simp] theorem subst_lift_weaken_inst {n : ℕ} (A : Formula PS TS (n + 1)) :
    (A.subst (Subst.lift (Subst.weaken n))).inst (Tm.var 0) = A := by
  simp only [inst, subst_subst]
  convert subst_id A using 2
  funext i
  refine Fin.cases rfl (fun j => rfl) i

/-- The lifting of a renaming is a renaming. -/
theorem _root_.LU.Subst.lift_ren {n m : ℕ} (ρ : Fin n → Fin m) :
    Subst.lift (fun i => Tm.var (ρ i) : Subst TS n m) =
      fun i => Tm.var ((Fin.cases 0 (fun j => (ρ j).succ) : Fin (n + 1) → Fin (m + 1)) i) := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

theorem _root_.LU.Subst.liftRen_injective {n m : ℕ} {ρ : Fin n → Fin m}
    (hρ : Function.Injective ρ) :
    Function.Injective (Fin.cases 0 (fun j => (ρ j).succ) : Fin (n + 1) → Fin (m + 1)) := by
  intro i j hij
  refine Fin.cases (Fin.cases (fun _ => rfl) (fun j h => ?_) j)
    (fun i => Fin.cases (fun h => ?_) (fun j h => ?_) j) i hij
  · exact absurd h.symm (Fin.succ_ne_zero _)
  · exact absurd h (Fin.succ_ne_zero _)
  · simp only [Fin.cases_succ, Fin.succ_inj] at h; rw [hρ h]

/-- Substitution along an injective renaming of variables is injective. -/
theorem subst_ren_injective {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {A B : Formula PS TS n}
    (h : A.subst (fun i => Tm.var (ρ i)) = B.subst (fun i => Tm.var (ρ i))) : A = B := by
  induction A generalizing m with
  | atom p ts =>
    cases B with
    | atom q us =>
      simp only [subst, atom.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [← Tms.rename_eq_subst, ← Tms.rename_eq_subst] at h
      rw [Tms.rename_injective hρ ts us (eq_of_heq h)]
    | _ => simp [subst] at h
  | lall A ih | lex A ih | call A ih | cex A ih =>
    cases B <;> simp only [subst, reduceCtorEq, lall.injEq, lex.injEq, call.injEq, cex.injEq,
      Subst.lift_ren] at h
    all_goals rw [ih (Subst.liftRen_injective hρ) h]
  | neg A ih | bang A ih | quest A ih =>
    cases B <;> simp only [subst, reduceCtorEq, neg.injEq, bang.injEq, quest.injEq] at h ⊢
    all_goals exact ih hρ h
  | tensor A A' ih ih' | par A A' ih ih' | lolli A A' ih ih' | with_ A A' ih ih'
  | plus A A' ih ih' | conj A A' ih ih' | disj A A' ih ih' | imp A A' ih ih'
  | iimp A A' ih ih' =>
    cases B <;> simp only [subst, reduceCtorEq, tensor.injEq, par.injEq, lolli.injEq, with_.injEq,
      plus.injEq, conj.injEq, disj.injEq, imp.injEq, iimp.injEq] at h ⊢
    all_goals exact ⟨ih hρ h.1, ih' hρ h.2⟩
  | one | zero | bot | top => cases B <;> simp only [subst, reduceCtorEq] at h ⊢

/-- Weakening is injective. -/
theorem shift_injective {n : ℕ} :
    Function.Injective (Formula.shift : Formula PS TS n → Formula PS TS (n + 1)) :=
  fun _ _ h => subst_ren_injective (Fin.succ_injective n) h

/-- The polarity of a formula (§2, Tables 1 and 2). -/
def pol {n : ℕ} : Formula PS TS n → Pol
  | atom p _ => PS.predPol p
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

@[simp] theorem pol_subst {n m : ℕ} (A : Formula PS TS n) (σ : Subst TS n m) :
    (A.subst σ).pol = A.pol := by
  induction A generalizing m <;> simp_all [subst, pol]

@[simp] theorem pol_shift {n : ℕ} (A : Formula PS TS n) : A.shift.pol = A.pol := pol_subst A _

@[simp] theorem pol_inst {n : ℕ} (A : Formula PS TS (n + 1)) (t : Tm TS n) :
    (A.inst t).pol = A.pol :=
  pol_subst A _

end Formula

end LU
