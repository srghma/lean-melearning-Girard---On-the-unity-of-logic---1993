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

First-order variables are represented with de Bruijn indices: the body of a quantifier
uses the index `0` for the bound variable.  `A[t/x]` (substitution of the term `t` for the
bound variable) is `Formula.inst A t`, and the eigenvariable condition "`x` not free in the
context" is expressed by shifting the context (`Formula.shift`).
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

/-! ## Terms and formulas -/

/-- First-order terms, with de Bruijn indices for variables. -/
inductive Term where
  | var : ℕ → Term
  | func : ℕ → List Term → Term
  deriving Inhabited

namespace Term

/-- Lift every variable `≥ c` by one. -/
def shift (c : ℕ) : Term → Term
  | var n => if n < c then var n else var (n + 1)
  | func f ts => func f (ts.map (shift c))

/-- Substitute `s` for the variable `k` (and lower the variables above `k`). -/
def subst (k : ℕ) (s : Term) : Term → Term
  | var n => if n < k then var n else if n = k then s else var (n - 1)
  | func f ts => func f (ts.map (subst k s))

end Term

/-- A predicate symbol: a name, an arity and a polarity
("atomic predicates are given with their polarity", §6). -/
structure Pred where
  name : ℕ
  arity : ℕ
  pol : Pol
  deriving DecidableEq

/-- The formulas of LU (§6). -/
inductive Formula where
  /-- atomic formula `a t₁ … tₙ` -/
  | atom : Pred → List Term → Formula
  /-- the constant `1` (also denoted `V`) -/
  | one : Formula
  /-- the constant `0` (also denoted `F`) -/
  | zero : Formula
  /-- the constant `⊥` -/
  | bot : Formula
  /-- the constant `⊤` -/
  | top : Formula
  /-- linear negation `A⊥` (also denoted `¬A`) -/
  | neg : Formula → Formula
  /-- `!A` -/
  | bang : Formula → Formula
  /-- `?A` -/
  | quest : Formula → Formula
  /-- `A ⊗ B` -/
  | tensor : Formula → Formula → Formula
  /-- `A ⅋ B` -/
  | par : Formula → Formula → Formula
  /-- `A ⊸ B` -/
  | lolli : Formula → Formula → Formula
  /-- `A & B` -/
  | with_ : Formula → Formula → Formula
  /-- `A ⊕ B` -/
  | plus : Formula → Formula → Formula
  /-- conjunction `A ∧ B` (classical and intuitionistic) -/
  | conj : Formula → Formula → Formula
  /-- disjunction `A ∨ B` (classical and intuitionistic) -/
  | disj : Formula → Formula → Formula
  /-- classical implication `A ⇒ B` -/
  | imp : Formula → Formula → Formula
  /-- intuitionistic implication `A ⊃ B` -/
  | iimp : Formula → Formula → Formula
  /-- linear universal quantifier `⋀x A` (body uses de Bruijn index `0`) -/
  | lall : Formula → Formula
  /-- linear existential quantifier `⋁x A` -/
  | lex : Formula → Formula
  /-- classical universal quantifier `∀x A` -/
  | call : Formula → Formula
  /-- existential quantifier `∃x A` (classical and intuitionistic) -/
  | cex : Formula → Formula
  deriving Inhabited

namespace Formula

/-- Lift every free variable `≥ c` by one. -/
def shiftFrom (c : ℕ) : Formula → Formula
  | atom p ts => atom p (ts.map (Term.shift c))
  | one => one
  | zero => zero
  | bot => bot
  | top => top
  | neg A => neg (A.shiftFrom c)
  | bang A => bang (A.shiftFrom c)
  | quest A => quest (A.shiftFrom c)
  | tensor A B => tensor (A.shiftFrom c) (B.shiftFrom c)
  | par A B => par (A.shiftFrom c) (B.shiftFrom c)
  | lolli A B => lolli (A.shiftFrom c) (B.shiftFrom c)
  | with_ A B => with_ (A.shiftFrom c) (B.shiftFrom c)
  | plus A B => plus (A.shiftFrom c) (B.shiftFrom c)
  | conj A B => conj (A.shiftFrom c) (B.shiftFrom c)
  | disj A B => disj (A.shiftFrom c) (B.shiftFrom c)
  | imp A B => imp (A.shiftFrom c) (B.shiftFrom c)
  | iimp A B => iimp (A.shiftFrom c) (B.shiftFrom c)
  | lall A => lall (A.shiftFrom (c + 1))
  | lex A => lex (A.shiftFrom (c + 1))
  | call A => call (A.shiftFrom (c + 1))
  | cex A => cex (A.shiftFrom (c + 1))

/-- Lift all free variables by one (used for the eigenvariable condition). -/
def shift (A : Formula) : Formula := A.shiftFrom 0

/-- Substitute the term `s` for the variable `k`. -/
def substAt (k : ℕ) (s : Term) : Formula → Formula
  | atom p ts => atom p (ts.map (Term.subst k s))
  | one => one
  | zero => zero
  | bot => bot
  | top => top
  | neg A => neg (A.substAt k s)
  | bang A => bang (A.substAt k s)
  | quest A => quest (A.substAt k s)
  | tensor A B => tensor (A.substAt k s) (B.substAt k s)
  | par A B => par (A.substAt k s) (B.substAt k s)
  | lolli A B => lolli (A.substAt k s) (B.substAt k s)
  | with_ A B => with_ (A.substAt k s) (B.substAt k s)
  | plus A B => plus (A.substAt k s) (B.substAt k s)
  | conj A B => conj (A.substAt k s) (B.substAt k s)
  | disj A B => disj (A.substAt k s) (B.substAt k s)
  | imp A B => imp (A.substAt k s) (B.substAt k s)
  | iimp A B => iimp (A.substAt k s) (B.substAt k s)
  | lall A => lall (A.substAt (k + 1) (s.shift 0))
  | lex A => lex (A.substAt (k + 1) (s.shift 0))
  | call A => call (A.substAt (k + 1) (s.shift 0))
  | cex A => cex (A.substAt (k + 1) (s.shift 0))

/-- `A[t/x]`: instantiate the bound variable (de Bruijn index `0`) of a quantifier body. -/
def inst (A : Formula) (t : Term) : Formula := A.substAt 0 t

/-- The polarity of a formula (§2, Tables 1 and 2). -/
def pol : Formula → Pol
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

@[simp] theorem pol_shiftFrom (c : ℕ) (A : Formula) : (A.shiftFrom c).pol = A.pol := by
  induction A generalizing c <;> simp_all [shiftFrom, pol]

@[simp] theorem pol_shift (A : Formula) : A.shift.pol = A.pol := pol_shiftFrom 0 A

@[simp] theorem pol_substAt (k : ℕ) (s : Term) (A : Formula) : (A.substAt k s).pol = A.pol := by
  induction A generalizing k s <;> simp_all [substAt, pol]

@[simp] theorem pol_inst (A : Formula) (t : Term) : (A.inst t).pol = A.pol := pol_substAt 0 t A

end Formula

end LU
