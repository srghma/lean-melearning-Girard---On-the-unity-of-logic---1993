module

public import Mathlib

/-!
# Checking the proposed signature-parameterised syntax

Standalone checks for `SIGNATURE_ASSESSMENT.md`. This file is not imported by the
formalization of LU.

* `Proposed`: the proposed design, in which the index `1` stands both for "a term" and for
  "a 1-tuple of terms".  The atom `p(x)` then has two distinct representations, and nested
  tuples are accepted as terms.
* `FixedA`: function and predicate symbols from a signature, with arguments given as
  `Fin (arity f) → Term`.
* `FixedB`: first-order tuples, with terms and tuples separated by an `Option ℕ` index.
-/

@[expose] public section

namespace SignatureAssessment

/-- Polarities (local copy, to keep this file standalone). -/
inductive Pol where
  | pos
  | neu
  | neg

/-- A signature of function symbols. -/
structure TermSig where
  Func : Type
  arity : Func → ℕ

/-- A signature of predicate symbols, with polarities. -/
structure PredSig where
  Pred : Type
  arity : Pred → ℕ
  predPol : Pred → Pol

namespace Proposed

/-- The proposed term family. -/
inductive Term (TS : TermSig) (n : ℕ) : ℕ → Type where
  | var : Fin n → Term TS n 1
  | func (f : TS.Func) : Term TS n (TS.arity f) → Term TS n 1
  | nil : Term TS n 0
  | cons {k : ℕ} : Term TS n 1 → Term TS n k → Term TS n (k + 1)

/-- The proposed formulas (only atoms and `1`, which is enough for the check). -/
inductive Formula (PS : PredSig) (TS : TermSig) : ℕ → Type where
  | atom {n : ℕ} (p : PS.Pred) (t : Term TS n (PS.arity p)) : Formula PS TS n
  | one {n : ℕ} : Formula PS TS n

/-- One unary positive predicate `p`. -/
def unaryPred : PredSig := ⟨Unit, fun _ => 1, fun _ => .pos⟩

/-- No function symbols. -/
def noFunc : TermSig := ⟨Empty, Empty.elim⟩

/-- In the proposed design, the atom `p(x)` has two distinct representations. -/
theorem atom_two_representations :
    (Formula.atom (PS := unaryPred) (TS := noFunc) (n := 1) () (Term.var 0)) ≠
      Formula.atom () (Term.cons (Term.var 0) Term.nil) := by
  intro h
  cases h

/-- A nested 1-tuple passes as a term. -/
def junkTerm : Term noFunc 1 1 := Term.cons (Term.cons (Term.var 0) Term.nil) Term.nil

/-- Renaming of variables is still injective for an injective renaming, so `shift`
injectivity can be proved without an inhabitant of the closed terms. -/
def Term.rename {TS : TermSig} {n m : ℕ} (ρ : Fin n → Fin m) :
    {k : ℕ} → Term TS n k → Term TS m k
  | _, var i => var (ρ i)
  | _, func f ts => func f (ts.rename ρ)
  | _, nil => nil
  | _, cons t ts => cons (t.rename ρ) (ts.rename ρ)

theorem Term.rename_injective {TS : TermSig} {n m : ℕ} (ρ : Fin n → Fin m)
    (hρ : Function.Injective ρ) :
    ∀ {k : ℕ} (s t : Term TS n k), s.rename ρ = t.rename ρ → s = t
  | _, var i, var j, h => by simp only [rename, var.injEq] at h; rw [hρ h]
  | _, func f ts, func g us, h => by
    simp only [rename, func.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Term.rename_injective ρ hρ ts us (eq_of_heq h)]
  | _, nil, nil, _ => rfl
  | _, cons t ts, cons u us, h => by
    simp only [rename, cons.injEq] at h
    rw [Term.rename_injective ρ hρ t u h.1, Term.rename_injective ρ hρ ts us h.2]
  | _, var _, func _ _, h => by simp [rename] at h
  | _, func _ _, var _, h => by simp [rename] at h
  | _, var _, cons _ _, h => by simp [rename] at h
  | _, cons _ _, var _, h => by simp [rename] at h
  | _, func _ _, cons _ _, h => by simp [rename] at h
  | _, cons _ _, func _ _, h => by simp [rename] at h

end Proposed

namespace FixedA

/-- Terms over a signature, arguments as functions on `Fin (arity f)`. -/
inductive Term (TS : TermSig) (n : ℕ) : Type where
  | var : Fin n → Term TS n
  | func (f : TS.Func) : (Fin (TS.arity f) → Term TS n) → Term TS n

/-- Atoms over a signature (the other connectives are unchanged). -/
inductive Formula (PS : PredSig) (TS : TermSig) : ℕ → Type where
  | atom {n : ℕ} (p : PS.Pred) (ts : Fin (PS.arity p) → Term TS n) : Formula PS TS n
  | one {n : ℕ} : Formula PS TS n

/-- Renaming, by structural recursion. -/
def Term.rename {TS : TermSig} {n m : ℕ} (ρ : Fin n → Fin m) : Term TS n → Term TS m
  | var i => var (ρ i)
  | func f ts => func f (fun i => (ts i).rename ρ)

end FixedA

namespace FixedB

/-- `Term TS n none` are the terms, `Term TS n (some k)` the `k`-tuples of terms. -/
inductive Term (TS : TermSig) (n : ℕ) : Option ℕ → Type where
  | var : Fin n → Term TS n none
  | func (f : TS.Func) : Term TS n (some (TS.arity f)) → Term TS n none
  | nil : Term TS n (some 0)
  | cons {k : ℕ} : Term TS n none → Term TS n (some k) → Term TS n (some (k + 1))

/-- Renaming, by structural recursion. -/
def Term.rename {TS : TermSig} {n m : ℕ} (ρ : Fin n → Fin m) :
    {k : Option ℕ} → Term TS n k → Term TS m k
  | _, var i => var (ρ i)
  | _, func f ts => func f (ts.rename ρ)
  | _, nil => nil
  | _, cons t ts => cons (t.rename ρ) (ts.rename ρ)

/-- With the split index, the argument of a unary predicate is always a genuine 1-tuple
`(u)` of a term `u`: there is no second representation. -/
theorem unary_tuple {TS : TermSig} {n : ℕ} (t : Term TS n (some 1)) :
    ∃ u, t = Term.cons u Term.nil := by
  rcases t with _ | _ | _ | ⟨u, ts⟩
  cases ts
  exact ⟨u, rfl⟩

end FixedB

end SignatureAssessment
