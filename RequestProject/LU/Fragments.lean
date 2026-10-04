module

public import RequestProject.LU.Calculus

/-!
# Remarkable fragments of LU (§6)

The fragments are defined by a restriction of the possible atomic formulas and of the
possible connectives and quantifiers:

1. the **classical** fragment: positive and negative atoms (including `V = 1` and `F = 0`),
   closed under `¬ = (·)⊥, ∧, ∨, ⇒, ∀x, ∃x`;
2. the **intuitionistic** fragment: positive and neutral atoms (including `V` and `F`),
   closed under `∧, ∨, ⊃, ⋀x, ∃x`;
3. the **neutral intuitionistic** fragment: neutral atoms, closed under `∧, ⊃, ⋀x`;
4. the **linear** fragment: all atoms (and the constants `1, 0, ⊥, ⊤`), closed under
   `(·)⊥, ⊗, ⅋, ⊸, ⊕, &, !, ?, ⋀x, ⋁x`.

Each fragment has its own notion of sequent:

* (i) a classical sequent `Γ;Γ' ⊢ Π';Π` is such that the number of negative formulas in `Γ`
  plus the number of positive formulas in `Π` is `0` or `1`;
* (ii) an intuitionistic sequent is of the form `Γ;Γ' ⊢ ;A`;
* (iii) a neutral intuitionistic sequent is a sequent `Γ;Γ' ⊢ ;A` with at most one formula
  in `Γ`;
* a linear sequent is any sequent made of linear formulas.

In every case all the formulas of the sequent must belong to the fragment.
-/

@[expose] public section

namespace LU

variable {n : ℕ}

open Formula

namespace Formula

/-- Formulas of the classical fragment. -/
def IsClassical {n : ℕ} : Formula n → Prop
  | atom p _ => p.pol ≠ .neu
  | one => True
  | zero => True
  | neg A => A.IsClassical
  | conj A B => A.IsClassical ∧ B.IsClassical
  | disj A B => A.IsClassical ∧ B.IsClassical
  | imp A B => A.IsClassical ∧ B.IsClassical
  | call A => A.IsClassical
  | cex A => A.IsClassical
  | _ => False

/-- Formulas of the intuitionistic fragment. -/
def IsIntuitionistic {n : ℕ} : Formula n → Prop
  | atom p _ => p.pol ≠ .neg
  | one => True
  | zero => True
  | conj A B => A.IsIntuitionistic ∧ B.IsIntuitionistic
  | disj A B => A.IsIntuitionistic ∧ B.IsIntuitionistic
  | iimp A B => A.IsIntuitionistic ∧ B.IsIntuitionistic
  | lall A => A.IsIntuitionistic
  | cex A => A.IsIntuitionistic
  | _ => False

/-- Formulas of the neutral intuitionistic fragment. -/
def IsNeutralInt {n : ℕ} : Formula n → Prop
  | atom p _ => p.pol = .neu
  | conj A B => A.IsNeutralInt ∧ B.IsNeutralInt
  | iimp A B => A.IsNeutralInt ∧ B.IsNeutralInt
  | lall A => A.IsNeutralInt
  | _ => False

/-- Formulas of the linear fragment. -/
def IsLinear {n : ℕ} : Formula n → Prop
  | atom _ _ => True
  | one => True
  | zero => True
  | bot => True
  | top => True
  | neg A => A.IsLinear
  | bang A => A.IsLinear
  | quest A => A.IsLinear
  | tensor A B => A.IsLinear ∧ B.IsLinear
  | par A B => A.IsLinear ∧ B.IsLinear
  | lolli A B => A.IsLinear ∧ B.IsLinear
  | with_ A B => A.IsLinear ∧ B.IsLinear
  | plus A B => A.IsLinear ∧ B.IsLinear
  | lall A => A.IsLinear
  | lex A => A.IsLinear
  | _ => False

end Formula

/-- All formulas of a sequent satisfy `F`. -/
def AllIn (F : ∀ {n : ℕ}, Formula n → Prop) (S : Sequent) : Prop := ∀ A ∈ S.formulas, F A

/-- `μ(S)`: the number of negative formulas in `Γ` plus the number of positive formulas
in `Δ`, for `S = Γ;Γ' ⊢ Δ';Δ`. -/
def mu (S : Sequent) : ℕ :=
  Multiset.card (S.L.filter (fun A => A.pol = .neg)) +
    Multiset.card (S.R.filter (fun A => A.pol = .pos))

/-- Classical sequents. -/
def ClassicalSeq (S : Sequent) : Prop := AllIn IsClassical S ∧ mu S ≤ 1

/-- Intuitionistic sequents `Γ;Γ' ⊢ ;A`. -/
def IntSeq (S : Sequent) : Prop :=
  AllIn IsIntuitionistic S ∧ S.CR = 0 ∧ Multiset.card S.R = 1

/-- Neutral intuitionistic sequents `Γ;Γ' ⊢ ;A` with at most one formula in `Γ`. -/
def NeutralIntSeq (S : Sequent) : Prop :=
  AllIn IsNeutralInt S ∧ S.CR = 0 ∧ Multiset.card S.R = 1 ∧ Multiset.card S.L ≤ 1

/-- Linear sequents. -/
def LinearSeq (S : Sequent) : Prop := AllIn IsLinear S

/-- The four remarkable fragments of §6. -/
inductive Fragment where
  | classical
  | intuitionistic
  | neutralIntuitionistic
  | linear

/-- The sequents of a fragment. -/
def Fragment.Seq : Fragment → Sequent → Prop
  | .classical => ClassicalSeq
  | .intuitionistic => IntSeq
  | .neutralIntuitionistic => NeutralIntSeq
  | .linear => LinearSeq

/-- A sequent is *provable within the fragment* `F` if it has a cut-free derivation all of
whose sequents are sequents of `F`. -/
def ProvableWithin (F : Fragment) (S : Sequent) : Prop := Derivable Rule F.Seq S

end LU
