module

public import RequestProject.LU.Syntax

/-!
# Table 3: classical and intuitionistic connectives defined in terms of linear logic

Girard's chimeric connectives `∧, ∨, ⇒, ⊃, ∀, ∃` are defined (§5, Table 3) by pattern
matching on the polarities of their arguments, in terms of the connectives of linear logic.
`Formula.toLinear` is a literal transcription of Table 3 (applied recursively).

We check that Tables 2 and 3 are coherent with Table 1: the polarity of a chimeric formula
(Table 2) coincides with the polarity of its linear decomposition (Table 3), computed with
Table 1 (`pol_toLinear`); and the decomposition is a formula of linear logic
(`isLinearConn_toLinear`).
-/

@[expose] public section

namespace LU

namespace Formula

/-- Table 3, conjunction `A ∧ B` (here `a`, `b` are the polarities of `A`, `B`). -/
def conjLin : Pol → Pol → Formula → Formula → Formula
  | .pos, .pos, A, B => tensor A B
  | .neu, .pos, A, B => tensor (bang A) B
  | .neg, .pos, A, B => tensor (bang A) B
  | .pos, .neu, A, B => tensor A (bang B)
  | .neu, .neu, A, B => with_ A B
  | .neg, .neu, A, B => with_ A B
  | .pos, .neg, A, B => tensor A (bang B)
  | .neu, .neg, A, B => with_ A B
  | .neg, .neg, A, B => with_ A B

/-- Table 3, disjunction `A ∨ B`. -/
def disjLin : Pol → Pol → Formula → Formula → Formula
  | .pos, .pos, A, B => plus A B
  | .neu, .pos, A, B => plus (bang A) B
  | .neg, .pos, A, B => par A (quest B)
  | .pos, .neu, A, B => plus A (bang B)
  | .neu, .neu, A, B => plus (bang A) (bang B)
  | .neg, .neu, A, B => par A (quest (bang B))
  | .pos, .neg, A, B => par (quest A) B
  | .neu, .neg, A, B => par (quest (bang A)) B
  | .neg, .neg, A, B => par A B

/-- Table 3, classical implication `A ⇒ B`. -/
def impLin : Pol → Pol → Formula → Formula → Formula
  | .pos, .pos, A, B => lolli A (quest B)
  | .neu, .pos, A, B => plus (bang (neg A)) B
  | .neg, .pos, A, B => plus (neg A) B
  | .pos, .neu, A, B => lolli A (quest (bang B))
  | .neu, .neu, A, B => plus (bang (neg A)) (bang B)
  | .neg, .neu, A, B => plus (neg A) (bang B)
  | .pos, .neg, A, B => lolli A B
  | .neu, .neg, A, B => par (quest (bang (neg A))) B
  | .neg, .neg, A, B => lolli (bang A) B

/-- Table 3, intuitionistic implication `A ⊃ B`. -/
def iimpLin : Pol → Formula → Formula → Formula
  | .pos, A, B => lolli A B
  | _, A, B => lolli (bang A) B

/-- Table 3, `∀x A`. -/
def callLin : Pol → Formula → Formula
  | .neg, A => lall A
  | _, A => lall (quest A)

/-- Table 3, `∃x A`. -/
def cexLin : Pol → Formula → Formula
  | .pos, A => lex A
  | _, A => lex (bang A)

/-- The translation of LU formulas into linear logic given by Table 3
(chimeric connectives are unfolded according to the polarities of their arguments). -/
def toLinear : Formula → Formula
  | atom p ts => atom p ts
  | one => one
  | zero => zero
  | bot => bot
  | top => top
  | neg A => neg A.toLinear
  | bang A => bang A.toLinear
  | quest A => quest A.toLinear
  | tensor A B => tensor A.toLinear B.toLinear
  | par A B => par A.toLinear B.toLinear
  | lolli A B => lolli A.toLinear B.toLinear
  | with_ A B => with_ A.toLinear B.toLinear
  | plus A B => plus A.toLinear B.toLinear
  | conj A B => conjLin A.pol B.pol A.toLinear B.toLinear
  | disj A B => disjLin A.pol B.pol A.toLinear B.toLinear
  | imp A B => impLin A.pol B.pol A.toLinear B.toLinear
  | iimp A B => iimpLin A.pol A.toLinear B.toLinear
  | lall A => lall A.toLinear
  | lex A => lex A.toLinear
  | call A => callLin A.pol A.toLinear
  | cex A => cexLin A.pol A.toLinear

/-- Formulas built only from atoms, constants and the connectives of linear logic. -/
def IsLinearConn : Formula → Prop
  | atom _ _ => True
  | one => True
  | zero => True
  | bot => True
  | top => True
  | neg A => A.IsLinearConn
  | bang A => A.IsLinearConn
  | quest A => A.IsLinearConn
  | tensor A B => A.IsLinearConn ∧ B.IsLinearConn
  | par A B => A.IsLinearConn ∧ B.IsLinearConn
  | lolli A B => A.IsLinearConn ∧ B.IsLinearConn
  | with_ A B => A.IsLinearConn ∧ B.IsLinearConn
  | plus A B => A.IsLinearConn ∧ B.IsLinearConn
  | conj _ _ => False
  | disj _ _ => False
  | imp _ _ => False
  | iimp _ _ => False
  | lall A => A.IsLinearConn
  | lex A => A.IsLinearConn
  | call _ => False
  | cex _ => False

/-- **Coherence of Tables 1, 2 and 3.** The polarity of every formula (Tables 1 and 2)
equals the polarity of its linear decomposition (Table 3). -/
theorem pol_toLinear (A : Formula) : A.toLinear.pol = A.pol := by
  induction A with
  | conj A B ihA ihB =>
    simp only [toLinear, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [conjLin, pol, Pol.tensor, Pol.with_,
      Pol.conj]
  | disj A B ihA ihB =>
    simp only [toLinear, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [disjLin, pol, Pol.plus, Pol.par,
      Pol.disj]
  | imp A B ihA ihB =>
    simp only [toLinear, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [impLin, pol, Pol.plus, Pol.par,
      Pol.lolli, Pol.imp, Pol.dual]
  | iimp A B ihA ihB =>
    simp only [toLinear, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [iimpLin, pol, Pol.lolli, Pol.iimp]
  | call A ihA =>
    simp only [toLinear, pol]
    cases hA : A.pol <;> simp_all [callLin, pol, Pol.lall]
  | cex A ihA =>
    simp only [toLinear, pol]
    cases hA : A.pol <;> simp_all [cexLin, pol, Pol.lex]
  | _ => simp_all [toLinear, pol]

/-- The decomposition of Table 3 only uses the connectives of linear logic. -/
theorem isLinearConn_toLinear (A : Formula) : A.toLinear.IsLinearConn := by
  induction A with
  | conj A B ihA ihB =>
    simp only [toLinear]
    cases A.pol <;> cases B.pol <;> simp_all [conjLin, IsLinearConn]
  | disj A B ihA ihB =>
    simp only [toLinear]
    cases A.pol <;> cases B.pol <;> simp_all [disjLin, IsLinearConn]
  | imp A B ihA ihB =>
    simp only [toLinear]
    cases A.pol <;> cases B.pol <;> simp_all [impLin, IsLinearConn]
  | iimp A B ihA ihB =>
    simp only [toLinear]
    cases A.pol <;> simp_all [iimpLin, IsLinearConn]
  | call A ihA =>
    simp only [toLinear]
    cases A.pol <;> simp_all [callLin, IsLinearConn]
  | cex A ihA =>
    simp only [toLinear]
    cases A.pol <;> simp_all [cexLin, IsLinearConn]
  | _ => simp_all [toLinear, IsLinearConn]

end Formula

end LU
