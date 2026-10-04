module

public import RequestProject.LU.Fragments

/-!
# Subformula property

Every rule of LU except cut has the subformula property: each formula of a premise is a
subformula (up to substitution of a term for a bound variable, and up to the shift used for
eigenvariables) of a formula of the conclusion.  We express this through *closed* classes of
formulas: if all formulas of the conclusion of a cut-free rule belong to a class closed under
immediate subformulas, then so do all formulas of the premises.  All the fragments of §6
are closed classes.
-/

@[expose] public section

namespace LU

open Formula

/-- A class of formulas closed under immediate subformulas, shift and instantiation. -/
structure SubClosed (F : Formula → Prop) : Prop where
  neg : ∀ A, F (neg A) → F A
  bang : ∀ A, F (bang A) → F A
  quest : ∀ A, F (quest A) → F A
  tensor : ∀ A B, F (tensor A B) → F A ∧ F B
  par : ∀ A B, F (par A B) → F A ∧ F B
  lolli : ∀ A B, F (lolli A B) → F A ∧ F B
  with_ : ∀ A B, F (with_ A B) → F A ∧ F B
  plus : ∀ A B, F (plus A B) → F A ∧ F B
  conj : ∀ A B, F (conj A B) → F A ∧ F B
  disj : ∀ A B, F (disj A B) → F A ∧ F B
  imp : ∀ A B, F (imp A B) → F A ∧ F B
  iimp : ∀ A B, F (iimp A B) → F A ∧ F B
  lall : ∀ A, F (lall A) → F A
  lex : ∀ A, F (lex A) → F A
  call : ∀ A, F (call A) → F A
  cex : ∀ A, F (cex A) → F A
  shift : ∀ A, F A → F A.shift
  inst : ∀ A t, F A → F (A.inst t)

theorem allIn_mk {F : Formula → Prop} {Γ Γ' Δ' Δ : Multiset Formula} :
    AllIn F ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫ ↔
      (∀ A ∈ Γ, F A) ∧ (∀ A ∈ Γ', F A) ∧ (∀ A ∈ Δ', F A) ∧ (∀ A ∈ Δ, F A) := by
  simp [AllIn, Sequent.formulas, or_imp, forall_and, and_assoc]

theorem forall_mem_sh {F : Formula → Prop} (hF : SubClosed F) {Γ : Multiset Formula}
    (h : ∀ A ∈ Γ, F A) : ∀ A ∈ sh Γ, F A := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.1 hA
  exact hF.shift B (h B hB)

set_option maxHeartbeats 4000000 in
/-- **Subformula property** of the cut-free rules of LU. -/
theorem Rule.allIn_premises {F : Formula → Prop} (hF : SubClosed F) {ps : List Sequent}
    {c : Sequent} (hr : Rule ps c) (hc : AllIn F c) : ∀ p ∈ ps, AllIn F p := by
  have hsh : ∀ Γ : Multiset Formula, (∀ A ∈ Γ, F A) → ∀ A ∈ sh Γ, F A :=
    fun Γ h => forall_mem_sh hF h
  have hneg := hF.neg
  have hbang := hF.bang
  have hquest := hF.quest
  have htensor₁ := fun A B h => (hF.tensor A B h).1
  have htensor₂ := fun A B h => (hF.tensor A B h).2
  have hpar₁ := fun A B h => (hF.par A B h).1
  have hpar₂ := fun A B h => (hF.par A B h).2
  have hlolli₁ := fun A B h => (hF.lolli A B h).1
  have hlolli₂ := fun A B h => (hF.lolli A B h).2
  have hwith₁ := fun A B h => (hF.with_ A B h).1
  have hwith₂ := fun A B h => (hF.with_ A B h).2
  have hplus₁ := fun A B h => (hF.plus A B h).1
  have hplus₂ := fun A B h => (hF.plus A B h).2
  have hconj₁ := fun A B h => (hF.conj A B h).1
  have hconj₂ := fun A B h => (hF.conj A B h).2
  have hdisj₁ := fun A B h => (hF.disj A B h).1
  have hdisj₂ := fun A B h => (hF.disj A B h).2
  have himp₁ := fun A B h => (hF.imp A B h).1
  have himp₂ := fun A B h => (hF.imp A B h).2
  have hiimp₁ := fun A B h => (hF.iimp A B h).1
  have hiimp₂ := fun A B h => (hF.iimp A B h).2
  have hlall := hF.lall
  have hlex := hF.lex
  have hcall := hF.call
  have hcex := hF.cex
  have hinst := hF.inst
  cases hr <;>
    simp only [allIn_mk, List.mem_cons, List.not_mem_nil, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.mem_add, Multiset.notMem_zero, or_imp, forall_and,
      Multiset.insert_eq_cons,
      forall_eq, or_false, IsEmpty.forall_iff, implies_true,
      true_and, and_true] at hc ⊢ <;>
    casesm* _ ∧ _ <;>
    (repeat' constructor) <;>
    first
    | assumption
    | exact hsh _ ‹_›
    | (apply hneg; assumption)
    | (apply hbang; assumption)
    | (apply hquest; assumption)
    | (apply htensor₁ <;> assumption)
    | (apply htensor₂ <;> assumption)
    | (apply hpar₁ <;> assumption)
    | (apply hpar₂ <;> assumption)
    | (apply hlolli₁ <;> assumption)
    | (apply hlolli₂ <;> assumption)
    | (apply hwith₁ <;> assumption)
    | (apply hwith₂ <;> assumption)
    | (apply hplus₁ <;> assumption)
    | (apply hplus₂ <;> assumption)
    | (apply hconj₁ <;> assumption)
    | (apply hconj₂ <;> assumption)
    | (apply hdisj₁ <;> assumption)
    | (apply hdisj₂ <;> assumption)
    | (apply himp₁ <;> assumption)
    | (apply himp₂ <;> assumption)
    | (apply hiimp₁ <;> assumption)
    | (apply hiimp₂ <;> assumption)
    | (apply hlall; assumption)
    | (apply hlex; assumption)
    | (apply hcall; assumption)
    | (apply hcex; assumption)
    | (apply hinst; apply hlall; assumption)
    | (apply hinst; apply hlex; assumption)
    | (apply hinst; apply hcall; assumption)
    | (apply hinst; apply hcex; assumption)


/-- In a cut-free derivation whose conclusion has all its formulas in a closed class `F`,
every sequent has all its formulas in `F`. -/
theorem Derivable.allIn {F : Formula → Prop} (hF : SubClosed F) {P : Sequent → Prop}
    {S : Sequent} (h : Derivable Rule P S) (hS : AllIn F S) :
    Derivable Rule (fun S => P S ∧ AllIn F S) S := by
  induction h with
  | mk ps c hr hc _ ih =>
    exact .mk ps c hr ⟨hc, hS⟩ fun p hp => ih p hp (hr.allIn_premises hF hS p hp)

namespace Formula

@[simp] theorem isClassical_shiftFrom (c : ℕ) (A : Formula) :
    (A.shiftFrom c).IsClassical ↔ A.IsClassical := by
  induction A generalizing c <;> simp_all [shiftFrom, IsClassical]

@[simp] theorem isClassical_substAt (k : ℕ) (s : Term) (A : Formula) :
    (A.substAt k s).IsClassical ↔ A.IsClassical := by
  induction A generalizing k s <;> simp_all [substAt, IsClassical]

@[simp] theorem isIntuitionistic_shiftFrom (c : ℕ) (A : Formula) :
    (A.shiftFrom c).IsIntuitionistic ↔ A.IsIntuitionistic := by
  induction A generalizing c <;> simp_all [shiftFrom, IsIntuitionistic]

@[simp] theorem isIntuitionistic_substAt (k : ℕ) (s : Term) (A : Formula) :
    (A.substAt k s).IsIntuitionistic ↔ A.IsIntuitionistic := by
  induction A generalizing k s <;> simp_all [substAt, IsIntuitionistic]

@[simp] theorem isNeutralInt_shiftFrom (c : ℕ) (A : Formula) :
    (A.shiftFrom c).IsNeutralInt ↔ A.IsNeutralInt := by
  induction A generalizing c <;> simp_all [shiftFrom, IsNeutralInt]

@[simp] theorem isNeutralInt_substAt (k : ℕ) (s : Term) (A : Formula) :
    (A.substAt k s).IsNeutralInt ↔ A.IsNeutralInt := by
  induction A generalizing k s <;> simp_all [substAt, IsNeutralInt]

@[simp] theorem isLinear_shiftFrom (c : ℕ) (A : Formula) :
    (A.shiftFrom c).IsLinear ↔ A.IsLinear := by
  induction A generalizing c <;> simp_all [shiftFrom, IsLinear]

@[simp] theorem isLinear_substAt (k : ℕ) (s : Term) (A : Formula) :
    (A.substAt k s).IsLinear ↔ A.IsLinear := by
  induction A generalizing k s <;> simp_all [substAt, IsLinear]

end Formula

theorem subClosed_classical : SubClosed IsClassical where
  neg _ h := h
  bang _ h := h.elim
  quest _ h := h.elim
  tensor _ _ h := h.elim
  par _ _ h := h.elim
  lolli _ _ h := h.elim
  with_ _ _ h := h.elim
  plus _ _ h := h.elim
  conj _ _ h := h
  disj _ _ h := h
  imp _ _ h := h
  iimp _ _ h := h.elim
  lall _ h := h.elim
  lex _ h := h.elim
  call _ h := h
  cex _ h := h
  shift A h := by simpa [shift] using h
  inst A t h := by simpa [inst] using h

theorem subClosed_intuitionistic : SubClosed IsIntuitionistic where
  neg _ h := h.elim
  bang _ h := h.elim
  quest _ h := h.elim
  tensor _ _ h := h.elim
  par _ _ h := h.elim
  lolli _ _ h := h.elim
  with_ _ _ h := h.elim
  plus _ _ h := h.elim
  conj _ _ h := h
  disj _ _ h := h
  imp _ _ h := h.elim
  iimp _ _ h := h
  lall _ h := h
  lex _ h := h.elim
  call _ h := h.elim
  cex _ h := h
  shift A h := by simpa [shift] using h
  inst A t h := by simpa [inst] using h

theorem subClosed_neutralInt : SubClosed IsNeutralInt where
  neg _ h := h.elim
  bang _ h := h.elim
  quest _ h := h.elim
  tensor _ _ h := h.elim
  par _ _ h := h.elim
  lolli _ _ h := h.elim
  with_ _ _ h := h.elim
  plus _ _ h := h.elim
  conj _ _ h := h
  disj _ _ h := h.elim
  imp _ _ h := h.elim
  iimp _ _ h := h
  lall _ h := h
  lex _ h := h.elim
  call _ h := h.elim
  cex _ h := h.elim
  shift A h := by simpa [shift] using h
  inst A t h := by simpa [inst] using h

theorem subClosed_linear : SubClosed IsLinear where
  neg _ h := h
  bang _ h := h
  quest _ h := h
  tensor _ _ h := h
  par _ _ h := h
  lolli _ _ h := h
  with_ _ _ h := h
  plus _ _ h := h
  conj _ _ h := h.elim
  disj _ _ h := h.elim
  imp _ _ h := h.elim
  iimp _ _ h := h.elim
  lall _ h := h
  lex _ h := h
  call _ h := h.elim
  cex _ h := h.elim
  shift A h := by simpa [shift] using h
  inst A t h := by simpa [inst] using h

end LU
