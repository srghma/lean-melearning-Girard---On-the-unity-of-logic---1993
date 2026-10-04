module

public import RequestProject.LU.Fragments

/-!
# Subformula property

Every rule of LU except cut has the subformula property: each formula of a premise is a
subformula (up to substitution of a term for a bound variable, and up to the weakening used
for eigenvariables) of a formula of the conclusion.  We express this through *closed* classes of
formulas: if all formulas of the conclusion of a cut-free rule belong to a class closed under
immediate subformulas, then so do all formulas of the premises.  All the fragments of §6
are closed classes.
-/

@[expose] public section

namespace LU

variable {n : ℕ}

open Formula

/-- A class of formulas closed under immediate subformulas, shift and instantiation. -/
structure SubClosed (F : ∀ {n : ℕ}, Formula n → Prop) : Prop where
  neg : ∀ {n : ℕ} (A : Formula n), F (neg A) → F A
  bang : ∀ {n : ℕ} (A : Formula n), F (bang A) → F A
  quest : ∀ {n : ℕ} (A : Formula n), F (quest A) → F A
  tensor : ∀ {n : ℕ} (A B : Formula n), F (tensor A B) → F A ∧ F B
  par : ∀ {n : ℕ} (A B : Formula n), F (par A B) → F A ∧ F B
  lolli : ∀ {n : ℕ} (A B : Formula n), F (lolli A B) → F A ∧ F B
  with_ : ∀ {n : ℕ} (A B : Formula n), F (with_ A B) → F A ∧ F B
  plus : ∀ {n : ℕ} (A B : Formula n), F (plus A B) → F A ∧ F B
  conj : ∀ {n : ℕ} (A B : Formula n), F (conj A B) → F A ∧ F B
  disj : ∀ {n : ℕ} (A B : Formula n), F (disj A B) → F A ∧ F B
  imp : ∀ {n : ℕ} (A B : Formula n), F (imp A B) → F A ∧ F B
  iimp : ∀ {n : ℕ} (A B : Formula n), F (iimp A B) → F A ∧ F B
  lall : ∀ {n : ℕ} (A : Formula (n + 1)), F (lall A) → F A
  lex : ∀ {n : ℕ} (A : Formula (n + 1)), F (lex A) → F A
  call : ∀ {n : ℕ} (A : Formula (n + 1)), F (call A) → F A
  cex : ∀ {n : ℕ} (A : Formula (n + 1)), F (cex A) → F A
  shift : ∀ {n : ℕ} (A : Formula n), F A → F A.shift
  inst : ∀ {n : ℕ} (A : Formula (n + 1)) (t : Term n), F A → F (A.inst t)

theorem allIn_mk {F : ∀ {n : ℕ}, Formula n → Prop} {Γ Γ' Δ' Δ : Multiset (Formula n)} :
    AllIn F ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫ ↔
      (∀ A ∈ Γ, F A) ∧ (∀ A ∈ Γ', F A) ∧ (∀ A ∈ Δ', F A) ∧ (∀ A ∈ Δ, F A) := by
  simp [AllIn, Sequent.formulas, or_imp, forall_and, and_assoc]

theorem forall_mem_sh {F : ∀ {n : ℕ}, Formula n → Prop} (hF : SubClosed F) {Γ : Multiset (Formula n)}
    (h : ∀ A ∈ Γ, F A) : ∀ A ∈ sh Γ, F A := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.1 hA
  exact hF.shift B (h B hB)

set_option maxHeartbeats 4000000 in
/-- **Subformula property** of the cut-free rules of LU. -/
theorem Rule.allIn_premises {F : ∀ {n : ℕ}, Formula n → Prop} (hF : SubClosed F) {ps : List Sequent}
    {c : Sequent} (hr : Rule ps c) (hc : AllIn F c) : ∀ p ∈ ps, AllIn F p := by
  have hsh : ∀ {n : ℕ} (Γ : Multiset (Formula n)), (∀ A ∈ Γ, F A) → ∀ A ∈ sh Γ, F A :=
    fun Γ h => forall_mem_sh hF h
  have hneg : ∀ {n : ℕ} (A : Formula n), F (neg A) → F A := hF.neg
  have hbang : ∀ {n : ℕ} (A : Formula n), F (bang A) → F A := hF.bang
  have hquest : ∀ {n : ℕ} (A : Formula n), F (quest A) → F A := hF.quest
  have htensor₁ : ∀ {n : ℕ} (A B : Formula n), F (tensor A B) → F A :=
    fun A B h => (hF.tensor A B h).1
  have htensor₂ : ∀ {n : ℕ} (A B : Formula n), F (tensor A B) → F B :=
    fun A B h => (hF.tensor A B h).2
  have hpar₁ : ∀ {n : ℕ} (A B : Formula n), F (par A B) → F A :=
    fun A B h => (hF.par A B h).1
  have hpar₂ : ∀ {n : ℕ} (A B : Formula n), F (par A B) → F B :=
    fun A B h => (hF.par A B h).2
  have hlolli₁ : ∀ {n : ℕ} (A B : Formula n), F (lolli A B) → F A :=
    fun A B h => (hF.lolli A B h).1
  have hlolli₂ : ∀ {n : ℕ} (A B : Formula n), F (lolli A B) → F B :=
    fun A B h => (hF.lolli A B h).2
  have hwith₁ : ∀ {n : ℕ} (A B : Formula n), F (with_ A B) → F A :=
    fun A B h => (hF.with_ A B h).1
  have hwith₂ : ∀ {n : ℕ} (A B : Formula n), F (with_ A B) → F B :=
    fun A B h => (hF.with_ A B h).2
  have hplus₁ : ∀ {n : ℕ} (A B : Formula n), F (plus A B) → F A :=
    fun A B h => (hF.plus A B h).1
  have hplus₂ : ∀ {n : ℕ} (A B : Formula n), F (plus A B) → F B :=
    fun A B h => (hF.plus A B h).2
  have hconj₁ : ∀ {n : ℕ} (A B : Formula n), F (conj A B) → F A :=
    fun A B h => (hF.conj A B h).1
  have hconj₂ : ∀ {n : ℕ} (A B : Formula n), F (conj A B) → F B :=
    fun A B h => (hF.conj A B h).2
  have hdisj₁ : ∀ {n : ℕ} (A B : Formula n), F (disj A B) → F A :=
    fun A B h => (hF.disj A B h).1
  have hdisj₂ : ∀ {n : ℕ} (A B : Formula n), F (disj A B) → F B :=
    fun A B h => (hF.disj A B h).2
  have himp₁ : ∀ {n : ℕ} (A B : Formula n), F (imp A B) → F A :=
    fun A B h => (hF.imp A B h).1
  have himp₂ : ∀ {n : ℕ} (A B : Formula n), F (imp A B) → F B :=
    fun A B h => (hF.imp A B h).2
  have hiimp₁ : ∀ {n : ℕ} (A B : Formula n), F (iimp A B) → F A :=
    fun A B h => (hF.iimp A B h).1
  have hiimp₂ : ∀ {n : ℕ} (A B : Formula n), F (iimp A B) → F B :=
    fun A B h => (hF.iimp A B h).2
  have hlall : ∀ {n : ℕ} (A : Formula (n + 1)), F (lall A) → F A := hF.lall
  have hlex : ∀ {n : ℕ} (A : Formula (n + 1)), F (lex A) → F A := hF.lex
  have hcall : ∀ {n : ℕ} (A : Formula (n + 1)), F (call A) → F A := hF.call
  have hcex : ∀ {n : ℕ} (A : Formula (n + 1)), F (cex A) → F A := hF.cex
  have hinst : ∀ {n : ℕ} (A : Formula (n + 1)) (t : Term n), F A → F (A.inst t) := hF.inst
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
theorem Derivable.allIn {F : ∀ {n : ℕ}, Formula n → Prop} (hF : SubClosed F) {P : Sequent → Prop}
    {S : Sequent} (h : Derivable Rule P S) (hS : AllIn F S) :
    Derivable Rule (fun S => P S ∧ AllIn F S) S := by
  induction h with
  | mk ps c hr hc _ ih =>
    exact .mk ps c hr ⟨hc, hS⟩ fun p hp => ih p hp (hr.allIn_premises hF hS p hp)

namespace Formula

@[simp] theorem isClassical_subst {m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).IsClassical ↔ A.IsClassical := by
  induction A generalizing m <;> simp_all [subst, IsClassical]

@[simp] theorem isIntuitionistic_subst {m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).IsIntuitionistic ↔ A.IsIntuitionistic := by
  induction A generalizing m <;> simp_all [subst, IsIntuitionistic]

@[simp] theorem isNeutralInt_subst {m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).IsNeutralInt ↔ A.IsNeutralInt := by
  induction A generalizing m <;> simp_all [subst, IsNeutralInt]

@[simp] theorem isLinear_subst {m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).IsLinear ↔ A.IsLinear := by
  induction A generalizing m <;> simp_all [subst, IsLinear]

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
