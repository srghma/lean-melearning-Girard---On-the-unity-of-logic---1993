module

public import RequestProject.LU.Subformula

/-!
# The linear and the neutral intuitionistic fragments

* Linear fragment: by the subformula property, a cut-free proof of a linear sequent only
  contains linear sequents.
* Neutral intuitionistic fragment (proof of the Theorem of §6): for any cut-free rule of LU
  ending with a neutral intuitionistic sequent `Γ;Γ' ⊢ ;S`, all premises are of the form
  `Λ;Λ' ⊢ ;T`, and one of them has at least as many formulas in its linear left zone as `Γ`,
  with the only exception of the identity axiom.  Hence `Γ` contains at most one formula
  (the analogue of the head variable of typed λ-calculi).
-/

@[expose] public section

namespace LU

open Formula

theorem linear_within {S : Sequent} (h : CutFreeProvable S) (hS : LinearSeq S) :
    ProvableWithin .linear S :=
  (h.allIn subClosed_linear hS).mono (fun _ _ h => h) (fun _ h => h.2)

theorem Formula.IsNeutralInt.pol_eq {A : Formula} (h : A.IsNeutralInt) : A.pol = .neu := by
  induction A with
  | atom p ts => exact h
  | conj A B ihA ihB => simp [pol, ihA h.1, ihB h.2, Pol.conj]
  | iimp A B ihA ihB => simp [pol, ihB h.2, Pol.iimp]
  | lall A ihA => simp [pol, ihA h, Pol.lall]
  | _ => exact h.elim

/-- The shape of a neutral intuitionistic sequent, apart from the bound on `Γ`. -/
def NeutShape (S : Sequent) : Prop :=
  AllIn IsNeutralInt S ∧ S.CR = 0 ∧ Multiset.card S.R = 1

set_option maxHeartbeats 4000000 in
/-- Rule analysis for the neutral intuitionistic fragment. -/
theorem Rule.neutral {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (hc : NeutShape c) :
    (∀ p ∈ ps, p.CR = 0 ∧ Multiset.card p.R = 1) ∧
      (ps = [] → Multiset.card c.L ≤ 1) ∧
      (ps ≠ [] → ∃ p ∈ ps, Multiset.card c.L ≤ Multiset.card p.L) := by
  obtain ⟨hA, hCR, hR⟩ : AllIn IsNeutralInt c ∧ c.CR = 0 ∧ Multiset.card c.R = 1 := hc
  have hpol : ∀ A : Formula, A.IsNeutralInt → A.pol = .neu := fun A h => h.pol_eq
  cases hr <;>
    simp only [allIn_mk, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton,
      or_imp, forall_and, forall_eq, IsNeutralInt] at hA <;>
    simp_all

theorem neutral_main {S : Sequent} (h : CutFreeProvable S) (hS : NeutShape S) :
    Multiset.card S.L ≤ 1 ∧ ProvableWithin .neutralIntuitionistic S := by
  unfold CutFreeProvable at h
  induction h with
  | mk ps c hr _ _ ih =>
    obtain ⟨h1, h2, h3⟩ := hr.neutral hS
    have hpre : ∀ p ∈ ps, NeutShape p := fun p hp =>
      ⟨hr.allIn_premises subClosed_neutralInt hS.1 p hp, (h1 p hp).1, (h1 p hp).2⟩
    have ihp := fun p hp => ih p hp (hpre p hp)
    have hL : Multiset.card c.L ≤ 1 := by
      by_cases hps0 : ps = []
      · exact h2 hps0
      · obtain ⟨p, hp, hle⟩ := h3 hps0
        exact hle.trans (ihp p hp).1
    exact ⟨hL, .mk ps c hr ⟨hS.1, hS.2.1, hS.2.2, hL⟩ fun p hp => (ihp p hp).2⟩

/-- **Theorem (§6), neutral intuitionistic fragment, cut-free version.** -/
theorem neutralInt_within {S : Sequent} (h : CutFreeProvable S) (hS : NeutralIntSeq S) :
    ProvableWithin .neutralIntuitionistic S :=
  (neutral_main h ⟨hS.1, hS.2.1, hS.2.2.1⟩).2

/-- In the neutral intuitionistic fragment, a cut-free provable sequent `Γ;Γ' ⊢ ;S` has at
most one formula in `Γ` (the "head variable"). -/
theorem neutral_headVariable {S : Sequent} (h : CutFreeProvable S)
    (hA : AllIn IsNeutralInt S) (hCR : S.CR = 0) (hR : Multiset.card S.R = 1) :
    Multiset.card S.L ≤ 1 :=
  (neutral_main h ⟨hA, hCR, hR⟩).1

end LU
