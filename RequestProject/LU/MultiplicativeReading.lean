module

public import RequestProject.LU.MainTheorem

/-!
# On the left rule for `N ⇒ P` (Fig. 3)

The scanned paper prints the left rule for the classical implication `N ⇒ P` as

  `Γ;Γ' ⊢ Δ';Δ,N    Q,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ;Π`

(with typos), i.e. as the *multiplicative* rule

  `Γ;Γ' ⊢ Δ';Δ,N    P,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ,Π`.

The formalization (`Rule.impL_NP`) uses instead the *additive* rule
`Γ;Γ' ⊢ Δ';Δ,N    P,Γ;Γ' ⊢ Δ';Δ  /  N⇒P,Γ;Γ' ⊢ Δ';Δ`, i.e. the left rule of `N⊥ ⊕ P`
(Table 3).  This is a deliberate departure from the printed Fig. 3, made to preserve the
Theorem of §6.

This file records why the multiplicative reading is incompatible with the proof of the
theorem of §6 for the classical fragment.  That proof says that for every rule with
classical formulas and a conclusion `S` with `μ(S) > 1` there is a premise `S'` with
`μ(S') ≥ μ(S)`, the axiom `F, Γ; ⊢ ; Δ` being the only exception.  The instance of the
multiplicative rule below has two cut-free provable premises made of classical formulas,
each with `μ = 1`, and a conclusion with `μ = 2`.

With `q, q'` positive atoms the instance is

  `; ⊢ ; ¬q, q     q', ¬q'; ⊢ ;  /  ¬q⇒q', ¬q'; ⊢ ; q`.
-/

@[expose] public section

namespace LU

open Formula

/-- A positive nullary atom `q` (a closed formula). -/
def atQ : Formula 0 := atom ⟨0, 0, .pos⟩ Fin.elim0

/-- A second positive nullary atom `q'` (a closed formula). -/
def atQ' : Formula 0 := atom ⟨1, 0, .pos⟩ Fin.elim0

/-- Left premise `; ⊢ ; ¬q, q`. -/
def multPrem1 : Sequent 0 := ⟪0 ; ∅ ⊢ ∅ ; neg atQ ::ₘ {atQ}⟫

/-- Right premise `q', ¬q' ; ⊢ ;` (with `P = q'`, `Λ = ¬q'`; as a multiset,
`¬q' ::ₘ {q'} = q' ::ₘ {¬q'}`). -/
def multPrem2 : Sequent 0 := ⟪neg atQ' ::ₘ {atQ'} ; ∅ ⊢ ∅ ; 0⟫

/-- Conclusion of the multiplicative reading: `¬q ⇒ q', ¬q' ; ⊢ ; q`. -/
def multConcl : Sequent 0 := ⟪imp (neg atQ) atQ' ::ₘ (0 + {neg atQ'}) ; ∅ ⊢ ∅ ; {atQ} + 0⟫

/-- With the multiplicative reading, the paper's invariant for the classical fragment fails:
both premises are cut-free provable, consist of classical formulas and have `μ = 1`, and
the conclusion has `μ = 2`. -/
theorem multiplicative_impL_NP_breaks_mu :
    CutFreeProvable multPrem1 ∧ CutFreeProvable multPrem2 ∧
    AllIn IsClassical multPrem1 ∧ AllIn IsClassical multPrem2 ∧ AllIn IsClassical multConcl ∧
    (neg atQ).pol = .neg ∧ atQ'.pol = .pos ∧
    mu multPrem1 = 1 ∧ mu multPrem2 = 1 ∧ mu multConcl = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · refine .mk' _ _ (Rule.negR 0 ∅ ∅ {atQ} atQ) trivial ?_
    simp only [List.mem_singleton, forall_eq]
    exact .mk' _ _ (Rule.ax atQ) trivial (by simp)
  · refine .mk' _ _ (Rule.negL {atQ'} ∅ ∅ 0 atQ') trivial ?_
    simp only [List.mem_singleton, forall_eq]
    exact .mk' _ _ (Rule.ax atQ') trivial (by simp)
  all_goals
    simp [multPrem1, multPrem2, multConcl, AllIn, Sequent.formulas, IsClassical, atQ, atQ',
      mu, Multiset.filter_singleton, pol, Pol.dual, Pol.imp]

end LU
