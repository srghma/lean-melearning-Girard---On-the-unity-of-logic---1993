module

public import RequestProject.LU.LJ

/-!
# The classical fragment and Gentzen's LK (end of §6)

> The classical fragment translates not to LK, but to LC; more precisely besides the
> superficial difference one-sided/two sided, LC uses the semi-colon in a different way.

The calculus LC of Girard's *A new constructive logic: classical logic* is not formalized
here.  What we formalize is the underlying soundness statement with respect to ordinary
classical logic: under the translation `Γ;Γ' ⊢ Δ';Δ ↦ Γ, Γ' ⊢ Δ', Δ`, every rule of LU on
classical formulas is a derived rule of Gentzen's LK.  Hence:

* `LK.of_cutFreeProvable_classical`: a cut-free provable LU sequent made of classical
  formulas translates to an LK-provable sequent;
* `LK.of_provableWithin_classical`: in particular, so does every sequent provable within the
  classical fragment;
* `LK.of_provable_classical`: every provable classical sequent (cuts allowed) translates to
  an LK-provable sequent, assuming cut elimination for LU.
-/

@[expose] public section

namespace LU

open Formula

/-- Gentzen's sequent calculus LK (with weakening and contraction, without cut) for the
connectives of the classical fragment.  `LK Γ Δ` means `Γ ⊢ Δ`. -/
inductive LK : Multiset Formula → Multiset Formula → Prop where
  | ax (A : Formula) : LK {A} {A}
  | weakL (Γ Δ : Multiset Formula) (A : Formula) : LK Γ Δ → LK (A ::ₘ Γ) Δ
  | weakR (Γ Δ : Multiset Formula) (A : Formula) : LK Γ Δ → LK Γ (A ::ₘ Δ)
  | contrL (Γ Δ : Multiset Formula) (A : Formula) : LK (A ::ₘ A ::ₘ Γ) Δ → LK (A ::ₘ Γ) Δ
  | contrR (Γ Δ : Multiset Formula) (A : Formula) : LK Γ (A ::ₘ A ::ₘ Δ) → LK Γ (A ::ₘ Δ)
  | trueR : LK 0 {one}
  | falseL (Γ Δ : Multiset Formula) : LK (zero ::ₘ Γ) Δ
  | negL (Γ Δ : Multiset Formula) (A : Formula) : LK Γ (A ::ₘ Δ) → LK (neg A ::ₘ Γ) Δ
  | negR (Γ Δ : Multiset Formula) (A : Formula) : LK (A ::ₘ Γ) Δ → LK Γ (neg A ::ₘ Δ)
  | conjR (Γ Δ : Multiset Formula) (A B : Formula) :
      LK Γ (A ::ₘ Δ) → LK Γ (B ::ₘ Δ) → LK Γ (conj A B ::ₘ Δ)
  | conjL (Γ Δ : Multiset Formula) (A B : Formula) :
      LK (A ::ₘ B ::ₘ Γ) Δ → LK (conj A B ::ₘ Γ) Δ
  | disjR (Γ Δ : Multiset Formula) (A B : Formula) :
      LK Γ (A ::ₘ B ::ₘ Δ) → LK Γ (disj A B ::ₘ Δ)
  | disjL (Γ Δ : Multiset Formula) (A B : Formula) :
      LK (A ::ₘ Γ) Δ → LK (B ::ₘ Γ) Δ → LK (disj A B ::ₘ Γ) Δ
  | impR (Γ Δ : Multiset Formula) (A B : Formula) :
      LK (A ::ₘ Γ) (B ::ₘ Δ) → LK Γ (imp A B ::ₘ Δ)
  | impL (Γ Δ : Multiset Formula) (A B : Formula) :
      LK Γ (A ::ₘ Δ) → LK (B ::ₘ Γ) Δ → LK (imp A B ::ₘ Γ) Δ
  /-- `∀x`-right, with the eigenvariable condition expressed by shifting the context. -/
  | allR (Γ Δ : Multiset Formula) (A : Formula) :
      LK (sh Γ) (A ::ₘ sh Δ) → LK Γ (call A ::ₘ Δ)
  | allL (Γ Δ : Multiset Formula) (A : Formula) (t : Term) :
      LK (A.inst t ::ₘ Γ) Δ → LK (call A ::ₘ Γ) Δ
  | exR (Γ Δ : Multiset Formula) (A : Formula) (t : Term) :
      LK Γ (A.inst t ::ₘ Δ) → LK Γ (cex A ::ₘ Δ)
  /-- `∃x`-left, with the eigenvariable condition expressed by shifting the context. -/
  | exL (Γ Δ : Multiset Formula) (A : Formula) :
      LK (A ::ₘ sh Γ) (sh Δ) → LK (cex A ::ₘ Γ) Δ

namespace LK

theorem congr {Γ Γ' Δ Δ' : Multiset Formula} (h : LK Γ Δ) (e1 : Γ = Γ') (e2 : Δ = Δ') :
    LK Γ' Δ' := e1 ▸ e2 ▸ h

theorem weakenL {Γ Δ : Multiset Formula} (h : LK Γ Δ) : ∀ E, LK (E + Γ) Δ := by
  intro E
  induction E using Multiset.induction_on with
  | empty => simpa using h
  | cons A E ih => rw [Multiset.cons_add]; exact .weakL _ _ A ih

theorem weakenR {Γ Δ : Multiset Formula} (h : LK Γ Δ) : ∀ E, LK Γ (E + Δ) := by
  intro E
  induction E using Multiset.induction_on with
  | empty => simpa using h
  | cons A E ih => rw [Multiset.cons_add]; exact .weakR _ _ A ih

/-- Weakening on both sides: `Γ ⊢ Δ` gives `Γ' ⊢ Δ'` whenever `Γ ≤ Γ'` and `Δ ≤ Δ'`. -/
theorem weaken {Γ Γ' Δ Δ' : Multiset Formula} (h : LK Γ Δ) (h1 : Γ ≤ Γ') (h2 : Δ ≤ Δ') :
    LK Γ' Δ' := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 h1
  obtain ⟨F, rfl⟩ := Multiset.le_iff_exists_add.1 h2
  exact ((h.weakenL E).weakenR F).congr (add_comm _ _) (add_comm _ _)

end LK

/-- Close an equation between multisets built from `+`, `::ₘ`, `{·}`, `0` and `sh`. -/
local macro "mset_tac" : tactic => `(tactic| ((try simp only [← Multiset.singleton_add,
  sh, Multiset.map_add, Multiset.map_singleton, Multiset.map_zero]) <;> abel))

/-- `Γ ≤ Δ` for multisets built from `+`, `::ₘ`, `{·}`, `0`, given the difference `E`. -/
local macro "mle_tac " E:term : tactic =>
  `(tactic| exact Multiset.le_iff_exists_add.2 ⟨$E, by mset_tac⟩)

theorem lk_of_cutFree_aux {S : Sequent}
    (h : Derivable Rule (fun S => True ∧ AllIn IsClassical S) S) :
    LK (S.L + S.CL) (S.CR + S.R) := by
  induction h with
  | mk ps c hr hc hps ih =>
  clear hps
  obtain ⟨-, hA⟩ := hc
  cases hr <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true] at ih <;>
    (try simp only [allIn_mk, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.notMem_zero, or_imp, forall_and, forall_eq,
      IsEmpty.forall_iff, implies_true] at hA) <;>
    (try (simp only [IsClassical, false_and, and_false, true_and, and_true] at hA; done)) <;>
    dsimp only at ih ⊢
  case ax A => exact (LK.ax A).congr (by mset_tac) (by mset_tac)
  case weakR Γ Γ' Δ' Δ A => exact (LK.weakR _ _ A ih).congr rfl (by mset_tac)
  case weakL Γ Γ' Δ' Δ A => exact (LK.weakL _ _ A ih).congr (by mset_tac) rfl
  case contrR Γ Γ' Δ' Δ A =>
    exact (LK.contrR (Γ + Γ') (Δ' + Δ) A (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case contrL Γ Γ' Δ' Δ A =>
    exact (LK.contrL (Γ + Γ') (Δ' + Δ) A (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case inR Γ Γ' Δ' Δ A => exact ih.congr rfl (by mset_tac)
  case inL Γ Γ' Δ' Δ A => exact ih.congr (by mset_tac) rfl
  case outR Γ Γ' Δ' Δ N _ => exact ih.congr rfl (by mset_tac)
  case outL Γ Γ' Δ' Δ P _ => exact ih.congr (by mset_tac) rfl
  case oneR => exact LK.trueR.congr (by mset_tac) (by mset_tac)
  case zeroL Γ Δ => exact (LK.falseL Γ Δ).congr (by mset_tac) (by mset_tac)
  case negL Γ Γ' Δ' Δ A =>
    exact (LK.negL (Γ + Γ') (Δ' + Δ) A (ih.congr rfl (by mset_tac))).congr (by mset_tac) rfl
  case negR Γ Γ' Δ' Δ A =>
    exact (LK.negR (Γ + Γ') (Δ' + Δ) A (ih.congr (by mset_tac) rfl)).congr rfl (by mset_tac)
  case conjR_PQ Γ Λ Γ' Δ' Δ Θ P Q _ _ =>
    exact (LK.conjR (Γ + Λ + Γ') (Δ' + Δ + Θ) P Q
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr rfl (by mset_tac)
  case conjL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.conjL (Γ + Γ') (Δ' + Δ) P Q (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjR_AQ Λ Γ' Δ' Θ A Q _ _ =>
    exact (LK.conjR (Λ + Γ') (Δ' + Θ) A Q
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case conjL_AQ Γ Γ' Δ' Δ A Q _ _ =>
    exact (LK.conjL (Γ + Γ') (Δ' + Δ) A Q (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjR_PB Γ Γ' Δ' Δ P B _ _ =>
    exact (LK.conjR (Γ + Γ') (Δ' + Δ) P B
      (ih.1.congr rfl (by mset_tac))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr rfl (by mset_tac)
  case conjL_PB Γ Γ' Δ' Δ P B _ _ =>
    exact (LK.conjL (Γ + Γ') (Δ' + Δ) P B (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjR_AB Γ Γ' Δ' Δ A B _ _ =>
    exact (LK.conjR (Γ + Γ') (Δ' + Δ) A B (ih.1.congr rfl (by mset_tac))
      (ih.2.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case conjL_AB₁ Γ Γ' Δ' Δ A B _ _ =>
    exact (LK.conjL (Γ + Γ') (Δ' + Δ) A B
      ((LK.weakL _ _ B ih).congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjL_AB₂ Γ Γ' Δ' Δ A B _ _ =>
    exact (LK.conjL (Γ + Γ') (Δ' + Δ) A B
      ((LK.weakL _ _ A ih).congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case callR_A Γ Γ' Δ' Δ A _ =>
    exact (LK.allR (Γ + Γ') (Δ' + Δ) A (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case callL_A Γ' Δ' A t _ =>
    exact (LK.allL Γ' Δ' A t (ih.congr (by mset_tac) (by mset_tac))).congr (by mset_tac)
      (by mset_tac)
  case callR_N Γ Γ' Δ' Δ N _ =>
    exact (LK.allR (Γ + Γ') (Δ' + Δ) N (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case callL_N Γ Γ' Δ' Δ N t _ =>
    exact (LK.allL (Γ + Γ') (Δ' + Δ) N t (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case disjR₁_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.disjR (Γ + Γ') (Δ' + Δ) P Q ((LK.weakR _ _ Q ih).congr rfl (by mset_tac))).congr
      rfl (by mset_tac)
  case disjR₂_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.disjR (Γ + Γ') (Δ' + Δ) P Q ((LK.weakR _ _ P ih).congr rfl (by mset_tac))).congr
      rfl (by mset_tac)
  case disjL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.disjL (Γ + Γ') (Δ' + Δ) P Q (ih.1.congr (by mset_tac) rfl)
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case disjR_MQ Γ Γ' Δ' Δ M Q _ _ =>
    exact (LK.disjR (Γ + Γ') (Δ' + Δ) M Q (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case disjL_MQ Γ Γ' Δ' Δ M Q _ _ =>
    exact (LK.disjL (Γ + Γ') (Δ' + Δ) M Q (ih.1.congr (by mset_tac) rfl)
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) rfl
  case disjR_PN Γ Γ' Δ' Δ P N _ _ =>
    exact (LK.disjR (Γ + Γ') (Δ' + Δ) P N (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case disjL_PN Λ Γ' Δ' Θ P N _ _ =>
    exact (LK.disjL (Λ + Γ') (Δ' + Θ) P N (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case disjR_MN Γ Γ' Δ' Δ M N _ _ =>
    exact (LK.disjR (Γ + Γ') (Δ' + Δ) M N (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case disjL_MN Γ Λ Γ' Δ' Δ Θ M N _ _ =>
    exact (LK.disjL (Γ + Λ + Γ') (Δ' + Δ + Θ) M N
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) (by mset_tac)
  case cexR_P Γ Γ' Δ' Δ P t _ =>
    exact (LK.exR (Γ + Γ') (Δ' + Δ) P t (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case cexL_P Λ Λ' Θ' Θ P _ =>
    exact (LK.exL (Λ + Λ') (Θ' + Θ) P (ih.congr (by mset_tac) (by mset_tac))).congr
      (by mset_tac) rfl
  case cexR_A Γ' Δ' A t _ =>
    exact (LK.exR Γ' Δ' A t (ih.congr (by mset_tac) (by mset_tac))).congr (by mset_tac)
      (by mset_tac)
  case cexL_A Λ Λ' Θ' Θ A _ =>
    exact (LK.exL (Λ + Λ') (Θ' + Θ) A (ih.congr (by mset_tac) (by mset_tac))).congr
      (by mset_tac) rfl
  case impR₁_NP Γ Γ' Δ' Δ N P _ _ =>
    exact (LK.impR (Γ + Γ') (Δ' + Δ) N P ((LK.weakL _ _ N ih).congr rfl (by mset_tac))).congr
      rfl (by mset_tac)
  case impR₂_NP Γ Γ' Δ' Δ N P _ _ =>
    exact (LK.impR (Γ + Γ') (Δ' + Δ) N P ((LK.weakR _ _ P ih).congr (by mset_tac) rfl)).congr
      rfl (by mset_tac)
  case impL_NP Γ Γ' Δ' Δ N P _ _ =>
    exact (LK.impL (Γ + Γ') (Δ' + Δ) N P (ih.1.congr rfl (by mset_tac))
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case impR_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.impR (Γ + Γ') (Δ' + Δ) P Q (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case impL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.impL (Γ + Γ') (Δ' + Δ) P Q (ih.1.congr rfl (by mset_tac))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) rfl
  case impR_MN Γ Γ' Δ' Δ M N _ _ =>
    exact (LK.impR (Γ + Γ') (Δ' + Δ) M N (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case impL_MN Λ Γ' Δ' Θ M N _ _ =>
    exact (LK.impL (Λ + Γ') (Δ' + Θ) M N (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case impR_PN Γ Γ' Δ' Δ P N _ _ =>
    exact (LK.impR (Γ + Γ') (Δ' + Δ) P N (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case impL_PN Γ Λ Γ' Δ' Δ Θ P N _ _ =>
    exact (LK.impL (Γ + Λ + Γ') (Δ' + Δ + Θ) P N
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) (by mset_tac)
  -- the remaining rules involve a neutral formula, which cannot be classical
  all_goals
    exfalso
    have hneu : ∀ A : Formula, A.IsClassical → A.pol ≠ .neu := fun A h => h.pol_ne_neu
    simp only [IsClassical] at hA
    rename_i h1 h2
    first
    | exact hneu _ (by tauto) h1
    | exact hneu _ (by tauto) h2

/-- **Soundness with respect to LK**: a cut-free provable LU sequent `Γ;Γ' ⊢ Δ';Δ` made of
classical formulas translates to an LK-provable sequent `Γ, Γ' ⊢ Δ', Δ`. -/
theorem LK.of_cutFreeProvable_classical {S : Sequent} (h : CutFreeProvable S)
    (hS : AllIn IsClassical S) : LK (S.L + S.CL) (S.CR + S.R) :=
  lk_of_cutFree_aux (h.allIn subClosed_classical hS)

/-- Every sequent provable within the classical fragment translates to an LK-provable
sequent. -/
theorem LK.of_provableWithin_classical {S : Sequent} (h : ProvableWithin .classical S) :
    LK (S.L + S.CL) (S.CR + S.R) :=
  LK.of_cutFreeProvable_classical h.cutFreeProvable (h.prop).1

/-- Every classical sequent provable in LU (cuts allowed) translates to an LK-provable
sequent, assuming cut elimination for LU. -/
theorem LK.of_provable_classical (hce : CutElimination) {S : Sequent}
    (hS : AllIn IsClassical S) (h : Provable S) : LK (S.L + S.CL) (S.CR + S.R) :=
  LK.of_cutFreeProvable_classical (hce S h) hS

end LU
