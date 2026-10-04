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

variable {n : ℕ}

open Formula

/-- Gentzen's sequent calculus LK (with weakening and contraction, without cut) for the
connectives of the classical fragment.  `LK Γ Δ` means `Γ ⊢ Δ`. -/
inductive LK : {n : ℕ} → Multiset (Formula n) → Multiset (Formula n) → Prop where
  | ax {n : ℕ} (A : Formula n) : LK {A} {A}
  | weakL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula n) : LK Γ Δ → LK (A ::ₘ Γ) Δ
  | weakR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula n) : LK Γ Δ → LK Γ (A ::ₘ Δ)
  | contrL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula n) : LK (A ::ₘ A ::ₘ Γ) Δ → LK (A ::ₘ Γ) Δ
  | contrR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula n) : LK Γ (A ::ₘ A ::ₘ Δ) → LK Γ (A ::ₘ Δ)
  | trueR {n : ℕ} : LK 0 {(one : Formula n)}
  | falseL {n : ℕ} (Γ Δ : Multiset (Formula n)) : LK (zero ::ₘ Γ) Δ
  | negL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula n) : LK Γ (A ::ₘ Δ) → LK (neg A ::ₘ Γ) Δ
  | negR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula n) : LK (A ::ₘ Γ) Δ → LK Γ (neg A ::ₘ Δ)
  | conjR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A B : Formula n) :
      LK Γ (A ::ₘ Δ) → LK Γ (B ::ₘ Δ) → LK Γ (conj A B ::ₘ Δ)
  | conjL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A B : Formula n) :
      LK (A ::ₘ B ::ₘ Γ) Δ → LK (conj A B ::ₘ Γ) Δ
  | disjR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A B : Formula n) :
      LK Γ (A ::ₘ B ::ₘ Δ) → LK Γ (disj A B ::ₘ Δ)
  | disjL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A B : Formula n) :
      LK (A ::ₘ Γ) Δ → LK (B ::ₘ Γ) Δ → LK (disj A B ::ₘ Γ) Δ
  | impR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A B : Formula n) :
      LK (A ::ₘ Γ) (B ::ₘ Δ) → LK Γ (imp A B ::ₘ Δ)
  | impL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A B : Formula n) :
      LK Γ (A ::ₘ Δ) → LK (B ::ₘ Γ) Δ → LK (imp A B ::ₘ Γ) Δ
  /-- `∀x`-right, with the eigenvariable condition expressed by weakening the context. -/
  | allR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula (n + 1)) :
      LK (sh Γ) (A ::ₘ sh Δ) → LK Γ (call A ::ₘ Δ)
  | allL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula (n + 1)) (t : Term n) :
      LK (A.inst t ::ₘ Γ) Δ → LK (call A ::ₘ Γ) Δ
  | exR {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula (n + 1)) (t : Term n) :
      LK Γ (A.inst t ::ₘ Δ) → LK Γ (cex A ::ₘ Δ)
  /-- `∃x`-left, with the eigenvariable condition expressed by weakening the context. -/
  | exL {n : ℕ} (Γ Δ : Multiset (Formula n)) (A : Formula (n + 1)) :
      LK (A ::ₘ sh Γ) (sh Δ) → LK (cex A ::ₘ Γ) Δ

namespace LK

theorem congr {Γ Γ' Δ Δ' : Multiset (Formula n)} (h : LK Γ Δ) (e1 : Γ = Γ') (e2 : Δ = Δ') :
    LK Γ' Δ' := e1 ▸ e2 ▸ h

theorem weakenL {Γ Δ : Multiset (Formula n)} (h : LK Γ Δ) : ∀ E, LK (E + Γ) Δ := by
  intro E
  induction E using Multiset.induction_on with
  | empty => simpa using h
  | cons A E ih => rw [Multiset.cons_add]; exact .weakL _ _ A ih

theorem weakenR {Γ Δ : Multiset (Formula n)} (h : LK Γ Δ) : ∀ E, LK Γ (E + Δ) := by
  intro E
  induction E using Multiset.induction_on with
  | empty => simpa using h
  | cons A E ih => rw [Multiset.cons_add]; exact .weakR _ _ A ih

/-- Weakening on both sides: `Γ ⊢ Δ` gives `Γ' ⊢ Δ'` whenever `Γ ≤ Γ'` and `Δ ≤ Δ'`. -/
theorem weaken {Γ Γ' Δ Δ' : Multiset (Formula n)} (h : LK Γ Δ) (h1 : Γ ≤ Γ') (h2 : Δ ≤ Δ') :
    LK Γ' Δ' := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 h1
  obtain ⟨F, rfl⟩ := Multiset.le_iff_exists_add.1 h2
  exact ((h.weakenL E).weakenR F).congr (add_comm _ _) (add_comm _ _)

/-- Contraction of a formula that already occurs in the left context. -/
theorem contrL_of_mem {Γ Δ : Multiset (Formula n)} {A : Formula n} (hA : A ∈ Γ)
    (h : LK (A ::ₘ Γ) Δ) : LK Γ Δ := by
  rw [← Multiset.cons_erase hA] at h ⊢
  exact .contrL _ _ A h

/-- Contraction of a formula that already occurs in the right context. -/
theorem contrR_of_mem {Γ Δ : Multiset (Formula n)} {A : Formula n} (hA : A ∈ Δ)
    (h : LK Γ (A ::ₘ Δ)) : LK Γ Δ := by
  rw [← Multiset.cons_erase hA] at h ⊢
  exact .contrR _ _ A h

/-- Moving a formula into a (left) central zone, with contraction if it is already there. -/
theorem insertL_of_cons {Γ Δ : Multiset (Formula n)} {C : Finset (Formula n)} {A : Formula n}
    (h : LK (A ::ₘ (Γ + C.val)) Δ) : LK (Γ + (insert A C).val) Δ := by
  by_cases hA : A ∈ C
  · rw [Finset.insert_eq_of_mem hA]
    exact contrL_of_mem (Multiset.mem_add.2 (Or.inr hA)) h
  · rw [Finset.insert_val_of_notMem hA, Multiset.add_cons]; exact h

/-- Moving a formula into a (right) central zone, with contraction if it is already there. -/
theorem insertR_of_cons {Γ Δ : Multiset (Formula n)} {C : Finset (Formula n)} {A : Formula n}
    (h : LK Γ (A ::ₘ (C.val + Δ))) : LK Γ ((insert A C).val + Δ) := by
  by_cases hA : A ∈ C
  · rw [Finset.insert_eq_of_mem hA]
    exact contrR_of_mem (Multiset.mem_add.2 (Or.inl hA)) h
  · rw [Finset.insert_val_of_notMem hA, Multiset.cons_add]; exact h

/-- Moving a formula out of a (left) central zone, with weakening if it remains there. -/
theorem cons_of_insertL {Γ Δ : Multiset (Formula n)} {C : Finset (Formula n)} {A : Formula n}
    (h : LK (Γ + (insert A C).val) Δ) : LK (A ::ₘ (Γ + C.val)) Δ := by
  by_cases hA : A ∈ C
  · rw [Finset.insert_eq_of_mem hA] at h; exact .weakL _ _ A h
  · rw [Finset.insert_val_of_notMem hA, Multiset.add_cons] at h; exact h

/-- Moving a formula out of a (right) central zone, with weakening if it remains there. -/
theorem cons_of_insertR {Γ Δ : Multiset (Formula n)} {C : Finset (Formula n)} {A : Formula n}
    (h : LK Γ ((insert A C).val + Δ)) : LK Γ (A ::ₘ (C.val + Δ)) := by
  by_cases hA : A ∈ C
  · rw [Finset.insert_eq_of_mem hA] at h; exact .weakR _ _ A h
  · rw [Finset.insert_val_of_notMem hA, Multiset.cons_add] at h; exact h

end LK

/-- Close an equation between multisets built from `+`, `::ₘ`, `{·}`, `0` and `sh`. -/
local macro "mset_tac" : tactic => `(tactic| ((try simp only [← Multiset.singleton_add,
  sh, shc_val, Finset.empty_val, Multiset.map_add, Multiset.map_singleton, Multiset.map_zero]) <;> abel))

/-- `Γ ≤ Δ` for multisets built from `+`, `::ₘ`, `{·}`, `0`, given the difference `E`. -/
local macro "mle_tac " E:term : tactic =>
  `(tactic| exact Multiset.le_iff_exists_add.2 ⟨$E, by mset_tac⟩)

theorem lk_of_cutFree_aux {S : Sequent n}
    (h : Derivable Rule (fun S => True ∧ AllIn IsClassical S) S) :
    LK (S.L + S.CL.val) (S.CR.val + S.R) := by
  induction h with
  | mk ps c hr hc hs hu ihs ihu =>
  have ih := Premise.forall_all (Q := fun s => LK (s.L + s.CL.val) (s.CR.val + s.R)) ihs ihu
  clear hs hu ihs ihu
  obtain ⟨-, hA⟩ := hc
  cases hr <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, Premise.all_same, Premise.all_up] at ih <;>
    (try simp only [allIn_mk, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.notMem_zero, or_imp, forall_and, forall_eq,
      IsEmpty.forall_iff, implies_true] at hA) <;>
    (try (simp only [IsClassical, false_and, and_false, true_and, and_true] at hA; done)) <;>
    dsimp only at ih ⊢
  case ax A => exact (LK.ax A).congr (by mset_tac) (by mset_tac)
  case weakR Γ Γ' Δ' Δ A => exact LK.insertR_of_cons (LK.weakR _ _ A ih)
  case weakL Γ Γ' Δ' Δ A => exact LK.insertL_of_cons (LK.weakL _ _ A ih)
  case inR Γ Γ' Δ' Δ A => exact LK.insertR_of_cons (ih.congr rfl (by mset_tac))
  case inL Γ Γ' Δ' Δ A => exact LK.insertL_of_cons (ih.congr (by mset_tac) rfl)
  case outR Γ Γ' Δ' Δ N _ => exact (LK.cons_of_insertR ih).congr rfl (by mset_tac)
  case outL Γ Γ' Δ' Δ P _ => exact (LK.cons_of_insertL ih).congr (by mset_tac) rfl
  case oneR => exact LK.trueR.congr (by mset_tac) (by mset_tac)
  case zeroL Γ Δ => exact (LK.falseL Γ Δ).congr (by mset_tac) (by mset_tac)
  case negL Γ Γ' Δ' Δ A =>
    exact (LK.negL (Γ + Γ'.val) (Δ'.val + Δ) A (ih.congr rfl (by mset_tac))).congr (by mset_tac) rfl
  case negR Γ Γ' Δ' Δ A =>
    exact (LK.negR (Γ + Γ'.val) (Δ'.val + Δ) A (ih.congr (by mset_tac) rfl)).congr rfl (by mset_tac)
  case conjR_PQ Γ Λ Γ' Δ' Δ Θ P Q _ _ =>
    exact (LK.conjR (Γ + Λ + Γ'.val) (Δ'.val + Δ + Θ) P Q
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr rfl (by mset_tac)
  case conjL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.conjL (Γ + Γ'.val) (Δ'.val + Δ) P Q (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjR_AQ Λ Γ' Δ' Θ A Q _ _ =>
    exact (LK.conjR (Λ + Γ'.val) (Δ'.val + Θ) A Q
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case conjL_AQ Γ Γ' Δ' Δ A Q _ _ =>
    exact (LK.conjL (Γ + Γ'.val) (Δ'.val + Δ) A Q
      ((LK.cons_of_insertL ih).congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjR_PB Γ Γ' Δ' Δ P B _ _ =>
    exact (LK.conjR (Γ + Γ'.val) (Δ'.val + Δ) P B
      (ih.1.congr rfl (by mset_tac))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr rfl (by mset_tac)
  case conjL_PB Γ Γ' Δ' Δ P B _ _ =>
    exact (LK.conjL (Γ + Γ'.val) (Δ'.val + Δ) P B
      ((LK.cons_of_insertL ih).congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjR_AB Γ Γ' Δ' Δ A B _ _ =>
    exact (LK.conjR (Γ + Γ'.val) (Δ'.val + Δ) A B (ih.1.congr rfl (by mset_tac))
      (ih.2.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case conjL_AB₁ Γ Γ' Δ' Δ A B _ _ =>
    exact (LK.conjL (Γ + Γ'.val) (Δ'.val + Δ) A B
      ((LK.weakL _ _ B ih).congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case conjL_AB₂ Γ Γ' Δ' Δ A B _ _ =>
    exact (LK.conjL (Γ + Γ'.val) (Δ'.val + Δ) A B
      ((LK.weakL _ _ A ih).congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case callR_A Γ Γ' Δ' Δ A _ =>
    exact (LK.allR (Γ + Γ'.val) (Δ'.val + Δ) A
      ((LK.cons_of_insertR ih).congr (by mset_tac) (by mset_tac))).congr rfl (by mset_tac)
  case callL_A Γ' Δ' A t _ =>
    exact (LK.allL Γ'.val Δ'.val A t (ih.congr (by mset_tac) (by mset_tac))).congr (by mset_tac)
      (by mset_tac)
  case callR_N Γ Γ' Δ' Δ N _ =>
    exact (LK.allR (Γ + Γ'.val) (Δ'.val + Δ) N (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case callL_N Γ Γ' Δ' Δ N t _ =>
    exact (LK.allL (Γ + Γ'.val) (Δ'.val + Δ) N t (ih.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case disjR₁_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.disjR (Γ + Γ'.val) (Δ'.val + Δ) P Q ((LK.weakR _ _ Q ih).congr rfl (by mset_tac))).congr
      rfl (by mset_tac)
  case disjR₂_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.disjR (Γ + Γ'.val) (Δ'.val + Δ) P Q ((LK.weakR _ _ P ih).congr rfl (by mset_tac))).congr
      rfl (by mset_tac)
  case disjL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.disjL (Γ + Γ'.val) (Δ'.val + Δ) P Q (ih.1.congr (by mset_tac) rfl)
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case disjR_MQ Γ Γ' Δ' Δ M Q _ _ =>
    exact (LK.disjR (Γ + Γ'.val) (Δ'.val + Δ) M Q
      ((LK.cons_of_insertR ih).congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case disjL_MQ Γ Γ' Δ' Δ M Q _ _ =>
    exact (LK.disjL (Γ + Γ'.val) (Δ'.val + Δ) M Q (ih.1.congr (by mset_tac) rfl)
      ((LK.cons_of_insertL ih.2).weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) rfl
  case disjR_PN Γ Γ' Δ' Δ P N _ _ =>
    exact (LK.disjR (Γ + Γ'.val) (Δ'.val + Δ) P N
      ((LK.cons_of_insertR ih).congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case disjL_PN Λ Γ' Δ' Θ P N _ _ =>
    exact (LK.disjL (Λ + Γ'.val) (Δ'.val + Θ) P N (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case disjR_MN Γ Γ' Δ' Δ M N _ _ =>
    exact (LK.disjR (Γ + Γ'.val) (Δ'.val + Δ) M N (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case disjL_MN Γ Λ Γ' Δ' Δ Θ M N _ _ =>
    exact (LK.disjL (Γ + Λ + Γ'.val) (Δ'.val + Δ + Θ) M N
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) (by mset_tac)
  case cexR_P Γ Γ' Δ' Δ P t _ =>
    exact (LK.exR (Γ + Γ'.val) (Δ'.val + Δ) P t (ih.congr rfl (by mset_tac))).congr rfl (by mset_tac)
  case cexL_P Λ Λ' Θ' Θ P _ =>
    exact (LK.exL (Λ + Λ'.val) (Θ'.val + Θ) P (ih.congr (by mset_tac) (by mset_tac))).congr
      (by mset_tac) rfl
  case cexR_A Γ' Δ' A t _ =>
    exact (LK.exR Γ'.val Δ'.val A t (ih.congr (by mset_tac) (by mset_tac))).congr (by mset_tac)
      (by mset_tac)
  case cexL_A Λ Λ' Θ' Θ A _ =>
    exact (LK.exL (Λ + Λ'.val) (Θ'.val + Θ) A
      ((LK.cons_of_insertL ih).congr (by mset_tac) (by mset_tac))).congr (by mset_tac) rfl
  case impR₁_NP Γ Γ' Δ' Δ N P _ _ =>
    exact (LK.impR (Γ + Γ'.val) (Δ'.val + Δ) N P ((LK.weakL _ _ N ih).congr rfl (by mset_tac))).congr
      rfl (by mset_tac)
  case impR₂_NP Γ Γ' Δ' Δ N P _ _ =>
    exact (LK.impR (Γ + Γ'.val) (Δ'.val + Δ) N P ((LK.weakR _ _ P ih).congr (by mset_tac) rfl)).congr
      rfl (by mset_tac)
  case impL_NP Γ Γ' Δ' Δ N P _ _ =>
    exact (LK.impL (Γ + Γ'.val) (Δ'.val + Δ) N P (ih.1.congr rfl (by mset_tac))
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case impR_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.impR (Γ + Γ'.val) (Δ'.val + Δ) P Q
      ((LK.cons_of_insertR ih).congr (by mset_tac) (by mset_tac))).congr rfl (by mset_tac)
  case impL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    exact (LK.impL (Γ + Γ'.val) (Δ'.val + Δ) P Q (ih.1.congr rfl (by mset_tac))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) rfl
  case impR_MN Γ Γ' Δ' Δ M N _ _ =>
    exact (LK.impR (Γ + Γ'.val) (Δ'.val + Δ) M N
      ((LK.cons_of_insertL ih).congr (by mset_tac) (by mset_tac))).congr rfl (by mset_tac)
  case impL_MN Λ Γ' Δ' Θ M N _ _ =>
    exact (LK.impL (Λ + Γ'.val) (Δ'.val + Θ) M N (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.congr (by mset_tac) rfl)).congr (by mset_tac) rfl
  case impR_PN Γ Γ' Δ' Δ P N _ _ =>
    exact (LK.impR (Γ + Γ'.val) (Δ'.val + Δ) P N (ih.congr (by mset_tac) (by mset_tac))).congr rfl
      (by mset_tac)
  case impL_PN Γ Λ Γ' Δ' Δ Θ P N _ _ =>
    exact (LK.impL (Γ + Λ + Γ'.val) (Δ'.val + Δ + Θ) P N
      (ih.1.weaken (by mle_tac Λ) (by mle_tac Θ))
      (ih.2.weaken (by mle_tac Γ) (by mle_tac Δ))).congr (by mset_tac) (by mset_tac)
  -- the remaining rules involve a neutral formula, which cannot be classical
  all_goals
    exfalso
    have hneu : ∀ {n : ℕ} (A : Formula n), A.IsClassical → A.pol ≠ .neu := fun A h => h.pol_ne_neu
    simp only [IsClassical] at hA
    rename_i h1 h2
    first
    | exact hneu _ (by tauto) h1
    | exact hneu _ (by tauto) h2

/-- **Soundness with respect to LK**: a cut-free provable LU sequent `Γ;Γ' ⊢ Δ';Δ` made of
classical formulas translates to an LK-provable sequent `Γ, Γ' ⊢ Δ', Δ`. -/
theorem LK.of_cutFreeProvable_classical {S : Sequent n} (h : CutFreeProvable S)
    (hS : AllIn IsClassical S) : LK (S.L + S.CL.val) (S.CR.val + S.R) :=
  lk_of_cutFree_aux (h.allIn subClosed_classical hS)

/-- Every sequent provable within the classical fragment translates to an LK-provable
sequent. -/
theorem LK.of_provableWithin_classical {S : Sequent n} (h : ProvableWithin .classical S) :
    LK (S.L + S.CL.val) (S.CR.val + S.R) :=
  LK.of_cutFreeProvable_classical h.cutFreeProvable (h.prop).1

/-- Every classical sequent provable in LU (cuts allowed) translates to an LK-provable
sequent, assuming cut elimination for LU. -/
theorem LK.of_provable_classical (hce : CutElimination) {S : Sequent n}
    (hS : AllIn IsClassical S) (h : Provable S) : LK (S.L + S.CL.val) (S.CR.val + S.R) :=
  LK.of_cutFreeProvable_classical (hce S h) hS

end LU
