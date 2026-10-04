module

public import RequestProject.LU.MainTheorem

/-!
# Comparison of the intuitionistic fragments with LJ (end of §6)

> Now, it remains to compare the systems LU restricted to various fragments with the sequent
> calculi for the corresponding logics:
> 1. The two intuitionistic fragments are OK: just translate `Γ;Γ' ⊢ ;A` as `Γ,Γ' ⊢ A` and
>    observe that all rules are correct.  The other way around might be slightly more
>    delicate at least if we investigate cut-free provability.

We define Gentzen's intuitionistic sequent calculus `LJ` for the connectives of the
intuitionistic fragment (`V = 1`, `F = 0`, `∧`, `∨`, `⊃`, `⋀x`, `∃x`, atoms), and prove:

* `LJ.of_provableWithin_intuitionistic`: if `Γ;Γ' ⊢ ;A` is provable within the
  intuitionistic fragment, then `Γ, Γ' ⊢ A` is provable in LJ (the translation is sound,
  "all rules are correct");
* `LJ.of_provableWithin_neutralInt`: the same for the neutral intuitionistic fragment;
* `LJ.of_provable_intuitionistic`: combined with the Theorem of §6, every provable
  intuitionistic sequent of LU translates to an LJ-provable sequent, assuming cut
  elimination for LU (passed as a hypothesis, like the Theorem with cuts);
* `LJ.provable`: the other way around, an LJ-provable sequent `Γ ⊢ C` of intuitionistic
  formulas is provable in LU as `;Γ ⊢ ;C` (with all hypotheses in the central zone).  This
  direction uses cuts, against the "projections" `A ∧ B; ⊢ ;A`, `⋀x A; ⊢ ;A[t/x]` and
  `A ⊃ B; Γ ⊢ ;B`; as the paper warns, cut-free provability is more delicate.
-/

@[expose] public section

namespace LU

open Formula

/-- Gentzen's sequent calculus LJ (with weakening and contraction, without cut) for the
connectives of the intuitionistic fragment.  `LJ Γ C` means `Γ ⊢ C`. -/
inductive LJ : Multiset Formula → Formula → Prop where
  | ax (A : Formula) : LJ {A} A
  | weak {Γ : Multiset Formula} {C : Formula} (A : Formula) : LJ Γ C → LJ (A ::ₘ Γ) C
  | contr {Γ : Multiset Formula} {C : Formula} (A : Formula) :
      LJ (A ::ₘ A ::ₘ Γ) C → LJ (A ::ₘ Γ) C
  | trueR : LJ 0 one
  | falseL (Γ : Multiset Formula) (C : Formula) : LJ (zero ::ₘ Γ) C
  | conjR {Γ : Multiset Formula} {A B : Formula} : LJ Γ A → LJ Γ B → LJ Γ (conj A B)
  | conjL {Γ : Multiset Formula} {A B C : Formula} :
      LJ (A ::ₘ B ::ₘ Γ) C → LJ (conj A B ::ₘ Γ) C
  | disjR₁ {Γ : Multiset Formula} {A B : Formula} : LJ Γ A → LJ Γ (disj A B)
  | disjR₂ {Γ : Multiset Formula} {A B : Formula} : LJ Γ B → LJ Γ (disj A B)
  | disjL {Γ : Multiset Formula} {A B C : Formula} :
      LJ (A ::ₘ Γ) C → LJ (B ::ₘ Γ) C → LJ (disj A B ::ₘ Γ) C
  | iimpR {Γ : Multiset Formula} {A B : Formula} : LJ (A ::ₘ Γ) B → LJ Γ (iimp A B)
  | iimpL {Γ : Multiset Formula} {A B C : Formula} :
      LJ Γ A → LJ (B ::ₘ Γ) C → LJ (iimp A B ::ₘ Γ) C
  /-- `⋀x`-right, with the eigenvariable condition expressed by shifting the context. -/
  | allR {Γ : Multiset Formula} {A : Formula} : LJ (sh Γ) A → LJ Γ (lall A)
  | allL {Γ : Multiset Formula} {A C : Formula} (t : Term) :
      LJ (A.inst t ::ₘ Γ) C → LJ (lall A ::ₘ Γ) C
  | exR {Γ : Multiset Formula} {A : Formula} (t : Term) : LJ Γ (A.inst t) → LJ Γ (cex A)
  /-- `∃x`-left, with the eigenvariable condition expressed by shifting the context. -/
  | exL {Γ : Multiset Formula} {A C : Formula} : LJ (A ::ₘ sh Γ) C.shift → LJ (cex A ::ₘ Γ) C

namespace LJ

theorem weaken {Γ : Multiset Formula} {C : Formula} (h : LJ Γ C) :
    ∀ Δ : Multiset Formula, LJ (Γ + Δ) C := by
  intro Δ
  induction Δ using Multiset.induction_on with
  | empty => simpa using h
  | cons A Δ ih => rw [Multiset.add_cons]; exact ih.weak A

theorem weaken_le {Γ Δ : Multiset Formula} {C : Formula} (h : LJ Γ C) (hle : Γ ≤ Δ) :
    LJ Δ C := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 hle
  exact h.weaken E

theorem congr {Γ Δ : Multiset Formula} {C : Formula} (h : LJ Γ C) (e : Γ = Δ) : LJ Δ C :=
  e ▸ h

end LJ

/-- Close an equation between multisets built from `+`, `::ₘ`, `{·}`, `0` and `sh`. -/
local macro "mset_tac" : tactic => `(tactic| ((try simp only [← Multiset.singleton_add,
  sh, Multiset.map_add, Multiset.map_singleton, Multiset.map_zero]) <;> abel))

theorem Derivable.prop {R : List Sequent → Sequent → Prop} {P : Sequent → Prop} {S : Sequent}
    (h : Derivable R P S) : P S := by
  cases h; assumption

theorem ljWithin_aux {S : Sequent} (h : ProvableWithin .intuitionistic S) :
    ∀ C ∈ S.R, LJ (S.L + S.CL) C := by
  induction h with
  | mk ps c hr hc hps ih =>
  have hP : ∀ p ∈ ps, IntSeq p := fun p hp => (hps p hp).prop
  clear hps
  change IntSeq c at hc
  cases hr <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true] at ih hP <;>
    obtain ⟨hA, hCR, hcard⟩ := hc <;>
    (try simp only [allIn_mk, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.notMem_zero, or_imp, forall_and, forall_eq,
      IsEmpty.forall_iff, implies_true] at hA) <;>
    (try (simp only [IsIntuitionistic, false_and, and_false, true_and, and_true] at hA; done)) <;>
    (try (simp at hCR; done)) <;>
    (try (simp [IntSeq] at hP; done)) <;>
    dsimp only at ih hP hCR hcard ⊢
  case ax A =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC; simpa using LJ.ax C
  case weakL Γ Γ' Δ' Δ A =>
    intro C hC; exact ((ih C hC).weak A).congr (by mset_tac)
  case contrL Γ Γ' Δ' Δ A =>
    intro C hC; exact (LJ.contr (Γ := Γ + Γ') A ((ih C hC).congr (by mset_tac))).congr (by mset_tac)
  case inL Γ Γ' Δ' Δ A =>
    intro C hC; exact (ih C hC).congr (by mset_tac)
  case outL Γ Γ' Δ' Δ P _ =>
    intro C hC; exact (ih C hC).congr (by mset_tac)
  case oneR =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC; simpa using LJ.trueR
  case zeroL Γ Δ =>
    intro C _; simpa using LJ.falseL Γ C
  case lallR Γ Γ' Δ' Δ A =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.allR (Γ := Γ + Γ') ((ih A (Multiset.mem_cons_self _ _)).congr (by mset_tac))
  case lallL Γ Γ' Δ' Δ A t =>
    intro C hC; exact (LJ.allL (Γ := Γ + Γ') (A := A) t ((ih C hC).congr (by mset_tac))).congr (by mset_tac)
  case conjR_PQ Γ Λ Γ' Δ' Δ Θ P Q _ _ =>
    obtain ⟨rfl, rfl⟩ : Δ = 0 ∧ Θ = 0 := by simpa using hcard
    intro C hC; rw [add_zero] at hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.conjR
      ((ih.1 P (Multiset.mem_cons_self _ _)).weaken_le
        (Multiset.le_iff_exists_add.2 ⟨Λ, by mset_tac⟩))
      ((ih.2 Q (Multiset.mem_cons_self _ _)).weaken_le
        (Multiset.le_iff_exists_add.2 ⟨Γ, by mset_tac⟩))
  case conjL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    intro C hC; exact (LJ.conjL (Γ := Γ + Γ') (A := P) (B := Q) ((ih C hC).congr (by mset_tac))).congr (by mset_tac)
  case conjR_AQ Λ Γ' Δ' Θ A Q _ _ =>
    obtain rfl : Θ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.conjR
      ((ih.1 A (Multiset.mem_singleton_self _)).weaken_le (Multiset.le_iff_exists_add.2 ⟨Λ, by mset_tac⟩))
      (ih.2 Q (Multiset.mem_cons_self _ _))
  case conjL_AQ Γ Γ' Δ' Δ A Q _ _ =>
    intro C hC
    exact (LJ.conjL (Γ := Γ + Γ') (A := A) (B := Q) ((ih C hC).congr (by mset_tac))).congr (by mset_tac)
  case conjR_PB Γ Γ' Δ' Δ P B _ _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.conjR (ih.1 P (Multiset.mem_cons_self _ _))
      ((ih.2 B (Multiset.mem_singleton_self _)).weaken_le (Multiset.le_iff_exists_add.2 ⟨Γ, by mset_tac⟩))
  case conjL_PB Γ Γ' Δ' Δ P B _ _ =>
    intro C hC
    exact (LJ.conjL (Γ := Γ + Γ') (A := P) (B := B) ((ih C hC).congr (by mset_tac))).congr (by mset_tac)
  case conjR_AB Γ Γ' Δ' Δ A B _ _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.conjR (ih.1 A (Multiset.mem_cons_self _ _)) (ih.2 B (Multiset.mem_cons_self _ _))
  case conjL_AB₁ Γ Γ' Δ' Δ A B _ _ =>
    intro C hC
    exact (LJ.conjL (Γ := Γ + Γ') (A := A) (B := B) (((ih C hC).weak B).congr
      (by mset_tac))).congr (by mset_tac)
  case conjL_AB₂ Γ Γ' Δ' Δ A B _ _ =>
    intro C hC
    exact (LJ.conjL (Γ := Γ + Γ') (A := A) (B := B) (((ih C hC).weak A).congr (by mset_tac))).congr (by mset_tac)
  case iimpR_P Γ Γ' Δ' Δ P B _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.iimpR (Γ := Γ + Γ') (A := P) ((ih B (Multiset.mem_cons_self _ _)).congr (by mset_tac))
  case iimpL_P Γ Λ Γ' Δ' Δ Θ P B _ =>
    obtain rfl : Δ = 0 := by simpa [IntSeq] using hP.1.2.2
    intro C hC; rw [zero_add] at hC
    refine (LJ.iimpL (Γ := Γ + Λ + Γ')
      ((ih.1 P (Multiset.mem_cons_self _ _)).weaken_le
        (Multiset.le_iff_exists_add.2 ⟨Λ, by mset_tac⟩))
      ((ih.2 C hC).weaken_le (Multiset.le_iff_exists_add.2 ⟨Γ, by mset_tac⟩))).congr
      (by mset_tac)
  case iimpR_A Γ Γ' Δ' Δ A B _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.iimpR (Γ := Γ + Γ') (A := A) ((ih B (Multiset.mem_cons_self _ _)).congr (by mset_tac))
  case iimpL_A Λ Γ' Δ' Θ A B _ =>
    intro C hC
    exact (LJ.iimpL (Γ := Λ + Γ')
      ((ih.1 A (Multiset.mem_singleton_self _)).weaken_le (Multiset.le_iff_exists_add.2 ⟨Λ, by mset_tac⟩))
      ((ih.2 C hC).congr (by mset_tac))).congr (by mset_tac)
  case disjR₁_PQ Γ Γ' Δ' Δ P Q _ _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₁ (ih P (Multiset.mem_cons_self _ _))
  case disjR₂_PQ Γ Γ' Δ' Δ P Q _ _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₂ (ih Q (Multiset.mem_cons_self _ _))
  case disjL_PQ Γ Γ' Δ' Δ P Q _ _ =>
    intro C hC
    exact (LJ.disjL (Γ := Γ + Γ') (A := P) (B := Q) ((ih.1 C hC).congr (by mset_tac)) ((ih.2 C hC).congr (by mset_tac))).congr (by mset_tac)
  case disjR₁_SQ Γ' Δ' S Q _ _ =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₁ (ih S (Multiset.mem_singleton_self _))
  case disjR₂_SQ Γ Γ' Δ' Δ S Q _ _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₂ (ih Q (Multiset.mem_cons_self _ _))
  case disjL_SQ Γ Γ' Δ' Δ S Q _ _ =>
    intro C hC
    exact (LJ.disjL (Γ := Γ + Γ') (A := S) (B := Q) ((ih.1 C hC).congr (by mset_tac))
      ((ih.2 C hC).congr (by mset_tac))).congr (by mset_tac)
  case disjR₁_PT Γ Γ' Δ' Δ P T _ _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₁ (ih P (Multiset.mem_cons_self _ _))
  case disjR₂_PT Γ' Δ' P T _ _ =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₂ (ih T (Multiset.mem_singleton_self _))
  case disjL_PT Γ Γ' Δ' Δ P T _ _ =>
    intro C hC
    exact (LJ.disjL (Γ := Γ + Γ') (A := P) (B := T) ((ih.1 C hC).congr (by mset_tac))
      ((ih.2 C hC).congr (by mset_tac))).congr (by mset_tac)
  case disjR₁_ST Γ' Δ' S T _ _ =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₁ (ih S (Multiset.mem_singleton_self _))
  case disjR₂_ST Γ' Δ' S T _ _ =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.disjR₂ (ih T (Multiset.mem_singleton_self _))
  case disjL_ST Γ Γ' Δ' Δ S T _ _ =>
    intro C hC
    exact (LJ.disjL (Γ := Γ + Γ') (A := S) (B := T) ((ih.1 C hC).congr (by mset_tac))
      ((ih.2 C hC).congr (by mset_tac))).congr (by mset_tac)
  case disjR₁_MT Γ Γ' Δ' Δ M T hM _ =>
    exact absurd hM (IsIntuitionistic.pol_ne_neg (by simp_all [IsIntuitionistic]))
  case disjR₂_SN Γ Γ' Δ' Δ S N _ hN =>
    exact absurd hN (IsIntuitionistic.pol_ne_neg (by simp_all [IsIntuitionistic]))
  case disjL_MN Γ Λ Γ' Δ' Δ Θ M N hM _ =>
    exact absurd hM (IsIntuitionistic.pol_ne_neg (by simp_all [IsIntuitionistic]))
  case cexR_P Γ Γ' Δ' Δ P t _ =>
    obtain rfl : Δ = 0 := by simpa using hcard
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.exR t (ih _ (Multiset.mem_cons_self _ _))
  case cexL_P Λ Λ' Θ' Θ P _ =>
    intro C hC
    exact (LJ.exL (Γ := Λ + Λ') (A := P) ((ih C.shift (Multiset.mem_map_of_mem _ hC)).congr (by mset_tac))).congr (by mset_tac)
  case cexR_A Γ' Δ' A t _ =>
    intro C hC; replace hC := Multiset.mem_singleton.1 hC; subst hC
    exact LJ.exR t (ih _ (Multiset.mem_singleton_self _))
  case cexL_A Λ Λ' Θ' Θ A _ =>
    intro C hC
    exact (LJ.exL (Γ := Λ + Λ') (A := A) ((ih C.shift (Multiset.mem_map_of_mem _ hC)).congr (by mset_tac))).congr (by mset_tac)

/-- **Soundness of the translation `Γ;Γ' ⊢ ;A ↦ Γ, Γ' ⊢ A`** (end of §6, item 1): a sequent
provable within the intuitionistic fragment translates to an LJ-provable sequent. -/
theorem LJ.of_provableWithin_intuitionistic {Γ Γ' : Multiset Formula} {A : Formula}
    (h : ProvableWithin .intuitionistic ⟪Γ ; Γ' ⊢ 0 ; {A}⟫) : LJ (Γ + Γ') A :=
  ljWithin_aux h A (Multiset.mem_singleton_self _)

theorem Formula.IsNeutralInt.isIntuitionistic {A : Formula} (h : A.IsNeutralInt) :
    A.IsIntuitionistic := by
  induction A with
  | atom p ts => simp_all [IsNeutralInt, IsIntuitionistic]
  | conj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | iimp A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | lall A ihA => exact ihA h
  | _ => exact h.elim

/-- The same for the neutral intuitionistic fragment. -/
theorem LJ.of_provableWithin_neutralInt {Γ Γ' : Multiset Formula} {A : Formula}
    (h : ProvableWithin .neutralIntuitionistic ⟪Γ ; Γ' ⊢ 0 ; {A}⟫) : LJ (Γ + Γ') A := by
  refine LJ.of_provableWithin_intuitionistic (h.mono (fun _ _ h => h) fun S hS => ?_)
  exact ⟨fun B hB => (hS.1 B hB).isIntuitionistic, hS.2.1, hS.2.2.1⟩

/-- Every intuitionistic sequent provable in LU (cuts allowed) translates to an LJ-provable
sequent, assuming cut elimination for LU (as the Theorem of §6 with cuts does). -/
theorem LJ.of_provable_intuitionistic (hce : CutElimination) {Γ Γ' : Multiset Formula}
    {A : Formula} (hS : IntSeq ⟪Γ ; Γ' ⊢ 0 ; {A}⟫) (h : Provable ⟪Γ ; Γ' ⊢ 0 ; {A}⟫) :
    LJ (Γ + Γ') A :=
  LJ.of_provableWithin_intuitionistic
    (fragment_theorem_of_cutElimination hce .intuitionistic hS h)

/-! ## The other way around: from LJ to LU -/

theorem Provable.rule {ps : List Sequent} {c : Sequent} (hr : Rule ps c)
    (h : ∀ p ∈ ps, Provable p) : Provable c :=
  .mk ps c (Or.inl hr) trivial h

theorem Provable.cutRule {ps : List Sequent} {c : Sequent} (hr : CutRule ps c)
    (h : ∀ p ∈ ps, Provable p) : Provable c :=
  .mk ps c (Or.inr hr) trivial h

theorem Provable.rule1 {p c : Sequent} (hr : Rule [p] c) (h : Provable p) : Provable c :=
  Provable.rule hr (by simpa using h)

theorem Provable.rule2 {p q c : Sequent} (hr : Rule [p, q] c) (hp : Provable p)
    (hq : Provable q) : Provable c :=
  Provable.rule hr (by simp [hp, hq])

theorem Provable.congr {S T : Sequent} (h : Provable S) (e : S = T) : Provable T := e ▸ h

/-- Weakening in the left central zone by a whole multiset. -/
theorem Provable.weakCL {Γ Γ' Δ' Δ : Multiset Formula} (h : Provable ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫) :
    ∀ E : Multiset Formula, Provable ⟪Γ ; E + Γ' ⊢ Δ' ; Δ⟫ := by
  intro E
  induction E using Multiset.induction_on with
  | empty => simpa using h
  | cons A E ih => rw [Multiset.cons_add]; exact .rule1 (Rule.weakL _ _ _ _ A) ih

theorem Provable.weakCL_le {Γ Γ' Γ'' Δ' Δ : Multiset Formula}
    (h : Provable ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫) (hle : Γ' ≤ Γ'') : Provable ⟪Γ ; Γ'' ⊢ Δ' ; Δ⟫ := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 hle
  simpa [add_comm] using h.weakCL E

/-- Identity with the formula in the central zone: `;A ⊢ ;A`. -/
theorem Provable.axC (A : Formula) : Provable ⟪0 ; {A} ⊢ 0 ; {A}⟫ :=
  .rule1 (Rule.inL 0 0 0 {A} A) (.rule (Rule.ax A) (by simp))

/-- A positive formula in the central zone may be moved to the linear zone (`outL`). -/
theorem Provable.outL' {Γ Γ' Δ' Δ : Multiset Formula} {P : Formula} (hP : P.pol = .pos)
    (h : Provable ⟪Γ ; P ::ₘ Γ' ⊢ Δ' ; Δ⟫) : Provable ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫ :=
  .rule1 (Rule.outL _ _ _ _ P hP) h

/-- Using a projection `B;⊢;A` provable in LU: if `;A, Γ ⊢ ;C` then `;B, Γ ⊢ ;C`. -/
theorem Provable.useProj {B A C : Formula} {Γ : Multiset Formula}
    (hBA : Provable ⟪{B} ; 0 ⊢ 0 ; {A}⟫) (h : Provable ⟪0 ; A ::ₘ Γ ⊢ 0 ; {C}⟫) :
    Provable ⟪0 ; B ::ₘ Γ ⊢ 0 ; {C}⟫ := by
  have h1 : Provable ⟪0 ; B ::ₘ Γ ⊢ 0 ; {A}⟫ :=
    (Provable.rule1 (Rule.inL 0 0 0 {A} B) hBA).weakCL_le (by simp)
  have h2 : Provable ⟪0 ; A ::ₘ B ::ₘ Γ ⊢ 0 ; {C}⟫ :=
    h.weakCL_le (Multiset.cons_le_cons _ (Multiset.le_cons_self _ _))
  exact .cutRule (CutRule.cutL 0 (B ::ₘ Γ) 0 {C} A) (by simp [h1, h2])

theorem pol_pos_or_neu {A : Formula} (h : A.IsIntuitionistic) : A.pol = .pos ∨ A.pol = .neu := by
  have := h.pol_ne_neg
  cases hA : A.pol <;> simp_all

/-- Weakening of a positive formula in the linear left zone. -/
theorem Provable.weakPos {Γ Γ' Δ' Δ : Multiset Formula} {P : Formula} (hP : P.pol = .pos)
    (h : Provable ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫) : Provable ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫ :=
  .outL' hP (.rule1 (Rule.weakL _ _ _ _ P) h)

theorem proj_conj₁ {A B : Formula} (hA : A.IsIntuitionistic) (hB : B.IsIntuitionistic) :
    Provable ⟪{conj A B} ; 0 ⊢ 0 ; {A}⟫ := by
  have ax := Provable.rule (Rule.ax A) (by simp)
  rcases pol_pos_or_neu hA with hpA | hpA <;> rcases pol_pos_or_neu hB with hpB | hpB
  · exact .rule1 (Rule.conjL_PQ 0 0 0 {A} A B hpA hpB)
      ((Provable.weakPos hpB ax).congr (by
        rw [Sequent.mk.injEq]; exact ⟨Multiset.cons_swap B A 0, rfl, rfl, rfl⟩))
  · exact .rule1 (Rule.conjL_PB 0 0 0 {A} A B hpA (by simp [hpB]))
      (.rule1 (Rule.weakL _ _ _ _ B) ax)
  · exact .rule1 (Rule.conjL_AQ 0 0 0 {A} A B (by simp [hpA]) hpB)
      (Provable.weakPos hpB (by simpa using Provable.axC A))
  · exact .rule1 (Rule.conjL_AB₁ 0 0 0 {A} A B (by simp [hpA]) (by simp [hpB])) ax

theorem proj_conj₂ {A B : Formula} (hA : A.IsIntuitionistic) (hB : B.IsIntuitionistic) :
    Provable ⟪{conj A B} ; 0 ⊢ 0 ; {B}⟫ := by
  have ax := Provable.rule (Rule.ax B) (by simp)
  rcases pol_pos_or_neu hA with hpA | hpA <;> rcases pol_pos_or_neu hB with hpB | hpB
  · exact .rule1 (Rule.conjL_PQ 0 0 0 {B} A B hpA hpB) (Provable.weakPos hpA ax)
  · exact .rule1 (Rule.conjL_PB 0 0 0 {B} A B hpA (by simp [hpB]))
      (Provable.weakPos hpA (by simpa using Provable.axC B))
  · exact .rule1 (Rule.conjL_AQ 0 0 0 {B} A B (by simp [hpA]) hpB)
      (.rule1 (Rule.weakL _ _ _ _ A) ax)
  · exact .rule1 (Rule.conjL_AB₂ 0 0 0 {B} A B (by simp [hpA]) (by simp [hpB])) ax

theorem proj_lall (A : Formula) (t : Term) : Provable ⟪{lall A} ; 0 ⊢ 0 ; {A.inst t}⟫ :=
  .rule1 (Rule.lallL 0 0 0 {A.inst t} A t) (.rule (Rule.ax _) (by simp))

/-- `A ⊃ B; ⊢ ;B` from `;Γ ⊢ ;A`, with `Γ` in the central zone. -/
theorem proj_iimp {A B : Formula} {Γ : Multiset Formula} (hA : A.IsIntuitionistic)
    (h : Provable ⟪0 ; Γ ⊢ 0 ; {A}⟫) : Provable ⟪{iimp A B} ; Γ ⊢ 0 ; {B}⟫ := by
  have axB : Provable ⟪{B} ; Γ ⊢ 0 ; {B}⟫ :=
    (Provable.rule (Rule.ax B) (by simp)).weakCL_le (Multiset.zero_le _)
  rcases pol_pos_or_neu hA with hpA | hpA
  · exact (Provable.rule2 (Rule.iimpL_P 0 0 Γ 0 0 {B} A B hpA) (by simpa using h)
      (by simpa using axB)).congr (by simp)
  · exact Provable.rule2 (Rule.iimpL_A 0 Γ 0 {B} A B (by simp [hpA])) h axB

theorem sh_zero : sh 0 = 0 := Multiset.map_zero _

/-- **From LJ to LU** (end of §6, item 1, "the other way around"): an LJ-provable sequent
`Γ ⊢ C` of intuitionistic formulas is provable in LU (with cut) as `;Γ ⊢ ;C`. -/
theorem LJ.provable {Γ : Multiset Formula} {C : Formula} (h : LJ Γ C)
    (hΓ : ∀ A ∈ Γ, A.IsIntuitionistic) (hC : C.IsIntuitionistic) :
    Provable ⟪0 ; Γ ⊢ 0 ; {C}⟫ := by
  induction h with
  | ax A => exact Provable.axC A
  | weak A _ ih =>
    exact .rule1 (Rule.weakL _ _ _ _ A) (ih (fun B hB => hΓ B (Multiset.mem_cons_of_mem hB)) hC)
  | contr A _ ih =>
    refine .rule1 (Rule.contrL _ _ _ _ A) (ih (fun B hB => ?_) hC)
    rcases Multiset.mem_cons.1 hB with rfl | hB
    · exact hΓ _ (Multiset.mem_cons_self _ _)
    · exact hΓ B hB
  | trueR => exact .rule (Rule.oneR) (by simp)
  | falseL Γ C =>
    exact (Provable.rule1 (Rule.inL 0 0 0 {C} zero) (.rule (Rule.zeroL 0 {C}) (by simp))).weakCL_le
      (by simp)
  | conjR _ _ ihA ihB =>
    rename_i Γ A B _ _
    have hA := ihA hΓ hC.1
    have hB := ihB hΓ hC.2
    rcases pol_pos_or_neu hC.1 with hpA | hpA <;> rcases pol_pos_or_neu hC.2 with hpB | hpB
    · exact (Provable.rule2 (Rule.conjR_PQ 0 0 Γ 0 0 0 A B hpA hpB) (by simpa using hA)
        (by simpa using hB)).congr (by simp)
    · exact Provable.rule2 (Rule.conjR_PB 0 Γ 0 0 A B hpA (by simp [hpB])) hA hB
    · exact Provable.rule2 (Rule.conjR_AQ 0 Γ 0 0 A B (by simp [hpA]) hpB) hA hB
    · exact Provable.rule2 (Rule.conjR_AB 0 Γ 0 0 A B (by simp [hpA]) (by simp [hpB])) hA hB
  | conjL _ ih =>
    rename_i Γ A B C _
    have hAB : (conj A B).IsIntuitionistic := hΓ _ (Multiset.mem_cons_self _ _)
    have hΓ' : ∀ D ∈ Γ, D.IsIntuitionistic := fun D hD => hΓ D (Multiset.mem_cons_of_mem hD)
    have h1 := ih (by
      intro D hD
      simp only [Multiset.mem_cons] at hD
      rcases hD with rfl | rfl | hD
      exacts [hAB.1, hAB.2, hΓ' D hD]) hC
    -- weaken with `A ∧ B`, then eliminate `A` and `B` by cuts against the projections
    have h2 : Provable ⟪0 ; A ::ₘ B ::ₘ conj A B ::ₘ Γ ⊢ 0 ; {C}⟫ :=
      h1.weakCL_le (Multiset.cons_le_cons _ (Multiset.cons_le_cons _ (Multiset.le_cons_self _ _)))
    have h3 : Provable ⟪0 ; conj A B ::ₘ B ::ₘ conj A B ::ₘ Γ ⊢ 0 ; {C}⟫ :=
      Provable.useProj (proj_conj₁ hAB.1 hAB.2) h2
    have h4 : Provable ⟪0 ; B ::ₘ conj A B ::ₘ Γ ⊢ 0 ; {C}⟫ :=
      (Provable.rule1 (Rule.contrL 0 (B ::ₘ Γ) 0 {C} (conj A B))
        (h3.congr (by rw [Multiset.cons_swap B (conj A B) Γ]))).congr
        (by rw [Multiset.cons_swap (conj A B) B Γ])
    have h5 := Provable.useProj (proj_conj₂ hAB.1 hAB.2) h4
    exact .rule1 (Rule.contrL _ _ _ _ _) h5
  | disjR₁ _ ih =>
    rename_i Γ A B _
    have hA := ih hΓ hC.1
    rcases pol_pos_or_neu hC.1 with hpA | hpA <;> rcases pol_pos_or_neu hC.2 with hpB | hpB
    · exact .rule1 (Rule.disjR₁_PQ 0 Γ 0 0 A B hpA hpB) hA
    · exact .rule1 (Rule.disjR₁_PT 0 Γ 0 0 A B hpA hpB) hA
    · exact .rule1 (Rule.disjR₁_SQ Γ 0 A B hpA hpB) hA
    · exact .rule1 (Rule.disjR₁_ST Γ 0 A B hpA hpB) hA
  | disjR₂ _ ih =>
    rename_i Γ A B _
    have hB := ih hΓ hC.2
    rcases pol_pos_or_neu hC.1 with hpA | hpA <;> rcases pol_pos_or_neu hC.2 with hpB | hpB
    · exact .rule1 (Rule.disjR₂_PQ 0 Γ 0 0 A B hpA hpB) hB
    · exact .rule1 (Rule.disjR₂_PT Γ 0 A B hpA hpB) hB
    · exact .rule1 (Rule.disjR₂_SQ 0 Γ 0 0 A B hpA hpB) hB
    · exact .rule1 (Rule.disjR₂_ST Γ 0 A B hpA hpB) hB
  | disjL _ _ ihA ihB =>
    rename_i Γ A B C _ _
    have hAB : (disj A B).IsIntuitionistic := hΓ _ (Multiset.mem_cons_self _ _)
    have hΓ' : ∀ D ∈ Γ, D.IsIntuitionistic := fun D hD => hΓ D (Multiset.mem_cons_of_mem hD)
    have hA := ihA (by
      intro D hD; rcases Multiset.mem_cons.1 hD with rfl | hD
      exacts [hAB.1, hΓ' D hD]) hC
    have hB := ihB (by
      intro D hD; rcases Multiset.mem_cons.1 hD with rfl | hD
      exacts [hAB.2, hΓ' D hD]) hC
    refine .rule1 (Rule.inL 0 Γ 0 {C} (disj A B)) ?_
    rcases pol_pos_or_neu hAB.1 with hpA | hpA <;> rcases pol_pos_or_neu hAB.2 with hpB | hpB
    · exact Provable.rule2 (Rule.disjL_PQ 0 Γ 0 {C} A B hpA hpB) (.outL' hpA hA) (.outL' hpB hB)
    · exact Provable.rule2 (Rule.disjL_PT 0 Γ 0 {C} A B hpA hpB) (.outL' hpA hA) hB
    · exact Provable.rule2 (Rule.disjL_SQ 0 Γ 0 {C} A B hpA hpB) hA (.outL' hpB hB)
    · exact Provable.rule2 (Rule.disjL_ST 0 Γ 0 {C} A B hpA hpB) hA hB
  | iimpR _ ih =>
    rename_i Γ A B _
    have hB := ih (by
      intro D hD; rcases Multiset.mem_cons.1 hD with rfl | hD
      exacts [hC.1, hΓ D hD]) hC.2
    rcases pol_pos_or_neu hC.1 with hpA | hpA
    · exact .rule1 (Rule.iimpR_P 0 Γ 0 0 A B hpA) (.outL' hpA hB)
    · exact .rule1 (Rule.iimpR_A 0 Γ 0 0 A B (by simp [hpA])) hB
  | iimpL _ _ ihA ihC =>
    rename_i Γ A B C _ _
    have hAB : (iimp A B).IsIntuitionistic := hΓ _ (Multiset.mem_cons_self _ _)
    have hΓ' : ∀ D ∈ Γ, D.IsIntuitionistic := fun D hD => hΓ D (Multiset.mem_cons_of_mem hD)
    have hA := ihA hΓ' hAB.1
    have hC' := ihC (by
      intro D hD; rcases Multiset.mem_cons.1 hD with rfl | hD
      exacts [hAB.2, hΓ' D hD]) hC
    have h1 : Provable ⟪0 ; iimp A B ::ₘ Γ ⊢ 0 ; {B}⟫ :=
      .rule1 (Rule.inL 0 Γ 0 {B} (iimp A B)) (proj_iimp hAB.1 hA)
    have h2 : Provable ⟪0 ; B ::ₘ iimp A B ::ₘ Γ ⊢ 0 ; {C}⟫ :=
      hC'.weakCL_le (Multiset.cons_le_cons _ (Multiset.le_cons_self _ _))
    exact .cutRule (CutRule.cutL 0 (iimp A B ::ₘ Γ) 0 {C} B) (by simp [h1, h2])
  | allR _ ih =>
    rename_i Γ A _
    have hA := ih (fun D hD => by
      obtain ⟨E, hE, rfl⟩ := Multiset.mem_map.1 hD
      simpa [shift] using hΓ E hE) hC
    exact .rule1 (Rule.lallR 0 Γ 0 0 A) (by simpa [sh_zero] using hA)
  | allL t _ ih =>
    rename_i Γ A C _
    have hA : (lall A).IsIntuitionistic := hΓ _ (Multiset.mem_cons_self _ _)
    have h1 := ih (by
      intro D hD; rcases Multiset.mem_cons.1 hD with rfl | hD
      · simpa [inst] using hA
      · exact hΓ D (Multiset.mem_cons_of_mem hD)) hC
    exact Provable.useProj (proj_lall A t) h1
  | exR t _ ih =>
    rename_i Γ A _
    have hA := ih hΓ (by simpa [inst] using hC)
    rcases pol_pos_or_neu (show A.IsIntuitionistic from hC) with hpA | hpA
    · exact .rule1 (Rule.cexR_P 0 Γ 0 0 A t hpA) hA
    · exact .rule1 (Rule.cexR_A Γ 0 A t (by simp [hpA])) hA
  | exL _ ih =>
    rename_i Γ A C _
    have hA : (cex A).IsIntuitionistic := hΓ _ (Multiset.mem_cons_self _ _)
    have h1 := ih (by
      intro D hD; rcases Multiset.mem_cons.1 hD with rfl | hD
      · exact hA
      · obtain ⟨E, hE, rfl⟩ := Multiset.mem_map.1 hD
        simpa [shift] using hΓ E (Multiset.mem_cons_of_mem hE)) (by simpa [shift] using hC)
    refine .rule1 (Rule.inL 0 Γ 0 {C} (cex A)) ?_
    rcases pol_pos_or_neu (show A.IsIntuitionistic from hA) with hpA | hpA
    · exact .rule1 (Rule.cexL_P 0 Γ 0 {C} A hpA) (by simpa [sh_zero] using Provable.outL' hpA h1)
    · exact .rule1 (Rule.cexL_A 0 Γ 0 {C} A (by simp [hpA])) (by simpa [sh_zero] using h1)

end LU
