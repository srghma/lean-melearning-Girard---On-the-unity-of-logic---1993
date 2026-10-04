module

public import RequestProject.LU.IntMain

/-!
# The classical fragment: infrastructure

For a sequent `S = Γ;Γ' ⊢ Δ';Δ` made of classical formulas, `μ(S)` counts the negative
formulas of `Γ` and the positive formulas of `Δ` (the formulas *contributing* to `μ`).
The other formulas of the linear zones (positive in `Γ`, negative in `Δ`) are the
*non-contributing* ones.

The proof of the theorem of §6 for the classical fragment establishes, by induction on a
cut-free proof of a sequent `S` made of classical formulas, the invariant `ClGood S`:
* if `μ(S) ≤ 1` then `S` is provable within the classical fragment;
* if `μ(S) ≥ 2` then *any* classical sequent containing at least the non-contributing
  formulas of `S` and the central zones of `S` is provable within the classical fragment
  ("an easy exercise ... to produce another proof of any sequent obtained by removing as many
  formulas among those which contribute to `μ(S)`").
-/

@[expose] public section

namespace LU

open Formula

/-- The negative formulas of a multiset. -/
def muL (Γ : Multiset Formula) : ℕ := Multiset.card (Γ.filter (fun A => A.pol = .neg))

/-- The positive formulas of a multiset. -/
def muR (Δ : Multiset Formula) : ℕ := Multiset.card (Δ.filter (fun A => A.pol = .pos))

/-- Non-contributing formulas of a left linear zone. -/
abbrev NCL (Γ : Multiset Formula) : Multiset Formula := Γ.filter (fun A => A.pol ≠ .neg)

/-- Non-contributing formulas of a right linear zone. -/
abbrev NCR (Δ : Multiset Formula) : Multiset Formula := Δ.filter (fun A => A.pol ≠ .pos)

theorem mu_mk (L C D R : Multiset Formula) : mu ⟪L ; C ⊢ D ; R⟫ = muL L + muR R := rfl

@[simp] theorem muL_zero : muL 0 = 0 := rfl
@[simp] theorem muR_zero : muR 0 = 0 := rfl
@[simp] theorem muL_add (a b : Multiset Formula) : muL (a + b) = muL a + muL b := by
  simp [muL]
@[simp] theorem muR_add (a b : Multiset Formula) : muR (a + b) = muR a + muR b := by
  simp [muR]
@[simp] theorem muL_cons (A : Formula) (a : Multiset Formula) :
    muL (A ::ₘ a) = (if A.pol = .neg then 1 else 0) + muL a := by
  simp only [muL, Multiset.filter_cons]; split_ifs <;> simp [add_comm]
@[simp] theorem muR_cons (A : Formula) (a : Multiset Formula) :
    muR (A ::ₘ a) = (if A.pol = .pos then 1 else 0) + muR a := by
  simp only [muR, Multiset.filter_cons]; split_ifs <;> simp [add_comm]
@[simp] theorem muL_singleton (A : Formula) : muL {A} = if A.pol = .neg then 1 else 0 := by
  simpa using muL_cons A 0
@[simp] theorem muR_singleton (A : Formula) : muR {A} = if A.pol = .pos then 1 else 0 := by
  simpa using muR_cons A 0

theorem NCL_eq_self {Γ : Multiset Formula} (h : muL Γ = 0) : NCL Γ = Γ := by
  rw [Multiset.filter_eq_self]
  intro A hA hA'
  have : 0 < muL Γ := Multiset.card_pos_iff_exists_mem.2 ⟨A, by simp [hA, hA']⟩
  omega

theorem NCR_eq_self {Δ : Multiset Formula} (h : muR Δ = 0) : NCR Δ = Δ := by
  rw [Multiset.filter_eq_self]
  intro A hA hA'
  have : 0 < muR Δ := Multiset.card_pos_iff_exists_mem.2 ⟨A, by simp [hA, hA']⟩
  omega

theorem NCL_le_of_add {A Γ X : Multiset Formula} (h : NCL (A + Γ) ≤ A + X) : NCL Γ ≤ X := by
  classical
  rw [Multiset.le_iff_count] at h ⊢
  intro a
  have := h a
  simp only [Multiset.filter_add, Multiset.count_add, Multiset.count_filter] at this ⊢
  split_ifs at this ⊢ <;> omega

theorem NCR_le_of_add {A Γ X : Multiset Formula} (h : NCR (A + Γ) ≤ A + X) : NCR Γ ≤ X := by
  classical
  rw [Multiset.le_iff_count] at h ⊢
  intro a
  have := h a
  simp only [Multiset.filter_add, Multiset.count_add, Multiset.count_filter] at this ⊢
  split_ifs at this ⊢ <;> omega

/-- Shape of the sequents occurring in a cut-free proof of a classical sequent. -/
abbrev ClShape (S : Sequent) : Prop := AllIn IsClassical S

/-- Provability within the classical fragment. -/
abbrev ClWithin (S : Sequent) : Prop := ProvableWithin .classical S

/-- The invariant proved by induction on a cut-free proof (see the module docstring). -/
def ClGood (S : Sequent) : Prop :=
  (mu S ≤ 1 → ClWithin S) ∧
  (2 ≤ mu S → ∀ T : Sequent, ClassicalSeq T → NCL S.L ≤ T.L → S.CL ≤ T.CL → S.CR ≤ T.CR →
    NCR S.R ≤ T.R → ClWithin T)

theorem ClWithin.classicalSeq {S : Sequent} (h : ClWithin S) : ClassicalSeq S := by
  cases h with
  | mk _ _ _ h _ => exact h

theorem cl_within_rule {ps : List Sequent} {c T : Sequent} (hr : Rule ps c) (heq : c = T)
    (hT : ClassicalSeq T) (hps : ∀ p ∈ ps, ClWithin p) : ClWithin T := by
  subst heq; exact .mk ps c hr hT hps

theorem cl_weakL {L C D R : Multiset Formula} (E : Multiset Formula)
    (h : ClWithin ⟪L ; C ⊢ D ; R⟫) (hE : ∀ A ∈ E, A.IsClassical) :
    ClWithin ⟪L ; C + E ⊢ D ; R⟫ := by
  induction E using Multiset.induction with
  | empty => simpa using h
  | cons A E ih =>
    have ih' := ih (fun B hB => hE B (Multiset.mem_cons_of_mem hB))
    obtain ⟨h1, h2⟩ := ih'.classicalSeq
    refine cl_within_rule (Rule.weakL L (C + E) D R A) (by simp) ⟨?_, h2⟩ (by simpa using ih')
    simp only [allIn_mk] at h1 ⊢
    refine ⟨h1.1, ?_, h1.2.2⟩
    intro B hB
    simp only [Multiset.add_cons, Multiset.mem_cons] at hB
    rcases hB with rfl | hB
    · exact hE _ (Multiset.mem_cons_self _ _)
    · exact h1.2.1 B hB

theorem cl_weakR {L C D R : Multiset Formula} (E : Multiset Formula)
    (h : ClWithin ⟪L ; C ⊢ D ; R⟫) (hE : ∀ A ∈ E, A.IsClassical) :
    ClWithin ⟪L ; C ⊢ D + E ; R⟫ := by
  induction E using Multiset.induction with
  | empty => simpa using h
  | cons A E ih =>
    have ih' := ih (fun B hB => hE B (Multiset.mem_cons_of_mem hB))
    obtain ⟨h1, h2⟩ := ih'.classicalSeq
    refine cl_within_rule (Rule.weakR L C (D + E) R A) (by simp) ⟨?_, h2⟩ (by simpa using ih')
    simp only [allIn_mk] at h1 ⊢
    refine ⟨h1.1, h1.2.1, ?_, h1.2.2.2⟩
    intro B hB
    simp only [Multiset.add_cons, Multiset.mem_cons] at hB
    rcases hB with rfl | hB
    · exact hE _ (Multiset.mem_cons_self _ _)
    · exact h1.2.2.1 B hB

/-- Weakening of the central zones, towards a target sequent. -/
theorem cl_weak_to {T : Sequent} {L C D R : Multiset Formula}
    (h : ClWithin ⟪L ; C ⊢ D ; R⟫) (hT : ClassicalSeq T) (hL : T.L = L) (hC : C ≤ T.CL)
    (hD : D ≤ T.CR) (hR : T.R = R) : ClWithin T := by
  obtain ⟨E, hE⟩ := Multiset.le_iff_exists_add.1 hC
  obtain ⟨E', hE'⟩ := Multiset.le_iff_exists_add.1 hD
  obtain ⟨TL, TC, TD, TR⟩ := T
  obtain ⟨hA, _⟩ := hT
  simp only at hL hR hE hE'
  subst hL hR hE hE'
  rw [allIn_mk] at hA
  refine cl_weakR E' (cl_weakL E h fun A hA' => hA.2.1 A ?_) fun A hA' => hA.2.2.1 A ?_
  · simp [hA']
  · simp [hA']

/-- Using the invariant of a premise towards a target sequent. -/
theorem ClGood.apply {p T : Sequent} (hp : ClGood p) (hT : ClassicalSeq T)
    (hle : mu p ≤ 1 → T.L = p.L ∧ T.R = p.R) (hL : NCL p.L ≤ T.L) (hC : p.CL ≤ T.CL)
    (hD : p.CR ≤ T.CR) (hR : NCR p.R ≤ T.R) : ClWithin T := by
  by_cases h : mu p ≤ 1
  · obtain ⟨hl, hr⟩ := hle h
    obtain ⟨pL, pC, pD, pR⟩ := p
    exact cl_weak_to (hp.1 h) hT hl hC hD hr
  · exact hp.2 (by omega) T hT hL hC hD hR

/-- Rules for which the conclusion can always be obtained from a premise. -/
theorem cl_absorb {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (hc : ClShape c)
    (ih : ∀ q ∈ ps, ClGood q) (h1 : mu c ≤ 1 → ∀ q ∈ ps, mu q ≤ 1)
    (h2 : 2 ≤ mu c → ∃ q ∈ ps, 2 ≤ mu q ∧ NCL q.L ≤ NCL c.L ∧ q.CL ≤ c.CL ∧ q.CR ≤ c.CR ∧
      NCR q.R ≤ NCR c.R) : ClGood c := by
  refine ⟨fun hmu => cl_within_rule hr rfl ⟨hc, hmu⟩ fun q hq => (ih q hq).1 (h1 hmu q hq),
    fun hmu T hT hL hC hD hR => ?_⟩
  obtain ⟨q, hq, hq2, hqL, hqC, hqD, hqR⟩ := h2 hmu
  exact (ih q hq).2 hq2 T hT (hqL.trans hL) (hqC.trans hC) (hqD.trans hD) (hqR.trans hR)

/-- Admissible transformations of the contexts in a rule: the identity, and the shift used
for the eigenvariable condition. -/
structure CtxMap (f : Multiset Formula → Multiset Formula) : Prop where
  add : ∀ a b, f (a + b) = f a + f b
  cl : ∀ a, (∀ A ∈ a, A.IsClassical) → ∀ A ∈ f a, A.IsClassical
  muL : ∀ a, muL (f a) = muL a
  muR : ∀ a, muR (f a) = muR a
  ncl : ∀ a, NCL (f a) = f (NCL a)
  ncr : ∀ a, NCR (f a) = f (NCR a)
  mono : ∀ a b, a ≤ b → f a ≤ f b

theorem ctxMap_id : CtxMap id where
  add _ _ := rfl
  cl _ h := h
  muL _ := rfl
  muR _ := rfl
  ncl _ := rfl
  ncr _ := rfl
  mono _ _ h := h

theorem ctxMap_sh : CtxMap sh where
  add a b := Multiset.map_add _ _ _
  cl _ h := forall_mem_sh subClosed_classical h
  muL a := by simp [muL, Multiset.filter_map, ]
  muR a := by simp [muR, Multiset.filter_map, ]
  ncl a := by simp [Multiset.filter_map, ]
  ncr a := by simp [Multiset.filter_map, ]
  mono _ _ h := Multiset.map_le_map h

theorem forall_mem_add_iff {F : Formula → Prop} {a b : Multiset Formula} :
    (∀ A ∈ a + b, F A) ↔ (∀ A ∈ a, F A) ∧ (∀ A ∈ b, F A) := by
  simp only [Multiset.mem_add, or_imp, forall_and]

/-- Decomposition of a target sequent containing the non-contributing formulas `L0`, `R0`
and the central formulas `C0`, `D0` of the principal part of a rule. -/
theorem cl_tgt_decomp {T : Sequent} {L0 C0 D0 R0 Γ Γ' Δ' Δ : Multiset Formula}
    (hL0 : NCL L0 = L0) (hR0 : NCR R0 = R0) (hL : NCL (L0 + Γ) ≤ T.L)
    (hC : C0 + Γ' ≤ T.CL) (hD : D0 + Δ' ≤ T.CR) (hR : NCR (R0 + Δ) ≤ T.R) :
    ∃ Tl Tc Td Tr, T = ⟪L0 + Tl ; C0 + Tc ⊢ D0 + Td ; R0 + Tr⟫ ∧ NCL Γ ≤ Tl ∧ Γ' ≤ Tc ∧
      Δ' ≤ Td ∧ NCR Δ ≤ Tr := by
  obtain ⟨TL, TC, TD, TR⟩ := T
  simp only at hL hC hD hR
  have h1 : L0 ≤ TL := calc
    L0 = NCL L0 := hL0.symm
    _ ≤ NCL (L0 + Γ) := Multiset.filter_le_filter _ (Multiset.le_add_right _ _)
    _ ≤ TL := hL
  have h2 : R0 ≤ TR := calc
    R0 = NCR R0 := hR0.symm
    _ ≤ NCR (R0 + Δ) := Multiset.filter_le_filter _ (Multiset.le_add_right _ _)
    _ ≤ TR := hR
  obtain ⟨Tl, rfl⟩ := Multiset.le_iff_exists_add.1 h1
  obtain ⟨Tr, rfl⟩ := Multiset.le_iff_exists_add.1 h2
  obtain ⟨Tc, rfl⟩ := Multiset.le_iff_exists_add.1 ((Multiset.le_add_right C0 Γ').trans hC)
  obtain ⟨Td, rfl⟩ := Multiset.le_iff_exists_add.1 ((Multiset.le_add_right D0 Δ').trans hD)
  exact ⟨Tl, Tc, Td, Tr, rfl, NCL_le_of_add hL, (add_le_add_iff_left _).1 hC,
    (add_le_add_iff_left _).1 hD, NCR_le_of_add hR⟩

theorem classicalSeq_parts {L C D R : Multiset Formula} (h : ClassicalSeq ⟪L ; C ⊢ D ; R⟫) :
    (∀ A ∈ L, A.IsClassical) ∧ (∀ A ∈ C, A.IsClassical) ∧ (∀ A ∈ D, A.IsClassical) ∧
      (∀ A ∈ R, A.IsClassical) ∧ muL L + muR R ≤ 1 :=
  ⟨(allIn_mk.1 h.1).1, (allIn_mk.1 h.1).2.1, (allIn_mk.1 h.1).2.2.1, (allIn_mk.1 h.1).2.2.2, h.2⟩

/-- A target of a premise of a rule, obtained from the decomposition of a target of the
conclusion. -/
theorem cl_premise_tgt {f : Multiset Formula → Multiset Formula} (hf : CtxMap f)
    {L1 C1 D1 R1 Γ Γ' Δ' Δ Tl Tc Td Tr : Multiset Formula}
    (h1 : muL L1 + muR R1 = 0)
    (hp : ClShape ⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫)
    (ih : ClGood ⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫)
    (hmu : 2 ≤ mu ⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫)
    (hTL : ∀ A ∈ Tl, A.IsClassical) (hTC : ∀ A ∈ Tc, A.IsClassical)
    (hTD : ∀ A ∈ Td, A.IsClassical) (hTR : ∀ A ∈ Tr, A.IsClassical)
    (hTmu : muL Tl + muR Tr ≤ 1)
    (hl : NCL Γ ≤ Tl) (hc : Γ' ≤ Tc) (hd : Δ' ≤ Td) (hr : NCR Δ ≤ Tr) :
    ClWithin ⟪L1 + f Tl ; C1 + f Tc ⊢ D1 + f Td ; R1 + f Tr⟫ := by
  have hpA := allIn_mk.1 hp
  simp only [forall_mem_add_iff] at hpA
  refine ih.2 hmu _ ⟨allIn_mk.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩ ?_ ?_ ?_ ?_
  · exact forall_mem_add_iff.2 ⟨hpA.1.1, hf.cl _ hTL⟩
  · exact forall_mem_add_iff.2 ⟨hpA.2.1.1, hf.cl _ hTC⟩
  · exact forall_mem_add_iff.2 ⟨hpA.2.2.1.1, hf.cl _ hTD⟩
  · exact forall_mem_add_iff.2 ⟨hpA.2.2.2.1, hf.cl _ hTR⟩
  · simp only [mu_mk, muL_add, muR_add, hf.muL, hf.muR]; omega
  · simp only [Multiset.filter_add, hf.ncl]
    exact add_le_add (Multiset.filter_le _ _) (hf.mono _ _ hl)
  · exact add_le_add le_rfl (hf.mono _ _ hc)
  · exact add_le_add le_rfl (hf.mono _ _ hd)
  · simp only [Multiset.filter_add, hf.ncr]
    exact add_le_add (Multiset.filter_le _ _) (hf.mono _ _ hr)

/-- One-premise rules whose principal formula and active formulas do not contribute to `μ`:
the conclusion is obtained by applying the same rule to a target of the premise. -/
theorem cl_reapply1 {f : Multiset Formula → Multiset Formula} (hf : CtxMap f)
    {L0 C0 D0 R0 L1 C1 D1 R1 Γ Γ' Δ' Δ : Multiset Formula}
    (hr : ∀ Γ Γ' Δ' Δ, Rule [⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫]
      ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫)
    (h0 : muL L0 + muR R0 = 0) (h1 : muL L1 + muR R1 = 0)
    (hc : ClShape ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫)
    (hp : ClShape ⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫)
    (ih : ClGood ⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫) :
    ClGood ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫ := by
  have hmu : mu ⟪L1 + f Γ ; C1 + f Γ' ⊢ D1 + f Δ' ; R1 + f Δ⟫ =
      mu ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫ := by
    simp only [mu_mk, muL_add, muR_add, hf.muL, hf.muR]; omega
  refine ⟨fun h => cl_within_rule (hr Γ Γ' Δ' Δ) rfl ⟨hc, h⟩
    (by simpa using ih.1 (hmu ▸ h)), fun h T hT hL hC hD hR => ?_⟩
  obtain ⟨Tl, Tc, Td, Tr, rfl, hl, hc', hd, hr'⟩ :=
    cl_tgt_decomp (NCL_eq_self (by omega)) (NCR_eq_self (by omega)) hL hC hD hR
  obtain ⟨hTL, hTC, hTD, hTR, hTmu⟩ := classicalSeq_parts hT
  rw [forall_mem_add_iff] at hTL hTC hTD hTR
  simp only [muL_add, muR_add] at hTmu
  refine cl_within_rule (hr Tl Tc Td Tr) rfl hT ?_
  simp only [List.mem_singleton, forall_eq]
  exact cl_premise_tgt hf h1 hp ih (hmu ▸ h) hTL.2 hTC.2 hTD.2 hTR.2 (by omega) hl hc' hd hr'

/-- Two-premise additive rules whose principal formula and active formulas do not
contribute to `μ`. -/
theorem cl_reapply2 {L0 C0 D0 R0 L1 C1 D1 R1 L2 C2 D2 R2 Γ Γ' Δ' Δ : Multiset Formula}
    (hr : ∀ Γ Γ' Δ' Δ, Rule [⟪L1 + Γ ; C1 + Γ' ⊢ D1 + Δ' ; R1 + Δ⟫,
      ⟪L2 + Γ ; C2 + Γ' ⊢ D2 + Δ' ; R2 + Δ⟫] ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫)
    (h0 : muL L0 + muR R0 = 0) (h1 : muL L1 + muR R1 = 0) (h2 : muL L2 + muR R2 = 0)
    (hc : ClShape ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫)
    (hp1 : ClShape ⟪L1 + Γ ; C1 + Γ' ⊢ D1 + Δ' ; R1 + Δ⟫)
    (hp2 : ClShape ⟪L2 + Γ ; C2 + Γ' ⊢ D2 + Δ' ; R2 + Δ⟫)
    (ih1 : ClGood ⟪L1 + Γ ; C1 + Γ' ⊢ D1 + Δ' ; R1 + Δ⟫)
    (ih2 : ClGood ⟪L2 + Γ ; C2 + Γ' ⊢ D2 + Δ' ; R2 + Δ⟫) :
    ClGood ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫ := by
  have hmu1 : mu ⟪L1 + Γ ; C1 + Γ' ⊢ D1 + Δ' ; R1 + Δ⟫ =
      mu ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫ := by
    simp only [mu_mk, muL_add, muR_add]; omega
  have hmu2 : mu ⟪L2 + Γ ; C2 + Γ' ⊢ D2 + Δ' ; R2 + Δ⟫ =
      mu ⟪L0 + Γ ; C0 + Γ' ⊢ D0 + Δ' ; R0 + Δ⟫ := by
    simp only [mu_mk, muL_add, muR_add]; omega
  refine ⟨fun h => cl_within_rule (hr Γ Γ' Δ' Δ) rfl ⟨hc, h⟩
    (by simpa using ⟨ih1.1 (hmu1 ▸ h), ih2.1 (hmu2 ▸ h)⟩), fun h T hT hL hC hD hR => ?_⟩
  obtain ⟨Tl, Tc, Td, Tr, rfl, hl, hc', hd, hr'⟩ :=
    cl_tgt_decomp (NCL_eq_self (by omega)) (NCR_eq_self (by omega)) hL hC hD hR
  obtain ⟨hTL, hTC, hTD, hTR, hTmu⟩ := classicalSeq_parts hT
  rw [forall_mem_add_iff] at hTL hTC hTD hTR
  simp only [muL_add, muR_add] at hTmu
  refine cl_within_rule (hr Tl Tc Td Tr) rfl hT ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨cl_premise_tgt ctxMap_id h1 hp1 ih1 (hmu1 ▸ h) hTL.2 hTC.2 hTD.2 hTR.2 (by omega)
      hl hc' hd hr',
    cl_premise_tgt ctxMap_id h2 hp2 ih2 (hmu2 ▸ h) hTL.2 hTC.2 hTD.2 hTR.2 (by omega)
      hl hc' hd hr'⟩

theorem cl_zeroL (Γ Δ : Multiset Formula) (hc : ClShape ⟪zero ::ₘ Γ ; 0 ⊢ 0 ; Δ⟫) :
    ClGood ⟪zero ::ₘ Γ ; 0 ⊢ 0 ; Δ⟫ := by
  refine ⟨fun h1 => cl_within_rule (Rule.zeroL Γ Δ) rfl ⟨hc, h1⟩ (by simp),
    fun _ T hT hL _ _ _ => ?_⟩
  obtain ⟨TL, TC, TD, TR⟩ := T
  have hz : zero ∈ NCL (zero ::ₘ Γ) := by simp [pol]
  obtain ⟨X, hX⟩ := Multiset.exists_cons_of_mem (Multiset.mem_of_le hL hz)
  simp only at hX
  obtain ⟨hTL, hTC, hTD, hTR, hTmu⟩ := classicalSeq_parts hT
  have hs : ClassicalSeq ⟪TL ; 0 ⊢ 0 ; TR⟫ := ⟨allIn_mk.2 ⟨hTL, by simp, by simp, hTR⟩, hTmu⟩
  have hw := cl_within_rule (Rule.zeroL X TR) (by rw [hX]) hs (by simp)
  exact cl_weak_to hw hT rfl (Multiset.zero_le _) (Multiset.zero_le _) rfl

/-- The "bad" permeability rule on the left: a negative formula enters the central zone. -/
theorem cl_inL_neg {Γ Γ' Δ' Δ : Multiset Formula} {A : Formula} (hA : A.pol = .neg)
    (hc : ClShape ⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫) (ih : ClGood ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫) :
    ClGood ⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫ := by
  have hmu : mu ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫ = mu ⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫ + 1 := by
    simp [mu_mk, hA]; omega
  have hN : NCL (A ::ₘ Γ) = NCL Γ := by simp [hA]
  refine ⟨fun h => ?_, fun h T hT hL hC hD hR => ?_⟩
  · by_cases h' : mu ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫ ≤ 1
    · exact cl_within_rule (Rule.inL Γ Γ' Δ' Δ A) rfl ⟨hc, h⟩ (by simpa using ih.1 h')
    · have hcA := allIn_mk.1 hc
      have hw := ih.2 (by omega) ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫
        ⟨allIn_mk.2 ⟨hcA.1, fun B hB => hcA.2.1 B (Multiset.mem_cons_of_mem hB), hcA.2.2.1,
          hcA.2.2.2⟩, by simpa [mu_mk] using h⟩
        (by rw [hN]; exact Multiset.filter_le _ _) le_rfl le_rfl (Multiset.filter_le _ _)
      have hAc : A.IsClassical := hcA.2.1 A (Multiset.mem_cons_self _ _)
      have hw' := cl_weakL {A} hw (by simpa using hAc)
      rwa [add_comm, Multiset.singleton_add] at hw'
  · exact ih.2 (by omega) T hT (by rw [hN]; exact hL)
      ((Multiset.le_cons_self _ _).trans hC) hD hR

/-- The "bad" permeability rule on the right: a positive formula enters the central zone. -/
theorem cl_inR_pos {Γ Γ' Δ' Δ : Multiset Formula} {A : Formula} (hA : A.pol = .pos)
    (hc : ClShape ⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫) (ih : ClGood ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫) :
    ClGood ⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫ := by
  have hmu : mu ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫ = mu ⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫ + 1 := by
    simp [mu_mk, hA]; omega
  have hN : NCR (A ::ₘ Δ) = NCR Δ := by simp [hA]
  refine ⟨fun h => ?_, fun h T hT hL hC hD hR => ?_⟩
  · by_cases h' : mu ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫ ≤ 1
    · exact cl_within_rule (Rule.inR Γ Γ' Δ' Δ A) rfl ⟨hc, h⟩ (by simpa using ih.1 h')
    · have hcA := allIn_mk.1 hc
      have hw := ih.2 (by omega) ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫
        ⟨allIn_mk.2 ⟨hcA.1, hcA.2.1, fun B hB => hcA.2.2.1 B (Multiset.mem_cons_of_mem hB),
          hcA.2.2.2⟩, by simpa [mu_mk] using h⟩
        (Multiset.filter_le _ _) le_rfl le_rfl (by rw [hN]; exact Multiset.filter_le _ _)
      have hAc : A.IsClassical := hcA.2.2.1 A (Multiset.mem_cons_self _ _)
      have hw' := cl_weakR {A} hw (by simpa using hAc)
      rwa [add_comm, Multiset.singleton_add] at hw'
  · exact ih.2 (by omega) T hT hL hC ((Multiset.le_cons_self _ _).trans hD)
      (by rw [hN]; exact hR)

theorem Formula.IsClassical.pol_ne_neu {A : Formula} (h : A.IsClassical) : A.pol ≠ .neu := by
  induction A with
  | atom p ts => exact h
  | one => simp [pol]
  | zero => simp [pol]
  | neg A ih => have := ih h; simp only [pol]; revert this; cases A.pol <;> simp [Pol.dual]
  | conj A B ihA ihB =>
    have h1 := ihA h.1; have h2 := ihB h.2
    simp only [pol]; revert h1 h2; cases A.pol <;> cases B.pol <;> simp [Pol.conj]
  | disj A B ihA ihB =>
    have h1 := ihA h.1; have h2 := ihB h.2
    simp only [pol]; revert h1 h2; cases A.pol <;> cases B.pol <;> simp [Pol.disj]
  | imp A B ihA ihB =>
    have h1 := ihA h.1; have h2 := ihB h.2
    simp only [pol]; revert h1 h2; cases A.pol <;> cases B.pol <;> simp [Pol.imp]
  | call A => simp [pol]
  | cex A => simp [pol]
  | _ => exact h.elim

theorem Formula.IsClassical.neg_of_ne_pos {A : Formula} (h : A.IsClassical) (h' : A.pol ≠ .pos) :
    A.pol = .neg := by
  have := h.pol_ne_neu; revert this h'; cases A.pol <;> simp

theorem Formula.IsClassical.pos_of_ne_neg {A : Formula} (h : A.IsClassical) (h' : A.pol ≠ .neg) :
    A.pol = .pos := by
  have := h.pol_ne_neu; revert this h'; cases A.pol <;> simp

theorem ClShape.rhead {Γ Γ' Δ' Δ : Multiset Formula} {C : Formula}
    (h : ClShape ⟪Γ ; Γ' ⊢ Δ' ; C ::ₘ Δ⟫) : C.IsClassical :=
  (allIn_mk.1 h).2.2.2 _ (Multiset.mem_cons_self _ _)

theorem ClShape.lhead {Γ Γ' Δ' Δ : Multiset Formula} {C : Formula}
    (h : ClShape ⟪C ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫) : C.IsClassical :=
  (allIn_mk.1 h).1 _ (Multiset.mem_cons_self _ _)

/-- One-premise rules where every target of the conclusion is a target of the premise. -/
theorem cl_absorb1 {p c : Sequent} (hr : Rule [p] c) (hc : ClShape c) (ih : ClGood p)
    (hmu : mu p = mu c) (hL : NCL p.L ≤ NCL c.L) (hC : p.CL ≤ c.CL) (hD : p.CR ≤ c.CR)
    (hR : NCR p.R ≤ NCR c.R) : ClGood c :=
  cl_absorb hr hc (by simpa using ih) (fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq; omega)
    (fun h => ⟨p, by simp, by omega, hL, hC, hD, hR⟩)

/-- Two-premise rules with a "main" premise carrying the context and a "side" premise with
`μ = 0`. -/
theorem cl_absorb_side {ps : List Sequent} {p s c : Sequent} (hr : Rule ps c)
    (hps : ∀ q ∈ ps, q = p ∨ q = s) (hp : p ∈ ps) (hc : ClShape c) (ihp : ClGood p)
    (ihs : ClGood s) (hmu : mu p = mu c) (hs : mu s = 0) (hL : NCL p.L ≤ NCL c.L)
    (hC : p.CL ≤ c.CL) (hD : p.CR ≤ c.CR) (hR : NCR p.R ≤ NCR c.R) : ClGood c :=
  cl_absorb hr hc (fun q hq => by rcases hps q hq with rfl | rfl <;> assumption)
    (fun h q hq => by rcases hps q hq with rfl | rfl <;> omega)
    (fun h => ⟨p, hp, by omega, hL, hC, hD, hR⟩)

/-- Multiplicative two-premise rules whose principal and active formulas contribute
to `μ`. -/
theorem cl_absorb_mult {p1 p2 c : Sequent} (hr : Rule [p1, p2] c) (hc : ClShape c)
    (ih1 : ClGood p1) (ih2 : ClGood p2) (hmu : mu p1 + mu p2 = mu c + 1) (h1 : 1 ≤ mu p1)
    (h2 : 1 ≤ mu p2) (hL1 : NCL p1.L ≤ NCL c.L) (hC1 : p1.CL ≤ c.CL) (hD1 : p1.CR ≤ c.CR)
    (hR1 : NCR p1.R ≤ NCR c.R) (hL2 : NCL p2.L ≤ NCL c.L) (hC2 : p2.CL ≤ c.CL)
    (hD2 : p2.CR ≤ c.CR) (hR2 : NCR p2.R ≤ NCR c.R) : ClGood c := by
  refine cl_absorb hr hc (by simpa using ⟨ih1, ih2⟩) (fun h q hq => ?_) (fun h => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> omega
  · by_cases h' : 2 ≤ mu p1
    · exact ⟨p1, by simp, h', hL1, hC1, hD1, hR1⟩
    · exact ⟨p2, by simp, by omega, hL2, hC2, hD2, hR2⟩

end LU
