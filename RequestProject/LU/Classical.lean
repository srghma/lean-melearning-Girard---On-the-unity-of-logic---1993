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

variable {n : ℕ}

open Formula

/-- The negative formulas of a multiset. -/
def muL (Γ : Multiset (Formula n)) : ℕ := Multiset.card (Γ.filter (fun A => A.pol = .neg))

/-- The positive formulas of a multiset. -/
def muR (Δ : Multiset (Formula n)) : ℕ := Multiset.card (Δ.filter (fun A => A.pol = .pos))

/-- Non-contributing formulas of a left linear zone. -/
abbrev NCL (Γ : Multiset (Formula n)) : Multiset (Formula n) := Γ.filter (fun A => A.pol ≠ .neg)

/-- Non-contributing formulas of a right linear zone. -/
abbrev NCR (Δ : Multiset (Formula n)) : Multiset (Formula n) := Δ.filter (fun A => A.pol ≠ .pos)

theorem mu_mk (L : Multiset (Formula n)) (C D : Finset (Formula n)) (R : Multiset (Formula n)) :
    mu ⟪L ; C ⊢ D ; R⟫ = muL L + muR R := rfl

@[simp] theorem muL_zero : muL (0 : Multiset (Formula n)) = 0 := rfl
@[simp] theorem muR_zero : muR (0 : Multiset (Formula n)) = 0 := rfl
@[simp] theorem muL_add (a b : Multiset (Formula n)) : muL (a + b) = muL a + muL b := by
  simp [muL]
@[simp] theorem muR_add (a b : Multiset (Formula n)) : muR (a + b) = muR a + muR b := by
  simp [muR]
@[simp] theorem muL_cons (A : Formula n) (a : Multiset (Formula n)) :
    muL (A ::ₘ a) = (if A.pol = .neg then 1 else 0) + muL a := by
  simp only [muL, Multiset.filter_cons]; split_ifs <;> simp [add_comm]
@[simp] theorem muR_cons (A : Formula n) (a : Multiset (Formula n)) :
    muR (A ::ₘ a) = (if A.pol = .pos then 1 else 0) + muR a := by
  simp only [muR, Multiset.filter_cons]; split_ifs <;> simp [add_comm]
@[simp] theorem muL_singleton (A : Formula n) : muL {A} = if A.pol = .neg then 1 else 0 := by
  simpa using muL_cons A 0
@[simp] theorem muR_singleton (A : Formula n) : muR {A} = if A.pol = .pos then 1 else 0 := by
  simpa using muR_cons A 0

theorem NCL_eq_self {Γ : Multiset (Formula n)} (h : muL Γ = 0) : NCL Γ = Γ := by
  rw [Multiset.filter_eq_self]
  intro A hA hA'
  have : 0 < muL Γ := Multiset.card_pos_iff_exists_mem.2 ⟨A, by simp [hA, hA']⟩
  omega

theorem NCR_eq_self {Δ : Multiset (Formula n)} (h : muR Δ = 0) : NCR Δ = Δ := by
  rw [Multiset.filter_eq_self]
  intro A hA hA'
  have : 0 < muR Δ := Multiset.card_pos_iff_exists_mem.2 ⟨A, by simp [hA, hA']⟩
  omega

theorem NCL_le_of_add {A Γ X : Multiset (Formula n)} (h : NCL (A + Γ) ≤ A + X) : NCL Γ ≤ X := by
  classical
  rw [Multiset.le_iff_count] at h ⊢
  intro a
  have := h a
  simp only [Multiset.filter_add, Multiset.count_add, Multiset.count_filter] at this ⊢
  split_ifs at this ⊢ <;> omega

theorem NCR_le_of_add {A Γ X : Multiset (Formula n)} (h : NCR (A + Γ) ≤ A + X) : NCR Γ ≤ X := by
  classical
  rw [Multiset.le_iff_count] at h ⊢
  intro a
  have := h a
  simp only [Multiset.filter_add, Multiset.count_add, Multiset.count_filter] at this ⊢
  split_ifs at this ⊢ <;> omega

/-- Shape of the sequents occurring in a cut-free proof of a classical sequent. -/
abbrev ClShape (S : Sequent n) : Prop := AllIn IsClassical S

/-- Provability within the classical fragment. -/
abbrev ClWithin (S : Sequent n) : Prop := ProvableWithin .classical S

/-- The invariant proved by induction on a cut-free proof (see the module docstring). -/
def ClGood (S : Sequent n) : Prop :=
  (mu S ≤ 1 → ClWithin S) ∧
  (2 ≤ mu S → ∀ (TL : Multiset (Formula n)) (TC TD : Finset (Formula n))
    (TR : Multiset (Formula n)), ClassicalSeq ⟪TL ; TC ⊢ TD ; TR⟫ →
    NCL S.L ≤ TL → S.CL ⊆ TC → S.CR ⊆ TD → NCR S.R ≤ TR → ClWithin ⟪TL ; TC ⊢ TD ; TR⟫)

theorem ClWithin.classicalSeq {S : Sequent n} (h : ClWithin S) : ClassicalSeq S := by
  cases h with
  | mk _ _ _ h _ => exact h

theorem cl_within_rule {ps : List (Premise n)} {c T : Sequent n} (hr : Rule ps c) (heq : c = T)
    (hT : ClassicalSeq T) (hps : ∀ p ∈ ps, p.All ClWithin) : ClWithin T := by
  subst heq; exact .mk' ps c hr hT hps

theorem cl_weakL {L R : Multiset (Formula n)} {C D : Finset (Formula n)}
    (E : Finset (Formula n)) (h : ClWithin ⟪L ; C ⊢ D ; R⟫) (hE : ∀ A ∈ E, A.IsClassical) :
    ClWithin ⟪L ; C ∪ E ⊢ D ; R⟫ := by
  induction E using Finset.induction_on with
  | empty => simpa using h
  | insert A E _ ih =>
    have ih' := ih (fun B hB => hE B (Finset.mem_insert_of_mem hB))
    obtain ⟨h1, h2⟩ := ih'.classicalSeq
    refine cl_within_rule (Rule.weakL L (C ∪ E) D R A) (by simp) ⟨?_, h2⟩ (by simpa using ih')
    simp only [allIn_mk] at h1 ⊢
    refine ⟨h1.1, ?_, h1.2.2⟩
    intro B hB
    simp only [Finset.union_insert, Finset.mem_insert] at hB
    rcases hB with rfl | hB
    · exact hE _ (Finset.mem_insert_self _ _)
    · exact h1.2.1 B hB

theorem cl_weakR {L R : Multiset (Formula n)} {C D : Finset (Formula n)}
    (E : Finset (Formula n)) (h : ClWithin ⟪L ; C ⊢ D ; R⟫) (hE : ∀ A ∈ E, A.IsClassical) :
    ClWithin ⟪L ; C ⊢ D ∪ E ; R⟫ := by
  induction E using Finset.induction_on with
  | empty => simpa using h
  | insert A E _ ih =>
    have ih' := ih (fun B hB => hE B (Finset.mem_insert_of_mem hB))
    obtain ⟨h1, h2⟩ := ih'.classicalSeq
    refine cl_within_rule (Rule.weakR L C (D ∪ E) R A) (by simp) ⟨?_, h2⟩ (by simpa using ih')
    simp only [allIn_mk] at h1 ⊢
    refine ⟨h1.1, h1.2.1, ?_, h1.2.2.2⟩
    intro B hB
    simp only [Finset.union_insert, Finset.mem_insert] at hB
    rcases hB with rfl | hB
    · exact hE _ (Finset.mem_insert_self _ _)
    · exact h1.2.2.1 B hB

/-- Weakening of the central zones, towards a target sequent. -/
theorem cl_weak_to {L R : Multiset (Formula n)} {C D TC TD : Finset (Formula n)}
    (h : ClWithin ⟪L ; C ⊢ D ; R⟫) (hT : ClassicalSeq ⟪L ; TC ⊢ TD ; R⟫) (hC : C ⊆ TC)
    (hD : D ⊆ TD) : ClWithin ⟪L ; TC ⊢ TD ; R⟫ := by
  obtain ⟨hA, _⟩ := hT
  rw [allIn_mk] at hA
  have := cl_weakR TD (cl_weakL TC h fun A hA' => hA.2.1 A hA') fun A hA' => hA.2.2.1 A hA'
  rwa [Finset.union_eq_right.2 hC, Finset.union_eq_right.2 hD] at this

/-- Using the invariant of a premise towards a target sequent. -/
theorem ClGood.apply {p : Sequent n} {TL TR : Multiset (Formula n)} {TC TD : Finset (Formula n)}
    (hp : ClGood p) (hT : ClassicalSeq ⟪TL ; TC ⊢ TD ; TR⟫)
    (hle : mu p ≤ 1 → TL = p.L ∧ TR = p.R) (hL : NCL p.L ≤ TL) (hC : p.CL ⊆ TC)
    (hD : p.CR ⊆ TD) (hR : NCR p.R ≤ TR) : ClWithin ⟪TL ; TC ⊢ TD ; TR⟫ := by
  by_cases h : mu p ≤ 1
  · obtain ⟨rfl, rfl⟩ := hle h
    exact cl_weak_to (hp.1 h) hT hC hD
  · exact hp.2 (by omega) TL TC TD TR hT hL hC hD hR

/-- Rules for which the conclusion can always be obtained from a premise. -/
theorem cl_absorb {ps : List (Premise n)} {c : Sequent n} (hr : Rule ps c) (hc : ClShape c)
    (ih : ∀ q ∈ ps, q.All ClGood) (h1 : mu c ≤ 1 → ∀ q ∈ ps, q.All (fun s => mu s ≤ 1))
    (h2 : 2 ≤ mu c → ∃ (L : Multiset (Formula n)) (C D : Finset (Formula n))
      (R : Multiset (Formula n)), Premise.same ⟪L ; C ⊢ D ; R⟫ ∈ ps ∧
      2 ≤ mu ⟪L ; C ⊢ D ; R⟫ ∧ NCL L ≤ NCL c.L ∧ C ⊆ c.CL ∧ D ⊆ c.CR ∧ NCR R ≤ NCR c.R) :
    ClGood c := by
  refine ⟨fun hmu => cl_within_rule hr rfl ⟨hc, hmu⟩ fun q hq =>
      ((ih q hq).imp fun _ h => h.1).mp (h1 hmu q hq),
    fun hmu TL TC TD TR hT hL hC hD hR => ?_⟩
  obtain ⟨L, C, D, R, hq, hq2, hqL, hqC, hqD, hqR⟩ := h2 hmu
  exact (ih _ hq).2 hq2 TL TC TD TR hT (hqL.trans hL) (hqC.trans hC) (hqD.trans hD)
    (hqR.trans hR)

/-- Admissible transformations of the contexts in a rule: the identity, and the shift used
for the eigenvariable condition (`f` acts on the linear zones, `g` on the central zones, and
`pr` makes a premise out of a sequent of the target scope). -/
structure CtxMap {n m : ℕ} (f : Multiset (Formula n) → Multiset (Formula m))
    (g : Finset (Formula n) → Finset (Formula m)) (pr : Sequent m → Premise n) : Prop where
  all : ∀ (Q : ∀ {k : ℕ}, Sequent k → Prop) (s : Sequent m), (pr s).All Q ↔ Q s
  add : ∀ a b, f (a + b) = f a + f b
  cl : ∀ a, (∀ A ∈ a, A.IsClassical) → ∀ A ∈ f a, A.IsClassical
  muL : ∀ a, muL (f a) = muL a
  muR : ∀ a, muR (f a) = muR a
  ncl : ∀ a, NCL (f a) = f (NCL a)
  ncr : ∀ a, NCR (f a) = f (NCR a)
  mono : ∀ a b, a ≤ b → f a ≤ f b
  union : ∀ a b, g (a ∪ b) = g a ∪ g b
  clc : ∀ a, (∀ A ∈ a, A.IsClassical) → ∀ A ∈ g a, A.IsClassical
  monoc : ∀ a b, a ⊆ b → g a ⊆ g b

theorem ctxMap_id :
    CtxMap (id : Multiset (Formula n) → Multiset (Formula n)) id Premise.same where
  all _ _ := Iff.rfl
  add _ _ := rfl
  cl _ h := h
  muL _ := rfl
  muR _ := rfl
  ncl _ := rfl
  ncr _ := rfl
  mono _ _ h := h
  union _ _ := rfl
  clc _ h := h
  monoc _ _ h := h

theorem ctxMap_sh :
    CtxMap (sh : Multiset (Formula n) → Multiset (Formula (n + 1))) shc Premise.up where
  all _ _ := Iff.rfl
  add a b := Multiset.map_add _ _ _
  cl _ h := forall_mem_sh subClosed_classical h
  muL a := by simp [muL, Multiset.filter_map]
  muR a := by simp [muR, Multiset.filter_map]
  ncl a := by simp [Multiset.filter_map]
  ncr a := by simp [Multiset.filter_map]
  mono _ _ h := Multiset.map_le_map h
  union a b := Finset.image_union _ _
  clc _ h := forall_mem_shc subClosed_classical h
  monoc _ _ h := Finset.image_subset_image h

theorem forall_mem_add_iff {F : ∀ {n : ℕ}, Formula n → Prop} {a b : Multiset (Formula n)} :
    (∀ A ∈ a + b, F A) ↔ (∀ A ∈ a, F A) ∧ (∀ A ∈ b, F A) := by
  simp only [Multiset.mem_add, or_imp, forall_and]

theorem forall_mem_union_iff {F : ∀ {n : ℕ}, Formula n → Prop} {a b : Finset (Formula n)} :
    (∀ A ∈ a ∪ b, F A) ↔ (∀ A ∈ a, F A) ∧ (∀ A ∈ b, F A) := by
  simp only [Finset.mem_union, or_imp, forall_and]

/-- Decomposition of a target sequent containing the non-contributing formulas `L0`, `R0`
and the central formulas `C0`, `D0` of the principal part of a rule. -/
theorem cl_tgt_decomp {TL TR L0 R0 Γ Δ : Multiset (Formula n)}
    {TC TD C0 D0 Γ' Δ' : Finset (Formula n)}
    (hL0 : NCL L0 = L0) (hR0 : NCR R0 = R0) (hL : NCL (L0 + Γ) ≤ TL)
    (hC : C0 ∪ Γ' ⊆ TC) (hD : D0 ∪ Δ' ⊆ TD) (hR : NCR (R0 + Δ) ≤ TR) :
    ∃ Tl Tc Td Tr, TL = L0 + Tl ∧ TC = C0 ∪ Tc ∧ TD = D0 ∪ Td ∧ TR = R0 + Tr ∧ NCL Γ ≤ Tl ∧
      Γ' ⊆ Tc ∧ Δ' ⊆ Td ∧ NCR Δ ≤ Tr := by
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
  refine ⟨Tl, TC, TD, Tr, rfl, ?_, ?_, rfl, NCL_le_of_add hL,
    Finset.subset_union_right.trans hC, Finset.subset_union_right.trans hD, NCR_le_of_add hR⟩
  · exact (Finset.union_eq_right.2 (Finset.subset_union_left.trans hC)).symm
  · exact (Finset.union_eq_right.2 (Finset.subset_union_left.trans hD)).symm

theorem classicalSeq_parts {L R : Multiset (Formula n)} {C D : Finset (Formula n)}
    (h : ClassicalSeq ⟪L ; C ⊢ D ; R⟫) :
    (∀ A ∈ L, A.IsClassical) ∧ (∀ A ∈ C, A.IsClassical) ∧ (∀ A ∈ D, A.IsClassical) ∧
      (∀ A ∈ R, A.IsClassical) ∧ muL L + muR R ≤ 1 :=
  ⟨(allIn_mk.1 h.1).1, (allIn_mk.1 h.1).2.1, (allIn_mk.1 h.1).2.2.1, (allIn_mk.1 h.1).2.2.2, h.2⟩

/-- A target of a premise of a rule, obtained from the decomposition of a target of the
conclusion. -/
theorem cl_premise_tgt {m : ℕ} {f : Multiset (Formula n) → Multiset (Formula m)}
    {g : Finset (Formula n) → Finset (Formula m)} {pr : Sequent m → Premise n}
    (hf : CtxMap f g pr) {L1 R1 : Multiset (Formula m)} {C1 D1 : Finset (Formula m)}
    {Γ Δ Tl Tr : Multiset (Formula n)} {Γ' Δ' Tc Td : Finset (Formula n)}
    (h1 : muL L1 + muR R1 = 0)
    (hp : ClShape ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫)
    (ih : ClGood ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫)
    (hmu : 2 ≤ mu ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫)
    (hTL : ∀ A ∈ Tl, A.IsClassical) (hTC : ∀ A ∈ Tc, A.IsClassical)
    (hTD : ∀ A ∈ Td, A.IsClassical) (hTR : ∀ A ∈ Tr, A.IsClassical)
    (hTmu : muL Tl + muR Tr ≤ 1)
    (hl : NCL Γ ≤ Tl) (hc : Γ' ⊆ Tc) (hd : Δ' ⊆ Td) (hr : NCR Δ ≤ Tr) :
    ClWithin ⟪L1 + f Tl ; C1 ∪ g Tc ⊢ D1 ∪ g Td ; R1 + f Tr⟫ := by
  have hpA := allIn_mk.1 hp
  simp only [forall_mem_add_iff, forall_mem_union_iff] at hpA
  refine ih.2 hmu _ _ _ _ ⟨allIn_mk.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩ ?_ ?_ ?_ ?_
  · exact forall_mem_add_iff.2 ⟨hpA.1.1, hf.cl _ hTL⟩
  · exact forall_mem_union_iff.2 ⟨hpA.2.1.1, hf.clc _ hTC⟩
  · exact forall_mem_union_iff.2 ⟨hpA.2.2.1.1, hf.clc _ hTD⟩
  · exact forall_mem_add_iff.2 ⟨hpA.2.2.2.1, hf.cl _ hTR⟩
  · simp only [mu_mk, muL_add, muR_add, hf.muL, hf.muR]; omega
  · simp only [Multiset.filter_add, hf.ncl]
    exact add_le_add (Multiset.filter_le _ _) (hf.mono _ _ hl)
  · exact Finset.union_subset_union (Finset.Subset.refl _) (hf.monoc _ _ hc)
  · exact Finset.union_subset_union (Finset.Subset.refl _) (hf.monoc _ _ hd)
  · simp only [Multiset.filter_add, hf.ncr]
    exact add_le_add (Multiset.filter_le _ _) (hf.mono _ _ hr)

/-- One-premise rules whose principal formula and active formulas do not contribute to `μ`:
the conclusion is obtained by applying the same rule to a target of the premise. -/
theorem cl_reapply1 {m : ℕ} {f : Multiset (Formula n) → Multiset (Formula m)}
    {g : Finset (Formula n) → Finset (Formula m)} {pr : Sequent m → Premise n}
    (hf : CtxMap f g pr) {L0 R0 Γ Δ : Multiset (Formula n)} {C0 D0 Γ' Δ' : Finset (Formula n)}
    {L1 R1 : Multiset (Formula m)} {C1 D1 : Finset (Formula m)}
    (hr : ∀ Γ Γ' Δ' Δ, Rule [pr ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫]
      ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫)
    (h0 : muL L0 + muR R0 = 0) (h1 : muL L1 + muR R1 = 0)
    (hc : ClShape ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫)
    (hp : ClShape ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫)
    (ih : ClGood ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫) :
    ClGood ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫ := by
  have hmu : mu ⟪L1 + f Γ ; C1 ∪ g Γ' ⊢ D1 ∪ g Δ' ; R1 + f Δ⟫ =
      mu ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫ := by
    simp only [mu_mk, muL_add, muR_add, hf.muL, hf.muR]; omega
  refine ⟨fun h => cl_within_rule (hr Γ Γ' Δ' Δ) rfl ⟨hc, h⟩
    (by simpa [hf.all] using ih.1 (hmu ▸ h)),
    fun h TL TC TD TR hT hL hC hD hR => ?_⟩
  obtain ⟨Tl, Tc, Td, Tr, rfl, rfl, rfl, rfl, hl, hc', hd, hr'⟩ :=
    cl_tgt_decomp (NCL_eq_self (by omega)) (NCR_eq_self (by omega)) hL hC hD hR
  obtain ⟨hTL, hTC, hTD, hTR, hTmu⟩ := classicalSeq_parts hT
  rw [forall_mem_add_iff] at hTL hTR
  rw [forall_mem_union_iff] at hTC hTD
  simp only [muL_add, muR_add] at hTmu
  refine cl_within_rule (hr Tl Tc Td Tr) rfl hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine (hf.all _ _).2 ?_
  exact cl_premise_tgt hf h1 hp ih (hmu ▸ h) hTL.2 hTC.2 hTD.2 hTR.2 (by omega) hl hc' hd hr'

/-- Two-premise additive rules whose principal formula and active formulas do not
contribute to `μ`. -/
theorem cl_reapply2 {L0 R0 L1 R1 L2 R2 Γ Δ : Multiset (Formula n)}
    {C0 D0 C1 D1 C2 D2 Γ' Δ' : Finset (Formula n)}
    (hr : ∀ Γ Γ' Δ' Δ, Rule [.same ⟪L1 + Γ ; C1 ∪ Γ' ⊢ D1 ∪ Δ' ; R1 + Δ⟫,
      .same ⟪L2 + Γ ; C2 ∪ Γ' ⊢ D2 ∪ Δ' ; R2 + Δ⟫] ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫)
    (h0 : muL L0 + muR R0 = 0) (h1 : muL L1 + muR R1 = 0) (h2 : muL L2 + muR R2 = 0)
    (hc : ClShape ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫)
    (hp1 : ClShape ⟪L1 + Γ ; C1 ∪ Γ' ⊢ D1 ∪ Δ' ; R1 + Δ⟫)
    (hp2 : ClShape ⟪L2 + Γ ; C2 ∪ Γ' ⊢ D2 ∪ Δ' ; R2 + Δ⟫)
    (ih1 : ClGood ⟪L1 + Γ ; C1 ∪ Γ' ⊢ D1 ∪ Δ' ; R1 + Δ⟫)
    (ih2 : ClGood ⟪L2 + Γ ; C2 ∪ Γ' ⊢ D2 ∪ Δ' ; R2 + Δ⟫) :
    ClGood ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫ := by
  have hmu1 : mu ⟪L1 + Γ ; C1 ∪ Γ' ⊢ D1 ∪ Δ' ; R1 + Δ⟫ =
      mu ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫ := by
    simp only [mu_mk, muL_add, muR_add]; omega
  have hmu2 : mu ⟪L2 + Γ ; C2 ∪ Γ' ⊢ D2 ∪ Δ' ; R2 + Δ⟫ =
      mu ⟪L0 + Γ ; C0 ∪ Γ' ⊢ D0 ∪ Δ' ; R0 + Δ⟫ := by
    simp only [mu_mk, muL_add, muR_add]; omega
  refine ⟨fun h => cl_within_rule (hr Γ Γ' Δ' Δ) rfl ⟨hc, h⟩
    (by simpa using ⟨ih1.1 (hmu1 ▸ h), ih2.1 (hmu2 ▸ h)⟩),
    fun h TL TC TD TR hT hL hC hD hR => ?_⟩
  obtain ⟨Tl, Tc, Td, Tr, rfl, rfl, rfl, rfl, hl, hc', hd, hr'⟩ :=
    cl_tgt_decomp (NCL_eq_self (by omega)) (NCR_eq_self (by omega)) hL hC hD hR
  obtain ⟨hTL, hTC, hTD, hTR, hTmu⟩ := classicalSeq_parts hT
  rw [forall_mem_add_iff] at hTL hTR
  rw [forall_mem_union_iff] at hTC hTD
  simp only [muL_add, muR_add] at hTmu
  refine cl_within_rule (hr Tl Tc Td Tr) rfl hT ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨cl_premise_tgt ctxMap_id h1 hp1 ih1 (hmu1 ▸ h) hTL.2 hTC.2 hTD.2 hTR.2 (by omega)
      hl hc' hd hr',
    cl_premise_tgt ctxMap_id h2 hp2 ih2 (hmu2 ▸ h) hTL.2 hTC.2 hTD.2 hTR.2 (by omega)
      hl hc' hd hr'⟩

theorem cl_zeroL (Γ Δ : Multiset (Formula n)) (hc : ClShape ⟪zero ::ₘ Γ ; ∅ ⊢ ∅ ; Δ⟫) :
    ClGood ⟪zero ::ₘ Γ ; ∅ ⊢ ∅ ; Δ⟫ := by
  refine ⟨fun h1 => cl_within_rule (Rule.zeroL Γ Δ) rfl ⟨hc, h1⟩ (by simp),
    fun _ TL TC TD TR hT hL _ _ _ => ?_⟩
  have hz : zero ∈ NCL (zero ::ₘ Γ) := by simp [pol]
  obtain ⟨X, hX⟩ := Multiset.exists_cons_of_mem (Multiset.mem_of_le hL hz)
  obtain ⟨hTL, hTC, hTD, hTR, hTmu⟩ := classicalSeq_parts hT
  have hs : ClassicalSeq ⟪TL ; ∅ ⊢ ∅ ; TR⟫ := ⟨allIn_mk.2 ⟨hTL, by simp, by simp, hTR⟩, hTmu⟩
  have hw := cl_within_rule (Rule.zeroL X TR) (by rw [hX]) hs (by simp)
  exact cl_weak_to hw hT (Finset.empty_subset _) (Finset.empty_subset _)

/-- The "bad" permeability rule on the left: a negative formula enters the central zone. -/
theorem cl_inL_neg {Γ Δ : Multiset (Formula n)} {Γ' Δ' : Finset (Formula n)} {A : Formula n}
    (hA : A.pol = .neg)
    (hc : ClShape ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫) (ih : ClGood ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫) :
    ClGood ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫ := by
  have hmu : mu ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫ = mu ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫ + 1 := by
    simp [mu_mk, hA]; omega
  have hN : NCL (A ::ₘ Γ) = NCL Γ := by simp [hA]
  refine ⟨fun h => ?_, fun h TL TC TD TR hT hL hC hD hR => ?_⟩
  · by_cases h' : mu ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫ ≤ 1
    · exact cl_within_rule (Rule.inL Γ Γ' Δ' Δ A) rfl ⟨hc, h⟩ (by simpa using ih.1 h')
    · have hcA := allIn_mk.1 hc
      have hw := ih.2 (by omega) Γ Γ' Δ' Δ
        ⟨allIn_mk.2 ⟨hcA.1, fun B hB => hcA.2.1 B (Finset.mem_insert_of_mem hB), hcA.2.2.1,
          hcA.2.2.2⟩, by simpa [mu_mk] using h⟩
        (by rw [hN]; exact Multiset.filter_le _ _) (Finset.Subset.refl _)
        (Finset.Subset.refl _) (Multiset.filter_le _ _)
      have hAc : A.IsClassical := hcA.2.1 A (Finset.mem_insert_self _ _)
      have hw' := cl_weakL {A} hw (by simpa using hAc)
      rwa [Finset.union_comm, ← Finset.insert_eq] at hw'
  · exact ih.2 (by omega) TL TC TD TR hT (by rw [hN]; exact hL)
      ((Finset.subset_insert _ _).trans hC) hD hR

/-- The "bad" permeability rule on the right: a positive formula enters the central zone. -/
theorem cl_inR_pos {Γ Δ : Multiset (Formula n)} {Γ' Δ' : Finset (Formula n)} {A : Formula n}
    (hA : A.pol = .pos)
    (hc : ClShape ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫) (ih : ClGood ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫) :
    ClGood ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫ := by
  have hmu : mu ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫ = mu ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫ + 1 := by
    simp [mu_mk, hA]; omega
  have hN : NCR (A ::ₘ Δ) = NCR Δ := by simp [hA]
  refine ⟨fun h => ?_, fun h TL TC TD TR hT hL hC hD hR => ?_⟩
  · by_cases h' : mu ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫ ≤ 1
    · exact cl_within_rule (Rule.inR Γ Γ' Δ' Δ A) rfl ⟨hc, h⟩ (by simpa using ih.1 h')
    · have hcA := allIn_mk.1 hc
      have hw := ih.2 (by omega) Γ Γ' Δ' Δ
        ⟨allIn_mk.2 ⟨hcA.1, hcA.2.1, fun B hB => hcA.2.2.1 B (Finset.mem_insert_of_mem hB),
          hcA.2.2.2⟩, by simpa [mu_mk] using h⟩
        (Multiset.filter_le _ _) (Finset.Subset.refl _) (Finset.Subset.refl _)
        (by rw [hN]; exact Multiset.filter_le _ _)
      have hAc : A.IsClassical := hcA.2.2.1 A (Finset.mem_insert_self _ _)
      have hw' := cl_weakR {A} hw (by simpa using hAc)
      rwa [Finset.union_comm, ← Finset.insert_eq] at hw'
  · exact ih.2 (by omega) TL TC TD TR hT hL hC ((Finset.subset_insert _ _).trans hD)
      (by rw [hN]; exact hR)

theorem Formula.IsClassical.pol_ne_neu {A : Formula n} (h : A.IsClassical) : A.pol ≠ .neu := by
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

theorem Formula.IsClassical.neg_of_ne_pos {A : Formula n} (h : A.IsClassical) (h' : A.pol ≠ .pos) :
    A.pol = .neg := by
  have := h.pol_ne_neu; revert this h'; cases A.pol <;> simp

theorem Formula.IsClassical.pos_of_ne_neg {A : Formula n} (h : A.IsClassical) (h' : A.pol ≠ .neg) :
    A.pol = .pos := by
  have := h.pol_ne_neu; revert this h'; cases A.pol <;> simp

theorem ClShape.rhead {Γ Δ : Multiset (Formula n)} {Γ' Δ' : Finset (Formula n)} {C : Formula n}
    (h : ClShape ⟪Γ ; Γ' ⊢ Δ' ; C ::ₘ Δ⟫) : C.IsClassical :=
  (allIn_mk.1 h).2.2.2 _ (Multiset.mem_cons_self _ _)

theorem ClShape.lhead {Γ Δ : Multiset (Formula n)} {Γ' Δ' : Finset (Formula n)} {C : Formula n}
    (h : ClShape ⟪C ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫) : C.IsClassical :=
  (allIn_mk.1 h).1 _ (Multiset.mem_cons_self _ _)

/-- One-premise rules where every target of the conclusion is a target of the premise. -/
theorem cl_absorb1 {c : Sequent n} {L R : Multiset (Formula n)} {C D : Finset (Formula n)}
    (hr : Rule [.same ⟪L ; C ⊢ D ; R⟫] c) (hc : ClShape c) (ih : ClGood ⟪L ; C ⊢ D ; R⟫)
    (hmu : mu ⟪L ; C ⊢ D ; R⟫ = mu c) (hL : NCL L ≤ NCL c.L) (hC : C ⊆ c.CL) (hD : D ⊆ c.CR)
    (hR : NCR R ≤ NCR c.R) : ClGood c :=
  cl_absorb hr hc (by simpa using ih) (fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq; show mu _ ≤ 1; omega)
    (fun h => ⟨L, C, D, R, by simp, by omega, hL, hC, hD, hR⟩)

/-- Two-premise rules with a "main" premise carrying the context and a "side" premise with
`μ = 0`. -/
theorem cl_absorb_side {ps : List (Premise n)} {s c : Sequent n} {L R : Multiset (Formula n)}
    {C D : Finset (Formula n)}
    (hr : Rule ps c)
    (hps : ∀ q ∈ ps, q = .same ⟪L ; C ⊢ D ; R⟫ ∨ q = .same s) (hp : .same ⟪L ; C ⊢ D ; R⟫ ∈ ps)
    (hc : ClShape c)
    (ihp : ClGood ⟪L ; C ⊢ D ; R⟫) (ihs : ClGood s) (hmu : mu ⟪L ; C ⊢ D ; R⟫ = mu c)
    (hs : mu s = 0) (hL : NCL L ≤ NCL c.L) (hC : C ⊆ c.CL) (hD : D ⊆ c.CR)
    (hR : NCR R ≤ NCR c.R) : ClGood c :=
  cl_absorb hr hc (fun q hq => by rcases hps q hq with rfl | rfl <;> assumption)
    (fun h q hq => by rcases hps q hq with rfl | rfl <;> show mu _ ≤ 1 <;> omega)
    (fun h => ⟨L, C, D, R, hp, by omega, hL, hC, hD, hR⟩)

/-- Multiplicative two-premise rules whose principal and active formulas contribute
to `μ`. -/
theorem cl_absorb_mult {c : Sequent n} {L1 R1 L2 R2 : Multiset (Formula n)}
    {C1 D1 C2 D2 : Finset (Formula n)}
    (hr : Rule [.same ⟪L1 ; C1 ⊢ D1 ; R1⟫, .same ⟪L2 ; C2 ⊢ D2 ; R2⟫] c) (hc : ClShape c)
    (ih1 : ClGood ⟪L1 ; C1 ⊢ D1 ; R1⟫) (ih2 : ClGood ⟪L2 ; C2 ⊢ D2 ; R2⟫)
    (hmu : mu ⟪L1 ; C1 ⊢ D1 ; R1⟫ + mu ⟪L2 ; C2 ⊢ D2 ; R2⟫ = mu c + 1)
    (h1 : 1 ≤ mu ⟪L1 ; C1 ⊢ D1 ; R1⟫) (h2 : 1 ≤ mu ⟪L2 ; C2 ⊢ D2 ; R2⟫)
    (hL1 : NCL L1 ≤ NCL c.L) (hC1 : C1 ⊆ c.CL) (hD1 : D1 ⊆ c.CR)
    (hR1 : NCR R1 ≤ NCR c.R) (hL2 : NCL L2 ≤ NCL c.L) (hC2 : C2 ⊆ c.CL)
    (hD2 : D2 ⊆ c.CR) (hR2 : NCR R2 ≤ NCR c.R) : ClGood c := by
  refine cl_absorb hr hc (by simpa using ⟨ih1, ih2⟩) (fun h q hq => ?_) (fun h => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> show mu _ ≤ 1 <;> omega
  · by_cases h' : 2 ≤ mu ⟪L1 ; C1 ⊢ D1 ; R1⟫
    · exact ⟨L1, C1, D1, R1, by simp, h', hL1, hC1, hD1, hR1⟩
    · exact ⟨L2, C2, D2, R2, by simp, by omega, hL2, hC2, hD2, hR2⟩

end LU
