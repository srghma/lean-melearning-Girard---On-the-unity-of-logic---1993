module

public import RequestProject.LU.NeutralInt

/-!
# The intuitionistic fragment: infrastructure

Following the proof of the theorem of §6, for a sequent `S = Γ;Γ' ⊢ ;Δ` made of
intuitionistic formulas (in a cut-free proof of an intuitionistic sequent the right central
zone stays empty), let `ν(S)` be the number of formulas of `Δ`.  When `ν(S) ≠ 1` (this
includes `ν(S) = 0`), "one can easily produce ... another proof of `Γ,Λ;Γ',Λ' ⊢ ;Π` where `Π`
has been obtained from `Δ` by adding formulas, or removing atomic or positive ones".

* `nrem A`: `A` is *not removable*, i.e. neutral and not atomic;
* `IntGood S`: the invariant proved by induction on cut-free proofs: if `ν(S) = 1` then `S`
  is provable within the intuitionistic fragment, and if `ν(S) ≠ 1` then every
  intuitionistic sequent `T` (`T = Λ;Λ' ⊢ ;C`) whose zones contain those of `S`, except
  possibly for removable formulas of `Δ`, is provable within the fragment.
-/

@[expose] public section

namespace LU

variable {n : ℕ}

open Formula

namespace Formula

/-- Is the formula atomic? -/
def isAtom : Formula n → Bool
  | atom _ _ => true
  | _ => false

/-- Non-removable formulas: neutral formulas which are not atomic. -/
def nrem (A : Formula n) : Bool := decide (A.pol = .neu) && !A.isAtom

@[simp] theorem isAtom_subst {m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).isAtom = A.isAtom := by
  cases A <;> rfl

@[simp] theorem nrem_shift (A : Formula n) : A.shift.nrem = A.nrem := by
  simp [nrem, shift]

theorem nrem_of_pos {A : Formula n} (h : A.pol = .pos) : A.nrem = false := by
  simp [nrem, h]

theorem IsIntuitionistic.pol_ne_neg {A : Formula n} (h : A.IsIntuitionistic) : A.pol ≠ .neg := by
  induction A with
  | atom p ts => exact h
  | one => simp [pol]
  | zero => simp [pol]
  | conj A B ihA ihB =>
    have h1 := ihA h.1; have h2 := ihB h.2
    simp only [pol]; revert h1 h2; cases A.pol <;> cases B.pol <;> simp [Pol.conj]
  | disj A B ihA ihB =>
    have h1 := ihA h.1; have h2 := ihB h.2
    simp only [pol]; revert h1 h2; cases A.pol <;> cases B.pol <;> simp [Pol.disj]
  | iimp A B ihA ihB =>
    have h2 := ihB h.2
    simp only [pol]; revert h2; cases A.pol <;> cases B.pol <;> simp [Pol.iimp]
  | lall A ihA =>
    have h1 := ihA h
    simp only [pol]; revert h1; cases A.pol <;> simp [Pol.lall]
  | cex A => simp [pol]
  | _ => exact h.elim

end Formula

/-- The non-removable formulas of a multiset. -/
abbrev NR (Δ : Multiset (Formula n)) : Multiset (Formula n) := Δ.filter (fun A => A.nrem = true)

/-- Shape of the sequents occurring in a cut-free proof of an intuitionistic sequent. -/
def IntShape (S : Sequent) : Prop := AllIn IsIntuitionistic S ∧ S.CR = 0

theorem IntShape.cr_eq {L C CR R : Multiset (Formula n)} (h : IntShape ⟪L ; C ⊢ CR ; R⟫) :
    CR = 0 := h.2

/-- Provability within the intuitionistic fragment. -/
abbrev IntWithin (S : Sequent) : Prop := ProvableWithin .intuitionistic S

/-- The invariant proved by induction on a cut-free proof. -/
def IntGood (S : Sequent) : Prop :=
  (Multiset.card S.R = 1 → IntWithin S) ∧
  (Multiset.card S.R ≠ 1 → ∀ TL TC TR : Multiset (Formula S.scope),
    IntSeq ⟪TL ; TC ⊢ 0 ; TR⟫ → S.L ≤ TL → S.CL ≤ TC → NR S.R ≤ TR →
      IntWithin ⟪TL ; TC ⊢ 0 ; TR⟫)

theorem IntWithin.intSeq {S : Sequent} (h : IntWithin S) : IntSeq S := by
  cases h with
  | mk _ _ _ h _ => exact h

theorem within_rule {ps : List Sequent} {c T : Sequent} (hr : Rule ps c) (heq : c = T)
    (hT : IntSeq T) (hps : ∀ p ∈ ps, IntWithin p) : IntWithin T := by
  subst heq; exact .mk ps c hr hT hps

theorem within_weakCL {L C R : Multiset (Formula n)} (E : Multiset (Formula n))
    (h : IntWithin ⟪L ; C ⊢ 0 ; R⟫) (hE : ∀ A ∈ E, A.IsIntuitionistic) :
    IntWithin ⟪L ; C + E ⊢ 0 ; R⟫ := by
  induction E using Multiset.induction with
  | empty => simpa using h
  | cons A E ih =>
    have ih' := ih (fun B hB => hE B (Multiset.mem_cons_of_mem hB))
    have hs := ih'.intSeq
    refine within_rule (Rule.weakL L (C + E) 0 R A) (by simp) ?_ (by simpa using ih')
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨?_, rfl, h3⟩
    simp only [allIn_mk] at h1 ⊢
    refine ⟨h1.1, ?_, h1.2.2⟩
    intro B hB
    simp only [Multiset.add_cons, Multiset.mem_cons] at hB
    rcases hB with rfl | hB
    · exact hE _ (Multiset.mem_cons_self _ _)
    · exact h1.2.1 B hB

theorem within_weakCL' {L C R TC : Multiset (Formula n)}
    (h : IntWithin ⟪L ; C ⊢ 0 ; R⟫) (hT : IntSeq ⟪L ; TC ⊢ 0 ; R⟫) (hC : C ≤ TC) :
    IntWithin ⟪L ; TC ⊢ 0 ; R⟫ := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 hC
  obtain ⟨hA, -, _⟩ := hT
  apply within_weakCL E h
  intro A hA'
  exact hA A (by simp [Sequent.formulas, hA'])

/-- Absorption: a target of the conclusion is a target of a premise. -/
theorem IntGood.absorb {p : Sequent} {TL TC TR : Multiset (Formula p.scope)} (hp : IntGood p)
    (hcard : Multiset.card p.R ≠ 1) (hT : IntSeq ⟪TL ; TC ⊢ 0 ; TR⟫) (hL : p.L ≤ TL)
    (hC : p.CL ≤ TC) (hR : NR p.R ≤ TR) : IntWithin ⟪TL ; TC ⊢ 0 ; TR⟫ :=
  hp.2 hcard TL TC TR hT hL hC hR

end LU

namespace LU

open Formula

theorem intSeq_mk {L C : Multiset (Formula n)} {Z : Formula n} (hL : ∀ A ∈ L, A.IsIntuitionistic)
    (hC : ∀ A ∈ C, A.IsIntuitionistic) (hZ : Z.IsIntuitionistic) : IntSeq ⟪L ; C ⊢ 0 ; {Z}⟫ :=
  ⟨allIn_mk.2 ⟨hL, hC, by simp, by simpa using hZ⟩, rfl, by simp⟩

theorem tgt_decomp {TL TC TR L C : Multiset (Formula n)} (hT : IntSeq ⟪TL ; TC ⊢ 0 ; TR⟫)
    (hL : L ≤ TL) (hC : C ≤ TC) :
    ∃ E E' Z, TL = L + E ∧ TC = C + E' ∧ TR = {Z} ∧ (∀ A ∈ E, A.IsIntuitionistic) ∧
      (∀ A ∈ E', A.IsIntuitionistic) ∧ Z.IsIntuitionistic := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 hL
  obtain ⟨E', rfl⟩ := Multiset.le_iff_exists_add.1 hC
  obtain ⟨hA, -, h1⟩ := hT
  obtain ⟨Z, rfl⟩ := Multiset.card_eq_one.1 (show Multiset.card TR = 1 from h1)
  simp only [allIn_mk, Multiset.mem_add, or_imp, forall_and, Multiset.mem_singleton,
    forall_eq] at hA
  exact ⟨E, E', Z, rfl, rfl, rfl, hA.1.2, hA.2.1.2, hA.2.2.2⟩

theorem forall_mem_sh' {Γ : Multiset (Formula n)} (h : ∀ A ∈ Γ, A.IsIntuitionistic) :
    ∀ A ∈ sh Γ, A.IsIntuitionistic := forall_mem_sh subClosed_intuitionistic h

/-- Rules whose conclusion has exactly one formula on the right, as well as all premises. -/
theorem good_card1 {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (hc : IntShape c)
    (h1 : Multiset.card c.R = 1) (hall : ∀ p ∈ ps, Multiset.card p.R = 1)
    (ih : ∀ p ∈ ps, IntGood p) : IntGood c :=
  ⟨fun _ => within_rule hr rfl ⟨hc.1, hc.2, h1⟩ fun p hp => (ih p hp).1 (hall p hp),
    fun h => absurd h1 h⟩

theorem NR_cons_of_rem {A : Formula n} (hA : A.nrem = false) (Δ : Multiset (Formula n)) :
    NR (A ::ₘ Δ) = NR Δ := by
  simp [hA]

theorem NR_cons_of_nrem {A : Formula n} (hA : A.nrem = true) (Δ : Multiset (Formula n)) :
    NR (A ::ₘ Δ) = A ::ₘ NR Δ := by
  simp [hA]

/-- One-premise right rules whose principal formula is removable. -/
theorem good_right_rem {Γ Γ' Δ : Multiset (Formula n)} {A C : Formula n}
    (hr : Rule [⟪Γ ; Γ' ⊢ 0 ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ 0 ; C ::ₘ Δ⟫)
    (hc : IntShape ⟪Γ ; Γ' ⊢ 0 ; C ::ₘ Δ⟫) (hA : A.nrem = false) (hCn : C.nrem = false)
    (ih : IntGood ⟪Γ ; Γ' ⊢ 0 ; A ::ₘ Δ⟫) : IntGood ⟪Γ ; Γ' ⊢ 0 ; C ::ₘ Δ⟫ := by
  refine ⟨fun h1 => within_rule hr rfl ⟨hc.1, hc.2, h1⟩ (by simpa using ih.1 (by simpa using h1)),
    fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ih.absorb (by simpa using h1) hT hL hC ?_⟩
  simpa [NR_cons_of_rem hA, NR_cons_of_rem hCn] using hR

/-- One-premise left (or structural) rules keeping the right-hand side. -/
theorem good_left1 {Γ Γ' Δ L0 C0 L1 C1 : Multiset (Formula n)}
    (hr : ∀ Γ Γ' Δ, Rule [⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; Δ⟫] ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫)
    (hc : IntShape ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫) (hp : IntShape ⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; Δ⟫)
    (ih : IntGood ⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; Δ⟫) : IntGood ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩ (by simpa using ih.1 h1),
    fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp.1
  have hcA := allIn_mk.1 hc.1
  simp only [Multiset.mem_add, or_imp, forall_and] at hpA hcA
  refine within_rule (hr (Γ + E) (Γ' + E') {Z}) (by simp [add_assoc]) hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine ih.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) (by simp) (by simpa using hR)
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.2.1.1, hpA.2.1.2, hE'⟩

/-- Two-premise additive left rules keeping the right-hand side. -/
theorem good_left2 {Γ Γ' Δ L0 C0 L1 C1 L2 C2 : Multiset (Formula n)}
    (hr : ∀ Γ Γ' Δ, Rule [⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; Δ⟫, ⟪L2 + Γ ; C2 + Γ' ⊢ 0 ; Δ⟫]
      ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫)
    (hc : IntShape ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫) (hp1 : IntShape ⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; Δ⟫)
    (hp2 : IntShape ⟪L2 + Γ ; C2 + Γ' ⊢ 0 ; Δ⟫)
    (ih1 : IntGood ⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; Δ⟫) (ih2 : IntGood ⟪L2 + Γ ; C2 + Γ' ⊢ 0 ; Δ⟫) :
    IntGood ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ⟨ih1.1 h1, ih2.1 h1⟩), fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp1.1
  have hpA2 := allIn_mk.1 hp2.1
  simp only [Multiset.mem_add, or_imp, forall_and] at hpA hpA2
  refine within_rule (hr (Γ + E) (Γ' + E') {Z}) (by simp [add_assoc]) hT ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨ih1.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) (by simp) (by simpa using hR),
    ih2.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) (by simp) (by simpa using hR)⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.2.1.1, hpA.2.1.2, hE'⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA2.1.1, hpA2.1.2, hE⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA2.2.1.1, hpA2.2.1.2, hE'⟩

theorem NR_sh (Δ : Multiset (Formula n)) : NR (sh Δ) = sh (NR Δ) := by
  simp [Multiset.filter_map]

/-- One-premise left rules with an eigenvariable (context weakened into the scope `n + 1`). -/
theorem good_left_sh {Γ Γ' Δ L0 C0 : Multiset (Formula n)} {L1 C1 : Multiset (Formula (n + 1))}
    (hr : ∀ Γ Γ' Δ, Rule [⟪L1 + sh Γ ; C1 + sh Γ' ⊢ 0 ; sh Δ⟫] ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫)
    (hc : IntShape ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫)
    (hp : IntShape ⟪L1 + sh Γ ; C1 + sh Γ' ⊢ 0 ; sh Δ⟫)
    (ih : IntGood ⟪L1 + sh Γ ; C1 + sh Γ' ⊢ 0 ; sh Δ⟫) : IntGood ⟪L0 + Γ ; C0 + Γ' ⊢ 0 ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ih.1 (by simpa using h1)), fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp.1
  simp only [Multiset.mem_add, or_imp, forall_and] at hpA
  refine within_rule (hr (Γ + E) (Γ' + E') {Z}) (by simp [add_assoc]) hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine ih.2 (by simpa using h1) _ _ _ (intSeq_mk ?_ ?_ ?_) (by simp) (by simp) ?_
  · simp only [Multiset.map_add, Multiset.mem_add, or_imp, forall_and]
    exact ⟨hpA.1.1, hpA.1.2, forall_mem_sh' hE⟩
  · simp only [Multiset.map_add, Multiset.mem_add, or_imp, forall_and]
    exact ⟨hpA.2.1.1, hpA.2.1.2, forall_mem_sh' hE'⟩
  · exact subClosed_intuitionistic.shift _ hZ
  · rw [NR_sh]; simpa using Multiset.map_le_map (f := Formula.shift) hR

theorem NR_le_single_of_nrem {C Z : Formula n} {Δ : Multiset (Formula n)} (hC : C.nrem = true)
    (h : NR (C ::ₘ Δ) ≤ {Z}) : Z = C ∧ NR Δ = 0 := by
  rw [NR_cons_of_nrem hC] at h
  have h1 := Multiset.card_le_card h
  simp only [Multiset.card_cons, Multiset.card_singleton] at h1
  have h0 : NR Δ = 0 := Multiset.card_eq_zero.1 (by omega)
  rw [h0] at h
  exact ⟨(Multiset.mem_singleton.1 (Multiset.mem_of_le h (Multiset.mem_cons_self _ _))).symm, h0⟩

theorem NR_cons_le (A : Formula n) (Δ : Multiset (Formula n)) : NR (A ::ₘ Δ) ≤ A ::ₘ NR Δ := by
  cases h : A.nrem
  · rw [NR_cons_of_rem h]; exact Multiset.le_cons_self _ _
  · rw [NR_cons_of_nrem h]

/-- One-premise right rules whose principal formula is not removable. -/
theorem good_right_nrem {Γ Γ' Δ L1 C1 : Multiset (Formula n)} {A C : Formula n}
    (hr : ∀ Γ Γ' Δ, Rule [⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ 0 ; C ::ₘ Δ⟫)
    (hCn : C.nrem = true)
    (hc : IntShape ⟪Γ ; Γ' ⊢ 0 ; C ::ₘ Δ⟫) (hp : IntShape ⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; A ::ₘ Δ⟫)
    (ih : IntGood ⟪L1 + Γ ; C1 + Γ' ⊢ 0 ; A ::ₘ Δ⟫) : IntGood ⟪Γ ; Γ' ⊢ 0 ; C ::ₘ Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ih.1 (by simpa using h1)), fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  obtain ⟨rfl, h0⟩ := NR_le_single_of_nrem hCn hR
  have hpA := allIn_mk.1 hp.1
  simp only [Multiset.mem_add, Multiset.mem_cons, or_imp, forall_and, forall_eq] at hpA
  refine within_rule (hr (Γ + E) (Γ' + E') 0) (by simp) hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine ih.2 (by simpa using h1) _ _ _ (intSeq_mk ?_ ?_ hpA.2.2.2.1) (by simp) (by simp) ?_
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.2.1.1, hpA.2.1.2, hE'⟩
  · simpa [h0] using NR_cons_le A Δ

end LU
