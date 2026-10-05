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

variable {PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]

variable {n : ℕ}

open Formula

namespace Formula

/-- Is the formula atomic? -/
def isAtom : Formula PS TS n → Bool
  | atom _ _ => true
  | _ => false

/-- Non-removable formulas: neutral formulas which are not atomic. -/
def nrem (A : Formula PS TS n) : Bool := decide (A.pol = .neu) && !A.isAtom

section

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

@[simp] theorem isAtom_subst {m : ℕ} (A : Formula PS TS n) (σ : Subst TS n m) :
    (A.subst σ).isAtom = A.isAtom := by
  cases A <;> rfl

@[simp] theorem nrem_shift (A : Formula PS TS n) : A.shift.nrem = A.nrem := by
  simp [nrem, shift]

theorem nrem_of_pos {A : Formula PS TS n} (h : A.pol = .pos) : A.nrem = false := by
  simp [nrem, h]

theorem IsIntuitionistic.pol_ne_neg {A : Formula PS TS n} (h : A.IsIntuitionistic) : A.pol ≠ .neg := by
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

end

end Formula

/-- The non-removable formulas of a multiset. -/
abbrev NR (Δ : Multiset (Formula PS TS n)) : Multiset (Formula PS TS n) := Δ.filter (fun A => A.nrem = true)

/-- Shape of the sequents occurring in a cut-free proof of an intuitionistic sequent. -/
def IntShape (S : Sequent PS TS n) : Prop := AllIn IsIntuitionistic S ∧ S.CR = ∅

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
theorem IntShape.cr_eq {L R : Multiset (Formula PS TS n)} {C CR : Finset (Formula PS TS n)}
    (h : IntShape ⟪L ; C ⊢ CR ; R⟫) : CR = ∅ := h.2

/-- Provability within the intuitionistic fragment. -/
abbrev IntWithin (S : Sequent PS TS n) : Prop := ProvableWithin .intuitionistic S

/-- The invariant proved by induction on a cut-free proof. -/
def IntGood (S : Sequent PS TS n) : Prop :=
  (Multiset.card S.R = 1 → IntWithin S) ∧
  (Multiset.card S.R ≠ 1 → ∀ (TL : Multiset (Formula PS TS n)) (TC : Finset (Formula PS TS n))
    (TR : Multiset (Formula PS TS n)),
    IntSeq ⟪TL ; TC ⊢ ∅ ; TR⟫ → S.L ≤ TL → S.CL ⊆ TC → NR S.R ≤ TR →
      IntWithin ⟪TL ; TC ⊢ ∅ ; TR⟫)

theorem IntWithin.intSeq {S : Sequent PS TS n} (h : IntWithin S) : IntSeq S := by
  cases h with
  | mk _ _ _ h _ => exact h

theorem within_rule {ps : List (Premise PS TS n)} {c T : Sequent PS TS n} (hr : Rule ps c) (heq : c = T)
    (hT : IntSeq T) (hps : ∀ p ∈ ps, p.All IntWithin) : IntWithin T := by
  subst heq; exact .mk' ps c hr hT hps

theorem within_weakCL {L R : Multiset (Formula PS TS n)} {C : Finset (Formula PS TS n)}
    (E : Finset (Formula PS TS n))
    (h : IntWithin ⟪L ; C ⊢ ∅ ; R⟫) (hE : ∀ A ∈ E, A.IsIntuitionistic) :
    IntWithin ⟪L ; C ∪ E ⊢ ∅ ; R⟫ := by
  induction E using Finset.induction_on with
  | empty => simpa using h
  | insert A E _ ih =>
    have ih' := ih (fun B hB => hE B (Finset.mem_insert_of_mem hB))
    have hs := ih'.intSeq
    refine within_rule (Rule.weakL L (C ∪ E) ∅ R A) (by simp) ?_ (by simpa using ih')
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨?_, rfl, h3⟩
    simp only [allIn_mk] at h1 ⊢
    refine ⟨h1.1, ?_, h1.2.2⟩
    intro B hB
    simp only [Finset.union_insert, Finset.mem_insert] at hB
    rcases hB with rfl | hB
    · exact hE _ (Finset.mem_insert_self _ _)
    · exact h1.2.1 B hB

theorem within_weakCL' {L R : Multiset (Formula PS TS n)} {C TC : Finset (Formula PS TS n)}
    (h : IntWithin ⟪L ; C ⊢ ∅ ; R⟫) (hT : IntSeq ⟪L ; TC ⊢ ∅ ; R⟫) (hC : C ⊆ TC) :
    IntWithin ⟪L ; TC ⊢ ∅ ; R⟫ := by
  obtain ⟨hA, -, _⟩ := hT
  have := within_weakCL TC h fun A hA' => hA A (by simp [Sequent.formulas, hA'])
  rwa [Finset.union_eq_right.2 hC] at this

/-- Absorption: a target of the conclusion is a target of a premise. -/
theorem IntGood.absorb {p : Sequent PS TS n} {TL TR : Multiset (Formula PS TS n)} {TC : Finset (Formula PS TS n)}
    (hp : IntGood p)
    (hcard : Multiset.card p.R ≠ 1) (hT : IntSeq ⟪TL ; TC ⊢ ∅ ; TR⟫) (hL : p.L ≤ TL)
    (hC : p.CL ⊆ TC) (hR : NR p.R ≤ TR) : IntWithin ⟪TL ; TC ⊢ ∅ ; TR⟫ :=
  hp.2 hcard TL TC TR hT hL hC hR

end LU

namespace LU

variable {PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]

open Formula

/-- Inclusion of central zones `C ∪ Γ' ⊆ C ∪ (Γ' ∪ E)` (also under `shc`). -/
local macro "csub" : term =>
  `(by simp only [Finset.image_union, ← Finset.union_assoc]; exact Finset.subset_union_left)

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
theorem intSeq_mk {L : Multiset (Formula PS TS n)} {C : Finset (Formula PS TS n)} {Z : Formula PS TS n}
    (hL : ∀ A ∈ L, A.IsIntuitionistic)
    (hC : ∀ A ∈ C, A.IsIntuitionistic) (hZ : Z.IsIntuitionistic) : IntSeq ⟪L ; C ⊢ ∅ ; {Z}⟫ :=
  ⟨allIn_mk.2 ⟨hL, hC, by simp, by simpa using hZ⟩, rfl, by simp⟩

theorem tgt_decomp {TL TR L : Multiset (Formula PS TS n)} {TC C : Finset (Formula PS TS n)}
    (hT : IntSeq ⟪TL ; TC ⊢ ∅ ; TR⟫) (hL : L ≤ TL) (hC : C ⊆ TC) :
    ∃ E E' Z, TL = L + E ∧ TC = C ∪ E' ∧ TR = {Z} ∧ (∀ A ∈ E, A.IsIntuitionistic) ∧
      (∀ A ∈ E', A.IsIntuitionistic) ∧ Z.IsIntuitionistic := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.1 hL
  obtain ⟨hA, -, h1⟩ := hT
  obtain ⟨Z, rfl⟩ := Multiset.card_eq_one.1 (show Multiset.card TR = 1 from h1)
  simp only [allIn_mk, Multiset.mem_add, or_imp, forall_and, Multiset.mem_singleton,
    forall_eq] at hA
  exact ⟨E, TC, Z, rfl, (Finset.union_eq_right.2 hC).symm, rfl, hA.1.2, hA.2.1, hA.2.2.2⟩

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
theorem forall_mem_sh' {Γ : Multiset (Formula PS TS n)} (h : ∀ A ∈ Γ, A.IsIntuitionistic) :
    ∀ A ∈ sh Γ, A.IsIntuitionistic := forall_mem_sh subClosed_intuitionistic h

/-- Rules whose conclusion has exactly one formula on the right, as well as all premises. -/
theorem good_card1 {ps : List (Premise PS TS n)} {c : Sequent PS TS n} (hr : Rule ps c) (hc : IntShape c)
    (h1 : Multiset.card c.R = 1) (hall : ∀ p ∈ ps, p.All (fun s => Multiset.card s.R = 1))
    (ih : ∀ p ∈ ps, p.All IntGood) : IntGood c :=
  ⟨fun _ => within_rule hr rfl ⟨hc.1, hc.2, h1⟩ fun p hp =>
      ((ih p hp).imp fun _ h => h.1).mp (hall p hp),
    fun h => absurd h1 h⟩

section

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

theorem NR_cons_of_rem {A : Formula PS TS n} (hA : A.nrem = false) (Δ : Multiset (Formula PS TS n)) :
    NR (A ::ₘ Δ) = NR Δ := by
  simp [hA]

theorem NR_cons_of_nrem {A : Formula PS TS n} (hA : A.nrem = true) (Δ : Multiset (Formula PS TS n)) :
    NR (A ::ₘ Δ) = A ::ₘ NR Δ := by
  simp [hA]

end

/-- One-premise right rules whose principal formula is removable. -/
theorem good_right_rem {Γ Δ : Multiset (Formula PS TS n)} {Γ' : Finset (Formula PS TS n)} {A C : Formula PS TS n}
    (hr : Rule [.same ⟪Γ ; Γ' ⊢ ∅ ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ ∅ ; C ::ₘ Δ⟫)
    (hc : IntShape ⟪Γ ; Γ' ⊢ ∅ ; C ::ₘ Δ⟫) (hA : A.nrem = false) (hCn : C.nrem = false)
    (ih : IntGood ⟪Γ ; Γ' ⊢ ∅ ; A ::ₘ Δ⟫) : IntGood ⟪Γ ; Γ' ⊢ ∅ ; C ::ₘ Δ⟫ := by
  refine ⟨fun h1 => within_rule hr rfl ⟨hc.1, hc.2, h1⟩ (by simpa using ih.1 (by simpa using h1)),
    fun h1 TL TC TR hT hL hC hR => ih.absorb (by simpa using h1) hT hL hC ?_⟩
  simpa [NR_cons_of_rem hA, NR_cons_of_rem hCn] using hR

/-- One-premise left (or structural) rules keeping the right-hand side. -/
theorem good_left1 {Γ Δ L0 L1 : Multiset (Formula PS TS n)} {Γ' C0 C1 : Finset (Formula PS TS n)}
    (hr : ∀ Γ Γ' Δ, Rule [.same ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; Δ⟫] ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (hc : IntShape ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫) (hp : IntShape ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (ih : IntGood ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; Δ⟫) : IntGood ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩ (by simpa using ih.1 h1),
    fun h1 TL TC TR hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp.1
  have hcA := allIn_mk.1 hc.1
  simp only [Multiset.mem_add, Finset.mem_union, or_imp, forall_and] at hpA hcA
  refine within_rule (hr (Γ + E) (Γ' ∪ E') {Z}) (by simp [add_assoc, Finset.union_assoc]) hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine ih.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) csub (by simpa using hR)
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Finset.mem_union, or_imp, forall_and]; exact ⟨hpA.2.1.1, hpA.2.1.2, hE'⟩

/-- Two-premise additive left rules keeping the right-hand side. -/
theorem good_left2 {Γ Δ L0 L1 L2 : Multiset (Formula PS TS n)} {Γ' C0 C1 C2 : Finset (Formula PS TS n)}
    (hr : ∀ Γ Γ' Δ, Rule [.same ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; Δ⟫, .same ⟪L2 + Γ ; C2 ∪ Γ' ⊢ ∅ ; Δ⟫]
      ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (hc : IntShape ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫) (hp1 : IntShape ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (hp2 : IntShape ⟪L2 + Γ ; C2 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (ih1 : IntGood ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; Δ⟫) (ih2 : IntGood ⟪L2 + Γ ; C2 ∪ Γ' ⊢ ∅ ; Δ⟫) :
    IntGood ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ⟨ih1.1 h1, ih2.1 h1⟩), fun h1 TL TC TR hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp1.1
  have hpA2 := allIn_mk.1 hp2.1
  simp only [Multiset.mem_add, Finset.mem_union, or_imp, forall_and] at hpA hpA2
  refine within_rule (hr (Γ + E) (Γ' ∪ E') {Z}) (by simp [add_assoc, Finset.union_assoc]) hT ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨ih1.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) csub (by simpa using hR),
    ih2.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) csub (by simpa using hR)⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Finset.mem_union, or_imp, forall_and]; exact ⟨hpA.2.1.1, hpA.2.1.2, hE'⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA2.1.1, hpA2.1.2, hE⟩
  · simp only [Finset.mem_union, or_imp, forall_and]; exact ⟨hpA2.2.1.1, hpA2.2.1.2, hE'⟩

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
theorem NR_sh (Δ : Multiset (Formula PS TS n)) : NR (sh Δ) = sh (NR Δ) := by
  simp [Multiset.filter_map]

/-- One-premise left rules with an eigenvariable (context weakened into the scope `n + 1`). -/
theorem good_left_sh {Γ Δ L0 : Multiset (Formula PS TS n)} {Γ' C0 : Finset (Formula PS TS n)}
    {L1 : Multiset (Formula PS TS (n + 1))} {C1 : Finset (Formula PS TS (n + 1))}
    (hr : ∀ Γ Γ' Δ, Rule [.up ⟪L1 + sh Γ ; C1 ∪ shc Γ' ⊢ ∅ ; sh Δ⟫] ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (hc : IntShape ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫)
    (hp : IntShape ⟪L1 + sh Γ ; C1 ∪ shc Γ' ⊢ ∅ ; sh Δ⟫)
    (ih : IntGood ⟪L1 + sh Γ ; C1 ∪ shc Γ' ⊢ ∅ ; sh Δ⟫) : IntGood ⟪L0 + Γ ; C0 ∪ Γ' ⊢ ∅ ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ih.1 (by simpa using h1)), fun h1 TL TC TR hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp.1
  simp only [Multiset.mem_add, Finset.mem_union, or_imp, forall_and] at hpA
  refine within_rule (hr (Γ + E) (Γ' ∪ E') {Z}) (by simp [add_assoc, Finset.union_assoc]) hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine ih.2 (by simpa using h1) _ _ _ (intSeq_mk ?_ ?_ ?_) (by simp) csub ?_
  · simp only [Multiset.map_add, Multiset.mem_add, or_imp, forall_and]
    exact ⟨hpA.1.1, hpA.1.2, forall_mem_sh' hE⟩
  · simp only [Finset.image_union, Finset.mem_union, or_imp, forall_and]
    exact ⟨hpA.2.1.1, hpA.2.1.2, forall_mem_shc subClosed_intuitionistic hE'⟩
  · exact subClosed_intuitionistic.shift _ hZ
  · rw [NR_sh]; simpa using Multiset.map_le_map (f := Formula.shift) hR

section

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

theorem NR_le_single_of_nrem {C Z : Formula PS TS n} {Δ : Multiset (Formula PS TS n)} (hC : C.nrem = true)
    (h : NR (C ::ₘ Δ) ≤ {Z}) : Z = C ∧ NR Δ = 0 := by
  rw [NR_cons_of_nrem hC] at h
  have h1 := Multiset.card_le_card h
  simp only [Multiset.card_cons, Multiset.card_singleton] at h1
  have h0 : NR Δ = 0 := Multiset.card_eq_zero.1 (by omega)
  rw [h0] at h
  exact ⟨(Multiset.mem_singleton.1 (Multiset.mem_of_le h (Multiset.mem_cons_self _ _))).symm, h0⟩

theorem NR_cons_le (A : Formula PS TS n) (Δ : Multiset (Formula PS TS n)) : NR (A ::ₘ Δ) ≤ A ::ₘ NR Δ := by
  cases h : A.nrem
  · rw [NR_cons_of_rem h]; exact Multiset.le_cons_self _ _
  · rw [NR_cons_of_nrem h]

end

/-- One-premise right rules whose principal formula is not removable. -/
theorem good_right_nrem {Γ Δ L1 : Multiset (Formula PS TS n)} {Γ' C1 : Finset (Formula PS TS n)}
    {A C : Formula PS TS n}
    (hr : ∀ Γ Γ' Δ, Rule [.same ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ ∅ ; C ::ₘ Δ⟫)
    (hCn : C.nrem = true)
    (hc : IntShape ⟪Γ ; Γ' ⊢ ∅ ; C ::ₘ Δ⟫) (hp : IntShape ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; A ::ₘ Δ⟫)
    (ih : IntGood ⟪L1 + Γ ; C1 ∪ Γ' ⊢ ∅ ; A ::ₘ Δ⟫) : IntGood ⟪Γ ; Γ' ⊢ ∅ ; C ::ₘ Δ⟫ := by
  refine ⟨fun h1 => within_rule (hr Γ Γ' Δ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ih.1 (by simpa using h1)), fun h1 TL TC TR hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  obtain ⟨rfl, h0⟩ := NR_le_single_of_nrem hCn hR
  have hpA := allIn_mk.1 hp.1
  simp only [Multiset.mem_add, Finset.mem_union, Multiset.mem_cons, or_imp, forall_and,
    forall_eq] at hpA
  refine within_rule (hr (Γ + E) (Γ' ∪ E') 0) (by simp) hT ?_
  simp only [List.mem_singleton, forall_eq]
  refine ih.2 (by simpa using h1) _ _ _ (intSeq_mk ?_ ?_ hpA.2.2.2.1) (by simp) csub ?_
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Finset.mem_union, or_imp, forall_and]; exact ⟨hpA.2.1.1, hpA.2.1.2, hE'⟩
  · simpa [h0] using NR_cons_le A Δ

end LU
