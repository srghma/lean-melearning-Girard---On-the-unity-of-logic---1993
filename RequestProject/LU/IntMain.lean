module

public import RequestProject.LU.Intuitionistic

/-!
# The intuitionistic fragment: rule-by-rule analysis and the theorem of §6

Each rule of LU applicable to intuitionistic formulas is checked to preserve the invariant
`IntGood`.  The only rule which can produce a premise with `ν ≠ 1` from a conclusion with
`ν = 1` is the "bad" rule

    Γ;Γ' ⊢ ;C,P      B,Λ;Γ' ⊢ ;
    ---------------------------
       P⊃B,Γ,Λ;Γ' ⊢ ;C

which is replaced by the "good" one `Γ;Γ' ⊢ ;P   B,Λ;Γ' ⊢ ;C  /  P⊃B,Γ,Λ;Γ' ⊢ ;C`
(here this is obtained directly from the invariant of the left premise).
-/

@[expose] public section

namespace LU

variable {n : ℕ}

open Formula

theorem good_zeroL (Γ Δ : Multiset (Formula n)) (hc : IntShape ⟪zero ::ₘ Γ ; 0 ⊢ 0 ; Δ⟫) :
    IntGood ⟪zero ::ₘ Γ ; 0 ⊢ 0 ; Δ⟫ := by
  refine ⟨fun h1 => within_rule (Rule.zeroL Γ Δ) rfl ⟨hc.1, hc.2, h1⟩ (by simp),
    fun _ (TL TC TR : Multiset (Formula n)) hT hL _ _ => ?_⟩
  obtain ⟨X, hX⟩ := Multiset.exists_cons_of_mem
    (Multiset.mem_of_le hL (Multiset.mem_cons_self _ _))
  have hs : IntSeq ⟪TL ; 0 ⊢ 0 ; TR⟫ := by
    obtain ⟨hA, _, h1⟩ := hT
    exact ⟨allIn_mk.2 ⟨(allIn_mk.1 hA).1, by simp, by simp, (allIn_mk.1 hA).2.2.2⟩, rfl, h1⟩
  have hw := within_rule (Rule.zeroL X TR) (by rw [hX]) hs (by simp)
  exact within_weakCL' hw hT (Multiset.zero_le _)

theorem good_weakL {Γ Γ' Δ : Multiset (Formula n)} {A : Formula n}
    (hc : IntShape ⟪Γ ; A ::ₘ Γ' ⊢ 0 ; Δ⟫) (ih : IntGood ⟪Γ ; Γ' ⊢ 0 ; Δ⟫) :
    IntGood ⟪Γ ; A ::ₘ Γ' ⊢ 0 ; Δ⟫ :=
  ⟨fun h1 => within_rule (Rule.weakL Γ Γ' 0 Δ A) rfl ⟨hc.1, hc.2, h1⟩ (by simpa using ih.1 h1),
    fun h1 _ _ _ hT hL hC hR => ih.absorb h1 hT hL ((Multiset.le_cons_self _ _).trans hC) hR⟩

theorem NR_add (Δ Θ : Multiset (Formula n)) : NR (Δ + Θ) = NR Δ + NR Θ :=
  Multiset.filter_add _ _ _

theorem card_cons_ne_one {A : Formula n} {Δ : Multiset (Formula n)} :
    Multiset.card (A ::ₘ Δ) ≠ 1 ↔ Δ ≠ 0 := by
  simp [Multiset.card_eq_zero]

theorem good_conjR_PQ {Γ Λ Γ' Δ Θ : Multiset (Formula n)} {P Q : Formula n} (hP : P.pol = .pos)
    (hQ : Q.pol = .pos) (hc : IntShape ⟪Γ + Λ ; Γ' ⊢ 0 ; conj P Q ::ₘ (Δ + Θ)⟫)
    (ih1 : IntGood ⟪Γ ; Γ' ⊢ 0 ; P ::ₘ Δ⟫) (ih2 : IntGood ⟪Λ ; Γ' ⊢ 0 ; Q ::ₘ Θ⟫) :
    IntGood ⟪Γ + Λ ; Γ' ⊢ 0 ; conj P Q ::ₘ (Δ + Θ)⟫ := by
  have hPQ : (conj P Q).nrem = false := nrem_of_pos (by simp [pol, hP, hQ, Pol.conj])
  constructor
  · intro h1
    have h0 : Δ + Θ = 0 := by simpa [Multiset.card_eq_zero] using h1
    obtain ⟨rfl, rfl⟩ := add_eq_zero.1 h0
    exact within_rule (Rule.conjR_PQ Γ Λ Γ' 0 0 0 P Q hP hQ) rfl ⟨hc.1, hc.2, h1⟩
      (by simpa using ⟨ih1.1 (by simp), ih2.1 (by simp)⟩)
  · intro h1
    refine fun (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_
    rw [NR_cons_of_rem hPQ, NR_add] at hR
    by_cases hΔ : Δ = 0
    · subst hΔ
      refine ih2.absorb ?_ hT ((Multiset.le_add_left _ _).trans hL) hC ?_
      · rw [card_cons_ne_one]; simpa using card_cons_ne_one.1 h1
      · rw [NR_cons_of_rem (nrem_of_pos hQ)]; simpa using hR
    · refine ih1.absorb (card_cons_ne_one.2 hΔ) hT ((Multiset.le_add_right _ _).trans hL) hC ?_
      rw [NR_cons_of_rem (nrem_of_pos hP)]; exact (Multiset.le_add_right _ _).trans hR

theorem good_conjR_AQ {Λ Γ' Θ : Multiset (Formula n)} {A Q : Formula n} (hA : A.pol ≠ .pos)
    (hQ : Q.pol = .pos) (hc : IntShape ⟪Λ ; Γ' ⊢ 0 ; conj A Q ::ₘ Θ⟫)
    (ih1 : IntGood ⟪0 ; Γ' ⊢ 0 ; {A}⟫) (ih2 : IntGood ⟪Λ ; Γ' ⊢ 0 ; Q ::ₘ Θ⟫) :
    IntGood ⟪Λ ; Γ' ⊢ 0 ; conj A Q ::ₘ Θ⟫ := by
  have hAQ : (conj A Q).nrem = false := nrem_of_pos (by
    simp only [pol, hQ]; cases A.pol <;> rfl)
  refine ⟨fun h1 => within_rule (Rule.conjR_AQ Λ Γ' 0 Θ A Q hA hQ) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ⟨ih1.1 (by simp), ih2.1 (by simpa using h1)⟩),
    fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ih2.absorb (by simpa using h1) hT hL hC ?_⟩
  rw [NR_cons_of_rem (nrem_of_pos hQ)]; rwa [NR_cons_of_rem hAQ] at hR

theorem good_conjR_PB {Γ Γ' Δ : Multiset (Formula n)} {P B : Formula n} (hP : P.pol = .pos)
    (hB : B.pol ≠ .pos) (hc : IntShape ⟪Γ ; Γ' ⊢ 0 ; conj P B ::ₘ Δ⟫)
    (ih1 : IntGood ⟪Γ ; Γ' ⊢ 0 ; P ::ₘ Δ⟫) (ih2 : IntGood ⟪0 ; Γ' ⊢ 0 ; {B}⟫) :
    IntGood ⟪Γ ; Γ' ⊢ 0 ; conj P B ::ₘ Δ⟫ := by
  have hPB : (conj P B).nrem = false := nrem_of_pos (by
    simp only [pol, hP]; cases B.pol <;> rfl)
  refine ⟨fun h1 => within_rule (Rule.conjR_PB Γ Γ' 0 Δ P B hP hB) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ⟨ih1.1 (by simpa using h1), ih2.1 (by simp)⟩),
    fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ih1.absorb (by simpa using h1) hT hL hC ?_⟩
  rw [NR_cons_of_rem (nrem_of_pos hP)]; rwa [NR_cons_of_rem hPB] at hR

theorem good_conjR_AB {Γ Γ' Δ : Multiset (Formula n)} {A B : Formula n} (hA : A.pol ≠ .pos)
    (hB : B.pol ≠ .pos) (hn : (conj A B).nrem = true)
    (hc : IntShape ⟪Γ ; Γ' ⊢ 0 ; conj A B ::ₘ Δ⟫)
    (hp1 : IntShape ⟪Γ ; Γ' ⊢ 0 ; A ::ₘ Δ⟫) (hp2 : IntShape ⟪Γ ; Γ' ⊢ 0 ; B ::ₘ Δ⟫)
    (ih1 : IntGood ⟪Γ ; Γ' ⊢ 0 ; A ::ₘ Δ⟫) (ih2 : IntGood ⟪Γ ; Γ' ⊢ 0 ; B ::ₘ Δ⟫) :
    IntGood ⟪Γ ; Γ' ⊢ 0 ; conj A B ::ₘ Δ⟫ := by
  refine ⟨fun h1 => within_rule (Rule.conjR_AB Γ Γ' 0 Δ A B hA hB) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ⟨ih1.1 (by simpa using h1), ih2.1 (by simpa using h1)⟩),
    fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  obtain ⟨rfl, h0⟩ := NR_le_single_of_nrem hn hR
  have hpA := allIn_mk.1 hp1.1
  have hpB := allIn_mk.1 hp2.1
  simp only [Multiset.mem_cons, or_imp, forall_and, forall_eq] at hpA hpB
  refine within_rule (Rule.conjR_AB (Γ + E) (Γ' + E') 0 0 A B hA hB) (by simp) hT ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  have hL' : ∀ X ∈ Γ + E, X.IsIntuitionistic := by
    simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.1, hE⟩
  have hC' : ∀ X ∈ Γ' + E', X.IsIntuitionistic := by
    simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.2.1, hE'⟩
  refine ⟨?_, ?_⟩
  · simpa using ih1.2 (by simpa using h1) _ _ _ (intSeq_mk hL' hC' hpA.2.2.2.1) (by simp)
      (by simp) (by simpa [h0] using NR_cons_le A Δ)
  · simpa using ih2.2 (by simpa using h1) _ _ _ (intSeq_mk hL' hC' hpB.2.2.2.1) (by simp)
      (by simp) (by simpa [h0] using NR_cons_le B Δ)

theorem good_iimpL_P {Γ Λ Γ' Δ Θ : Multiset (Formula n)} {P B : Formula n} (hP : P.pol = .pos)
    (hc : IntShape ⟪iimp P B ::ₘ (Γ + Λ) ; Γ' ⊢ 0 ; Δ + Θ⟫)
    (hp2 : IntShape ⟪B ::ₘ Λ ; Γ' ⊢ 0 ; Θ⟫)
    (ih1 : IntGood ⟪Γ ; Γ' ⊢ 0 ; P ::ₘ Δ⟫) (ih2 : IntGood ⟪B ::ₘ Λ ; Γ' ⊢ 0 ; Θ⟫) :
    IntGood ⟪iimp P B ::ₘ (Γ + Λ) ; Γ' ⊢ 0 ; Δ + Θ⟫ := by
  have hle : Γ ≤ iimp P B ::ₘ (Γ + Λ) :=
    (Multiset.le_add_right _ _).trans (Multiset.le_cons_self _ _)
  constructor
  · intro h1
    by_cases hΔ : Δ = 0
    · subst hΔ
      exact within_rule (Rule.iimpL_P Γ Λ Γ' 0 0 Θ P B hP) rfl ⟨hc.1, hc.2, h1⟩
        (by simpa using ⟨ih1.1 (by simp), ih2.1 (by simpa using h1)⟩)
    · refine ih1.absorb (card_cons_ne_one.2 hΔ) ⟨hc.1, hc.2, h1⟩ hle le_rfl ?_
      rw [NR_cons_of_rem (nrem_of_pos hP)]
      exact (Multiset.filter_le _ _).trans (Multiset.le_add_right _ _)
  · intro h1
    refine fun (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_
    by_cases hΔ : Δ = 0
    · subst hΔ
      obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
      have hpA := allIn_mk.1 hp2.1
      simp only [Multiset.mem_cons, or_imp, forall_and, forall_eq] at hpA
      refine within_rule (Rule.iimpL_P Γ (Λ + E) (Γ' + E') 0 0 {Z} P B hP) (by simp [add_assoc])
        hT ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨by simpa using within_weakCL E' (ih1.1 (by simp)) hE', ?_⟩
      refine ih2.2 (by simpa using h1) _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) (by simp)
        (by simpa using hR)
      · simp only [Multiset.mem_cons, Multiset.mem_add, or_imp, forall_and, forall_eq]
        exact ⟨hpA.1.1, hpA.1.2, hE⟩
      · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.2.1, hE'⟩
    · refine ih1.absorb (card_cons_ne_one.2 hΔ) hT (hle.trans hL) hC ?_
      rw [NR_cons_of_rem (nrem_of_pos hP)]
      refine le_trans ?_ hR
      simp

theorem good_iimpL_A {Λ Γ' Θ : Multiset (Formula n)} {A B : Formula n} (hA : A.pol ≠ .pos)
    (hc : IntShape ⟪iimp A B ::ₘ Λ ; Γ' ⊢ 0 ; Θ⟫)
    (hp2 : IntShape ⟪B ::ₘ Λ ; Γ' ⊢ 0 ; Θ⟫)
    (ih1 : IntGood ⟪0 ; Γ' ⊢ 0 ; {A}⟫) (ih2 : IntGood ⟪B ::ₘ Λ ; Γ' ⊢ 0 ; Θ⟫) :
    IntGood ⟪iimp A B ::ₘ Λ ; Γ' ⊢ 0 ; Θ⟫ := by
  refine ⟨fun h1 => within_rule (Rule.iimpL_A Λ Γ' 0 Θ A B hA) rfl ⟨hc.1, hc.2, h1⟩
    (by simpa using ⟨ih1.1 (by simp), ih2.1 h1⟩), fun h1 (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_⟩
  obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
  have hpA := allIn_mk.1 hp2.1
  simp only [Multiset.mem_cons, or_imp, forall_and, forall_eq] at hpA
  refine within_rule (Rule.iimpL_A (Λ + E) (Γ' + E') 0 {Z} A B hA) (by simp) hT ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨by simpa using within_weakCL E' (ih1.1 (by simp)) hE', ?_⟩
  refine ih2.2 h1 _ _ _ (intSeq_mk ?_ ?_ hZ) (by simp) (by simp) hR
  · simp only [Multiset.mem_cons, Multiset.mem_add, or_imp, forall_and, forall_eq]
    exact ⟨hpA.1.1, hpA.1.2, hE⟩
  · simp only [Multiset.mem_add, or_imp, forall_and]; exact ⟨hpA.2.1, hE'⟩

theorem good_lallR {Γ Γ' Δ : Multiset (Formula n)} {A : Formula (n + 1)} (hn : (lall A).nrem = true)
    (hc : IntShape ⟪Γ ; Γ' ⊢ 0 ; lall A ::ₘ Δ⟫)
    (hp : IntShape ⟪sh Γ ; sh Γ' ⊢ 0 ; A ::ₘ sh Δ⟫)
    (ih : IntGood ⟪sh Γ ; sh Γ' ⊢ 0 ; A ::ₘ sh Δ⟫) :
    IntGood ⟪Γ ; Γ' ⊢ 0 ; lall A ::ₘ Δ⟫ := by
  constructor
  · intro h1
    have h0 : Δ = 0 := by simpa [Multiset.card_eq_zero] using h1
    subst h0
    exact within_rule (Rule.lallR Γ Γ' 0 0 A) rfl ⟨hc.1, hc.2, h1⟩
      (by simpa using ih.1 (by simp))
  · intro h1
    refine fun (TL TC TR : Multiset (Formula n)) hT hL hC hR => ?_
    obtain ⟨E, E', Z, rfl, rfl, rfl, hE, hE', hZ⟩ := tgt_decomp (n := n) hT hL hC
    obtain ⟨rfl, h0⟩ := NR_le_single_of_nrem hn hR
    have hpA := allIn_mk.1 hp.1
    simp only [Multiset.mem_cons, or_imp, forall_and, forall_eq] at hpA
    refine within_rule (Rule.lallR (Γ + E) (Γ' + E') 0 0 A) (by simp) hT ?_
    simp only [List.mem_singleton, forall_eq]
    have := ih.2 (by simpa using card_cons_ne_one.1 h1)
      (sh (Γ + E)) (sh (Γ' + E')) {A} (intSeq_mk ?_ ?_ hpA.2.2.2.1) (by simp) (by simp)
      (by simpa [NR_sh, h0] using NR_cons_le A (sh Δ))
    · simpa using this
    · simp only [Multiset.map_add, Multiset.mem_add, or_imp, forall_and]
      exact ⟨hpA.1, forall_mem_sh' hE⟩
    · simp only [Multiset.map_add, Multiset.mem_add, or_imp, forall_and]
      exact ⟨hpA.2.1, forall_mem_sh' hE'⟩

theorem nrem_iimp {A B : Formula n} (h : B.pol ≠ .neg) : (iimp A B).nrem = true := by
  simp only [nrem, isAtom, Bool.not_false, Bool.and_true, decide_eq_true_eq, pol]
  revert h; generalize A.pol = a; generalize B.pol = b; cases a <;> cases b <;> simp [Pol.iimp]

theorem nrem_lall {A : Formula (n + 1)} (h : A.pol ≠ .neg) : (lall A).nrem = true := by
  simp only [nrem, isAtom, Bool.not_false, Bool.and_true, decide_eq_true_eq, pol]
  revert h; generalize A.pol = a; cases a <;> simp [Pol.lall]

theorem nrem_conj {A B : Formula n} (hA : A.pol = .neu) (hB : B.pol = .neu) :
    (conj A B).nrem = true := by
  simp [nrem, pol, isAtom, hA, hB, Pol.conj]

theorem pol_eq_neu {A : Formula n} (h1 : A.pol ≠ .pos) (h2 : A.pol ≠ .neg) : A.pol = .neu := by
  revert h1 h2; cases A.pol <;> simp

/-- The principal formula on the right of an intuitionistic-shaped sequent is intuitionistic. -/
theorem IntShape.right_head {Γ Γ' Δ' Δ : Multiset (Formula n)} {C : Formula n}
    (h : IntShape ⟪Γ ; Γ' ⊢ Δ' ; C ::ₘ Δ⟫) : C.IsIntuitionistic :=
  (allIn_mk.1 h.1).2.2.2 _ (Multiset.mem_cons_self _ _)

set_option maxHeartbeats 4000000 in
/-- Rule-by-rule analysis for the intuitionistic fragment. -/
theorem Rule.intGood {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (hc : IntShape c)
    (hpre : ∀ p ∈ ps, IntShape p) (ih : ∀ p ∈ ps, IntGood p) : IntGood c := by
  have hr' := hr
  have hneg : ∀ {n : ℕ} (A : Formula n), A.IsIntuitionistic → A.pol ≠ .neg := fun A h => h.pol_ne_neg
  cases hr
  case ax A => exact good_card1 hr' hc (by simp) (by simp) ih
  case oneR => exact good_card1 hr' hc (by simp) (by simp) ih
  case zeroL Γ Δ => exact good_zeroL Γ Δ hc
  case weakL Γ Γ' Δ' Δ A =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih
    exact good_weakL hc ih
  case contrL Γ Γ' Δ' Δ A =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := 0) (C0 := {A}) (L1 := 0) (C1 := {A, A}) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.contrL Γ Γ' 0 Δ A)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case inL Γ Γ' Δ' Δ A =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := 0) (C0 := {A}) (L1 := {A}) (C1 := 0) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.inL Γ Γ' 0 Δ A)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case outL Γ Γ' Δ' Δ P hP =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {P}) (C0 := 0) (L1 := 0) (C1 := {P}) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.outL Γ Γ' 0 Δ P hP)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {conj P Q}) (C0 := 0) (L1 := {P, Q}) (C1 := 0) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.conjL_PQ Γ Γ' 0 Δ P Q hP hQ)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjL_AQ Γ Γ' Δ' Δ A Q hA hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {conj A Q}) (C0 := 0) (L1 := {Q}) (C1 := {A}) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.conjL_AQ Γ Γ' 0 Δ A Q hA hQ)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjL_PB Γ Γ' Δ' Δ P B hP hB =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {conj P B}) (C0 := 0) (L1 := {P}) (C1 := {B}) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.conjL_PB Γ Γ' 0 Δ P B hP hB)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjL_AB₁ Γ Γ' Δ' Δ A B hA hB =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {conj A B}) (C0 := 0) (L1 := {A}) (C1 := 0) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.conjL_AB₁ Γ Γ' 0 Δ A B hA hB)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjL_AB₂ Γ Γ' Δ' Δ A B hA hB =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {conj A B}) (C0 := 0) (L1 := {B}) (C1 := 0) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.conjL_AB₂ Γ Γ' 0 Δ A B hA hB)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case lallL Γ Γ' Δ' Δ A t =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left1 (L0 := {lall A}) (C0 := 0) (L1 := {A.inst t}) (C1 := 0) (Γ := Γ)
      (Γ' := Γ') (Δ := Δ) (fun Γ Γ' Δ => by simpa using Rule.lallL Γ Γ' 0 Δ A t)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case disjL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    simpa using good_left2 (L0 := {disj P Q}) (C0 := 0) (L1 := {P}) (C1 := 0) (L2 := {Q})
      (C2 := 0) (Γ := Γ) (Γ' := Γ') (Δ := Δ)
      (fun Γ Γ' Δ => by simpa using Rule.disjL_PQ Γ Γ' 0 Δ P Q hP hQ)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case disjL_SQ Γ Γ' Δ' Δ S Q hS hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    simpa using good_left2 (L0 := {disj S Q}) (C0 := 0) (L1 := 0) (C1 := {S}) (L2 := {Q})
      (C2 := 0) (Γ := Γ) (Γ' := Γ') (Δ := Δ)
      (fun Γ Γ' Δ => by simpa using Rule.disjL_SQ Γ Γ' 0 Δ S Q hS hQ)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case disjL_PT Γ Γ' Δ' Δ P T hP hT =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    simpa using good_left2 (L0 := {disj P T}) (C0 := 0) (L1 := {P}) (C1 := 0) (L2 := 0)
      (C2 := {T}) (Γ := Γ) (Γ' := Γ') (Δ := Δ)
      (fun Γ Γ' Δ => by simpa using Rule.disjL_PT Γ Γ' 0 Δ P T hP hT)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case disjL_ST Γ Γ' Δ' Δ S T hS hT =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    simpa using good_left2 (L0 := {disj S T}) (C0 := 0) (L1 := 0) (C1 := {S}) (L2 := 0)
      (C2 := {T}) (Γ := Γ) (Γ' := Γ') (Δ := Δ)
      (fun Γ Γ' Δ => by simpa using Rule.disjL_ST Γ Γ' 0 Δ S T hS hT)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case cexL_P Λ Λ' Θ' Θ P hP =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left_sh (L0 := {cex P}) (C0 := 0) (L1 := {P}) (C1 := 0) (Γ := Λ)
      (Γ' := Λ') (Δ := Θ) (fun Γ Γ' Δ => by simpa using Rule.cexL_P Γ Γ' 0 Δ P hP)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case cexL_A Λ Λ' Θ' Θ A hA =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using good_left_sh (L0 := {cex A}) (C0 := 0) (L1 := 0) (C1 := {A}) (Γ := Λ)
      (Γ' := Λ') (Δ := Θ) (fun Γ Γ' Δ => by simpa using Rule.cexL_A Γ Γ' 0 Δ A hA)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case iimpR_P Γ Γ' Δ' Δ P B hP =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    have hn := nrem_iimp (A := P) (hneg B hc.right_head.2)
    simpa using good_right_nrem (L1 := {P}) (C1 := 0) (Γ := Γ) (Γ' := Γ') (Δ := Δ)
      (fun Γ Γ' Δ => by simpa using Rule.iimpR_P Γ Γ' 0 Δ P B hP) hn
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case iimpR_A Γ Γ' Δ' Δ A B hA =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    have hn := nrem_iimp (A := A) (hneg B hc.right_head.2)
    simpa using good_right_nrem (L1 := 0) (C1 := {A}) (Γ := Γ) (Γ' := Γ') (Δ := Δ)
      (fun Γ Γ' Δ => by simpa using Rule.iimpR_A Γ Γ' 0 Δ A B hA) hn
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case lallR Γ Γ' Δ' Δ A =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih hpre
    have hn := nrem_lall (hneg A hc.right_head)
    exact good_lallR hn hc (by simpa using hpre) (by simpa using ih)
  case conjR_PQ Γ Λ Γ' Δ' Δ Θ P Q hP hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih
    exact good_conjR_PQ hP hQ hc ih.1 ih.2
  case conjR_AQ Λ Γ' Δ' Θ A Q hA hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih
    exact good_conjR_AQ hA hQ hc ih.1 ih.2
  case conjR_PB Γ Γ' Δ' Δ P B hP hB =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih
    exact good_conjR_PB hP hB hc ih.1 ih.2
  case conjR_AB Γ Γ' Δ' Δ A B hA hB =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    have hn := nrem_conj (pol_eq_neu hA (hneg A hc.right_head.1))
      (pol_eq_neu hB (hneg B hc.right_head.2))
    exact good_conjR_AB hA hB hn hc hpre.1 hpre.2 ih.1 ih.2
  case iimpL_P Γ Λ Γ' Δ' Δ Θ P B hP =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    exact good_iimpL_P hP hc hpre.2 ih.1 ih.2
  case iimpL_A Λ Γ' Δ' Θ A B hA =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      implies_true, and_true, IsEmpty.forall_iff] at ih hpre
    exact good_iimpL_A hA hc hpre.2 ih.1 ih.2
  case disjR₁_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih
    exact good_right_rem hr' hc (nrem_of_pos hP) (nrem_of_pos (by simp [pol, hP, hQ, Pol.disj])) ih
  case disjR₂_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih
    exact good_right_rem hr' hc (nrem_of_pos hQ) (nrem_of_pos (by simp [pol, hP, hQ, Pol.disj])) ih
  case disjR₂_SQ Γ Γ' Δ' Δ S Q hS hQ =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih
    exact good_right_rem hr' hc (nrem_of_pos hQ) (nrem_of_pos (by simp [pol, hS, hQ, Pol.disj])) ih
  case disjR₁_PT Γ Γ' Δ' Δ P T hP hT =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih
    exact good_right_rem hr' hc (nrem_of_pos hP) (nrem_of_pos (by simp [pol, hP, hT, Pol.disj])) ih
  case cexR_P Γ Γ' Δ' Δ P t hP =>
    have h0 := hc.cr_eq; subst h0
    simp only [List.mem_singleton, forall_eq] at ih
    exact good_right_rem hr' hc (nrem_of_pos (by simp [hP])) (nrem_of_pos (by simp [pol])) ih
  case disjR₁_SQ => exact good_card1 hr' hc (by simp) (by simp) ih
  case disjR₁_ST => exact good_card1 hr' hc (by simp) (by simp) ih
  case disjR₂_ST => exact good_card1 hr' hc (by simp) (by simp) ih
  case disjR₂_PT => exact good_card1 hr' hc (by simp) (by simp) ih
  case cexR_A => exact good_card1 hr' hc (by simp) (by simp) ih
  all_goals
    exfalso
    simp only [IntShape, allIn_mk, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton, or_imp,
      forall_and, IsIntuitionistic] at hc hpre
    simp_all

set_option maxHeartbeats 4000000 in
/-- In a cut-free rule whose conclusion has an empty right central zone and whose formulas
are intuitionistic, the premises also have an empty right central zone. -/
theorem Rule.int_CR {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (hc : IntShape c)
    (hp : ∀ p ∈ ps, AllIn IsIntuitionistic p) : ∀ p ∈ ps, p.CR = 0 := by
  have hneg : ∀ {n : ℕ} (A : Formula n), A.IsIntuitionistic → A.pol ≠ .neg := fun A h => h.pol_ne_neg
  cases hr <;>
    simp only [IntShape, allIn_mk, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton, or_imp,
      forall_and, IsIntuitionistic] at hc hp ⊢ <;>
    simp_all

/-- Main lemma: every cut-free provable intuitionistic-shaped sequent satisfies the
invariant `IntGood`. -/
theorem int_main {S : Sequent} (h : CutFreeProvable S) (hS : IntShape S) : IntGood S := by
  unfold CutFreeProvable at h
  induction h with
  | mk ps c hr _ _ ih =>
    have hA : ∀ p ∈ ps, AllIn IsIntuitionistic p :=
      hr.allIn_premises subClosed_intuitionistic hS.1
    have hpre : ∀ p ∈ ps, IntShape p := fun p hp => ⟨hA p hp, hr.int_CR hS hA p hp⟩
    exact hr.intGood hS hpre fun p hp => ih p hp (hpre p hp)

/-- **Theorem (§6), intuitionistic fragment, cut-free version.**  A cut-free provable
intuitionistic sequent `Γ;Γ' ⊢ ;A` is provable within the intuitionistic fragment. -/
theorem intuitionistic_within {S : Sequent} (h : CutFreeProvable S) (hS : IntSeq S) :
    ProvableWithin .intuitionistic S :=
  (int_main h ⟨hS.1, hS.2.1⟩).1 hS.2.2

end LU
