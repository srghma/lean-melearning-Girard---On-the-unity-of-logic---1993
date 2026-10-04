module

public import RequestProject.LU.Classical

/-!
# The classical fragment: rule-by-rule analysis and the theorem of §6
-/

@[expose] public section

namespace LU

open Formula

attribute [local simp] Formula.pol Pol.conj Pol.disj Pol.imp Pol.dual mu_mk Multiset.le_cons_self

/-- Closes the arithmetic and multiset side conditions of the rule analysis. -/
macro "cl_simp" : tactic => `(tactic| first | (simp [*]; done) | (simp [*]; omega))

set_option maxHeartbeats 4000000 in
/-- Rule-by-rule analysis for the classical fragment. -/
theorem Rule.clGood {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (hc : ClShape c)
    (hpre : ∀ p ∈ ps, ClShape p) (ih : ∀ p ∈ ps, ClGood p) : ClGood c := by
  have hr' := hr
  have hneu : ∀ A : Formula, A.IsClassical → A.pol ≠ .neu := fun A h => h.pol_ne_neu
  cases hr
  case ax A => exact cl_absorb hr' hc ih (by simp) (fun h => by
      simp only [mu_mk, muL_singleton, muR_singleton] at h; split_ifs at h <;> simp_all)
  case weakR Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case weakL Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case contrR Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := {A}) (R0 := 0)
      (L1 := 0) (C1 := 0) (D1 := {A, A}) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.contrR x1 x2 x3 x4 A)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case contrL Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := {A}) (D0 := 0) (R0 := 0)
      (L1 := 0) (C1 := {A, A}) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.contrL x1 x2 x3 x4 A)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case inR Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    by_cases hA : A.pol = .pos
    · exact cl_inR_pos hA hc ih
    · simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := {A}) (R0 := 0)
        (L1 := 0) (C1 := 0) (D1 := 0) (R1 := {A}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
        (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.inR x1 x2 x3 x4 A)
        (by cl_simp) (by cl_simp)
        (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case inL Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    by_cases hA : A.pol = .neg
    · exact cl_inL_neg hA hc ih
    · simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := {A}) (D0 := 0) (R0 := 0)
        (L1 := {A}) (C1 := 0) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
        (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.inL x1 x2 x3 x4 A)
        (by cl_simp) (by cl_simp)
        (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case outR Γ Γ' Δ' Δ N hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {N})
      (L1 := 0) (C1 := 0) (D1 := {N}) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.outR x1 x2 x3 x4 N hN)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case outL Γ Γ' Δ' Δ P hP =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := {P}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := 0) (C1 := {P}) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.outL x1 x2 x3 x4 P hP)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case oneR => exact cl_absorb hr' hc ih (by simp) (fun h => by simp [mu_mk, pol] at h)
  case zeroL Γ Δ => exact cl_zeroL Γ Δ hc
  case negL Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    have hAc : A.IsClassical := hc.lhead
    by_cases hA : A.pol = .pos
    · exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
    · have hA' := hAc.neg_of_ne_pos hA
      simpa using cl_reapply1 ctxMap_id (L0 := {neg A}) (C0 := 0) (D0 := 0) (R0 := 0)
        (L1 := 0) (C1 := 0) (D1 := 0) (R1 := {A}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
        (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.negL x1 x2 x3 x4 A)
        (by cl_simp) (by cl_simp)
        (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case negR Γ Γ' Δ' Δ A =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    have hAc : A.IsClassical := hc.rhead
    by_cases hA : A.pol = .pos
    · simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {neg A})
        (L1 := {A}) (C1 := 0) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
        (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.negR x1 x2 x3 x4 A)
        (by cl_simp) (by cl_simp)
        (by simpa using hc) (by simpa using hpre) (by simpa using ih)
    · have hA' := hAc.neg_of_ne_pos hA
      exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case conjR_PQ Γ Λ Γ' Δ' Δ Θ P Q hP hQ =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_mult hr' hc ih.1 ih.2 (by cl_simp) (by cl_simp) (by cl_simp)
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case conjL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := {conj P Q}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := {P, Q}) (C1 := 0) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.conjL_PQ x1 x2 x3 x4 P Q hP hQ)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjR_AQ Λ Γ' Δ' Θ A Q hA hQ =>
    have hA' := (show A.IsClassical from hc.rhead.1).neg_of_ne_pos hA
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_side hr' (by simp) (by simp) hc ih.2 ih.1
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case conjL_AQ Γ Γ' Δ' Δ A Q hA hQ =>
    have hA' := (show A.IsClassical from hc.lhead.1).neg_of_ne_pos hA
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := {conj A Q}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := {Q}) (C1 := {A}) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.conjL_AQ x1 x2 x3 x4 A Q hA hQ)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjR_PB Γ Γ' Δ' Δ P B hP hB =>
    have hB' := (show B.IsClassical from hc.rhead.2).neg_of_ne_pos hB
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_side hr' (by simp) (by simp) hc ih.1 ih.2
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case conjL_PB Γ Γ' Δ' Δ P B hP hB =>
    have hB' := (show B.IsClassical from hc.lhead.2).neg_of_ne_pos hB
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := {conj P B}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := {P}) (C1 := {B}) (D1 := 0) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.conjL_PB x1 x2 x3 x4 P B hP hB)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case conjR_AB Γ Γ' Δ' Δ A B hA hB =>
    have hA' := (show A.IsClassical from hc.rhead.1).neg_of_ne_pos hA
    have hB' := (show B.IsClassical from hc.rhead.2).neg_of_ne_pos hB
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    simpa using cl_reapply2 (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {conj A B})
      (L1 := 0) (C1 := 0) (D1 := 0) (R1 := {A})
      (L2 := 0) (C2 := 0) (D2 := 0) (R2 := {B}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.conjR_AB x1 x2 x3 x4 A B hA hB)
      (by cl_simp) (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case conjL_AB₁ Γ Γ' Δ' Δ A B hA hB =>
    have hA' := (show A.IsClassical from hc.lhead.1).neg_of_ne_pos hA
    have hB' := (show B.IsClassical from hc.lhead.2).neg_of_ne_pos hB
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case conjL_AB₂ Γ Γ' Δ' Δ A B hA hB =>
    have hA' := (show A.IsClassical from hc.lhead.1).neg_of_ne_pos hA
    have hB' := (show B.IsClassical from hc.lhead.2).neg_of_ne_pos hB
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case callR_A Γ Γ' Δ' Δ A hA =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_sh (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {call A})
      (L1 := 0) (C1 := 0) (D1 := {A}) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.callR_A x1 x2 x3 x4 A hA)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case callR_N Γ Γ' Δ' Δ N hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_sh (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {call N})
      (L1 := 0) (C1 := 0) (D1 := 0) (R1 := {N}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.callR_N x1 x2 x3 x4 N hN)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case callL_A Γ' Δ' A t hA => exact cl_absorb hr' hc ih (fun _ q hq => by
      simp only [List.mem_singleton] at hq; subst hq; simp [mu_mk, hA]) (fun h => by simp [mu_mk, pol] at h)
  case callL_N Γ Γ' Δ' Δ N t hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case disjR₁_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case disjR₂_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case disjL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    simpa using cl_reapply2 (L0 := {disj P Q}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := {P}) (C1 := 0) (D1 := 0) (R1 := 0)
      (L2 := {Q}) (C2 := 0) (D2 := 0) (R2 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.disjL_PQ x1 x2 x3 x4 P Q hP hQ)
      (by cl_simp) (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case disjR_MQ Γ Γ' Δ' Δ M Q hM hQ =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {disj M Q})
      (L1 := 0) (C1 := 0) (D1 := {Q}) (R1 := {M}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.disjR_MQ x1 x2 x3 x4 M Q hM hQ)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case disjL_MQ Γ Γ' Δ' Δ M Q hM hQ =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_side hr' (by simp) (by simp) hc ih.1 ih.2
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case disjR_PN Γ Γ' Δ' Δ P N hP hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {disj P N})
      (L1 := 0) (C1 := 0) (D1 := {P}) (R1 := {N}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.disjR_PN x1 x2 x3 x4 P N hP hN)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case disjL_PN Λ Γ' Δ' Θ P N hP hN =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_side hr' (by simp) (by simp) hc ih.2 ih.1
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case disjR_MN Γ Γ' Δ' Δ M N hM hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {disj M N})
      (L1 := 0) (C1 := 0) (D1 := 0) (R1 := {M, N}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.disjR_MN x1 x2 x3 x4 M N hM hN)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case disjL_MN Γ Λ Γ' Δ' Δ Θ M N hM hN =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_mult hr' hc ih.1 ih.2 (by cl_simp) (by cl_simp) (by cl_simp)
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case cexR_P Γ Γ' Δ' Δ P t hP =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case cexL_P Λ Λ' Θ' Θ P hP =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_sh (L0 := {cex P}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := {P}) (C1 := 0) (D1 := 0) (R1 := 0) (Γ := Λ) (Γ' := Λ') (Δ' := Θ')
      (Δ := Θ) (fun x1 x2 x3 x4 => by simpa using Rule.cexL_P x1 x2 x3 x4 P hP)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case cexR_A Γ' Δ' A t hA =>
    have hA' := (show (A.inst t).IsClassical from (allIn_mk.1 (hpre _ (List.mem_singleton_self _))).2.2.2 _ (Multiset.mem_singleton_self _)).neg_of_ne_pos (by simpa using hA)
    exact cl_absorb hr' hc ih (fun _ q hq => by
      simp only [List.mem_singleton] at hq; subst hq; simp [mu_mk, hA']) (fun h => by simp [mu_mk, pol] at h)
  case cexL_A Λ Λ' Θ' Θ A hA =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_sh (L0 := {cex A}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := 0) (C1 := {A}) (D1 := 0) (R1 := 0) (Γ := Λ) (Γ' := Λ') (Δ' := Θ')
      (Δ := Θ) (fun x1 x2 x3 x4 => by simpa using Rule.cexL_A x1 x2 x3 x4 A hA)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case impR₁_NP Γ Γ' Δ' Δ N P hN hP =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case impR₂_NP Γ Γ' Δ' Δ N P hN hP =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    exact cl_absorb1 hr' hc ih (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case impL_NP Γ Γ' Δ' Δ N P hN hP =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    simpa using cl_reapply2 (L0 := {imp N P}) (C0 := 0) (D0 := 0) (R0 := 0)
      (L1 := 0) (C1 := 0) (D1 := 0) (R1 := {N})
      (L2 := {P}) (C2 := 0) (D2 := 0) (R2 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.impL_NP x1 x2 x3 x4 N P hN hP)
      (by cl_simp) (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre.1) (by simpa using hpre.2)
      (by simpa using ih.1) (by simpa using ih.2)
  case impR_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {imp P Q})
      (L1 := {P}) (C1 := 0) (D1 := {Q}) (R1 := 0) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.impR_PQ x1 x2 x3 x4 P Q hP hQ)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case impL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_side hr' (by simp) (by simp) hc ih.1 ih.2
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case impR_MN Γ Γ' Δ' Δ M N hM hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {imp M N})
      (L1 := 0) (C1 := {M}) (D1 := 0) (R1 := {N}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.impR_MN x1 x2 x3 x4 M N hM hN)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case impL_MN Λ Γ' Δ' Θ M N hM hN =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_side hr' (by simp) (by simp) hc ih.2 ih.1
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)
  case impR_PN Γ Γ' Δ' Δ P N hP hN =>
    simp only [List.mem_singleton, forall_eq] at ih hpre
    simpa using cl_reapply1 ctxMap_id (L0 := 0) (C0 := 0) (D0 := 0) (R0 := {imp P N})
      (L1 := {P}) (C1 := 0) (D1 := 0) (R1 := {N}) (Γ := Γ) (Γ' := Γ') (Δ' := Δ')
      (Δ := Δ) (fun x1 x2 x3 x4 => by simpa using Rule.impR_PN x1 x2 x3 x4 P N hP hN)
      (by cl_simp) (by cl_simp)
      (by simpa using hc) (by simpa using hpre) (by simpa using ih)
  case impL_PN Γ Λ Γ' Δ' Δ Θ P N hP hN =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, implies_true, and_true,
      IsEmpty.forall_iff] at ih hpre
    exact cl_absorb_mult hr' hc ih.1 ih.2 (by cl_simp) (by cl_simp) (by cl_simp)
      (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp) (by cl_simp)

  all_goals
    exfalso
    simp only [allIn_mk, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton, or_imp,
      forall_and, IsClassical] at hc hpre
    simp_all

/-- Main lemma: every cut-free provable sequent made of classical formulas satisfies the
invariant `ClGood`. -/
theorem cl_main {S : Sequent} (h : CutFreeProvable S) (hS : ClShape S) : ClGood S := by
  unfold CutFreeProvable at h
  induction h with
  | mk ps c hr _ _ ih =>
    have hpre : ∀ p ∈ ps, ClShape p := hr.allIn_premises subClosed_classical hS
    exact hr.clGood hS hpre fun p hp => ih p hp (hpre p hp)

/-- **Theorem (§6), classical fragment, cut-free version.**  A cut-free provable classical
sequent is provable within the classical fragment. -/
theorem classical_within {S : Sequent} (h : CutFreeProvable S) (hS : ClassicalSeq S) :
    ProvableWithin .classical S :=
  (cl_main h hS.1).1 hS.2

end LU
