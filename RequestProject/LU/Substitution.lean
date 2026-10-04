module

public import RequestProject.LU.Subformula

/-!
# The substitution property (§6)

> An important property of these fragments is the *substitution property*: let `a` be a
> proper predicate symbol of arity `n`, and let `A` be a formula of the same polarity as `a`,
> in which distinct free variables `x₁, …, xₙ` have been distinguished.  Then one can define
> for any formula `B` the substitution `B[λx₁…xₙ.A / a]` as the result of replacing any atom
> `a t₁ … tₙ` of `B` by `A[t₁, …, tₙ]` (with usual precautions concerning free and bound
> variables).  All the fragments considered are closed under mutual substitution.

## Representation

Variables are de Bruijn indices.  In `A`, the distinguished variables `x₁, …, xₙ` are the
indices `0, …, n-1`; the other free variables of `A` (its parameters) are the indices
`n, n+1, …`.  When an atom `a t₁ … tₙ` occurs in `B` under `d` binders, it is replaced by
`A` in which `xᵢ` becomes `tᵢ` and the parameter `n + j` becomes `j + d`: the parameters
are lifted over the `d` binders, so that they are never captured ("usual precautions").
The substitution `B[λx⃗.A / a]` is `Formula.substPred a A B` (`= substPredAt a A 0 B`).

## Results

* `Formula.pol_substPred`: if `A` has the polarity of `a`, then `B[λx⃗.A/a]` has the polarity
  of `B`;
* `Fragment.mem_substPred`: **the four fragments are closed under substitution** — if `B`
  and `A` belong to a fragment, so does `B[λx⃗.A/a]` (the polarity hypothesis is not even
  needed for formulas);
* `Fragment.seq_substPred`: if moreover `A` has the polarity of `a`, then substitution maps
  sequents of a fragment (classical, intuitionistic, …) to sequents of the same fragment;
* `CutFreeProvable.substPred`, `Provable.substPred`, `ProvableWithin.substPred`:
  substituting a formula of the right polarity for an atom preserves provability in LU
  (with or without cut) and provability within a fragment.
-/

@[expose] public section

namespace LU

/-! ## Simultaneous substitution for terms -/

namespace Term

/-- Simultaneous substitution of `σ i` for every variable `i`. -/
def substAll (σ : ℕ → Term) : Term → Term
  | var n => σ n
  | func f ts => func f (ts.map (substAll σ))

theorem shift_substAll (σ : ℕ → Term) (c : ℕ) :
    ∀ u : Term, (u.substAll σ).shift c = u.substAll (fun i => (σ i).shift c)
  | var n => by simp [substAll]
  | func f ts => by
    simp only [substAll, shift, List.map_map, func.injEq, true_and]
    apply List.map_congr_left
    intro u hu
    exact shift_substAll σ c u

theorem subst_substAll (σ : ℕ → Term) (k : ℕ) (s : Term) :
    ∀ u : Term, subst k s (u.substAll σ) = u.substAll (fun i => subst k s (σ i))
  | var n => by simp [substAll]
  | func f ts => by
    simp only [substAll, subst, List.map_map, func.injEq, true_and]
    apply List.map_congr_left
    intro u hu
    exact subst_substAll σ k s u

theorem shift_shift_zero (c : ℕ) :
    ∀ u : Term, (u.shift 0).shift (c + 1) = (u.shift c).shift 0
  | var n => by
    by_cases h : n < c
    · simp [shift, h]
    · simp [shift, h]
  | func f ts => by
    simp only [shift, List.map_map, func.injEq, true_and]
    apply List.map_congr_left
    intro u hu
    exact shift_shift_zero c u

theorem subst_succ_shift_zero (k : ℕ) (s : Term) :
    ∀ u : Term, subst (k + 1) (s.shift 0) (u.shift 0) = (subst k s u).shift 0
  | var n => by
    simp only [shift, Nat.not_lt_zero, if_false, subst]
    by_cases h1 : n < k
    · simp [h1, shift]
    · by_cases h2 : n = k
      · subst h2; simp
      · have : n - 1 + 1 = n := by omega
        simp [h1, h2, shift, this]
  | func f ts => by
    simp only [shift, subst, List.map_map, func.injEq, true_and]
    apply List.map_congr_left
    intro u hu
    exact subst_succ_shift_zero k s u

end Term

/-- Lifting a simultaneous substitution under a binder. -/
def liftSubst (σ : ℕ → Term) : ℕ → Term
  | 0 => .var 0
  | n + 1 => (σ n).shift 0

namespace Formula

/-- Simultaneous substitution of terms for the free variables of a formula. -/
def substAll (σ : ℕ → Term) : Formula → Formula
  | atom p ts => atom p (ts.map (Term.substAll σ))
  | one => one
  | zero => zero
  | bot => bot
  | top => top
  | neg A => neg (A.substAll σ)
  | bang A => bang (A.substAll σ)
  | quest A => quest (A.substAll σ)
  | tensor A B => tensor (A.substAll σ) (B.substAll σ)
  | par A B => par (A.substAll σ) (B.substAll σ)
  | lolli A B => lolli (A.substAll σ) (B.substAll σ)
  | with_ A B => with_ (A.substAll σ) (B.substAll σ)
  | plus A B => plus (A.substAll σ) (B.substAll σ)
  | conj A B => conj (A.substAll σ) (B.substAll σ)
  | disj A B => disj (A.substAll σ) (B.substAll σ)
  | imp A B => imp (A.substAll σ) (B.substAll σ)
  | iimp A B => iimp (A.substAll σ) (B.substAll σ)
  | lall A => lall (A.substAll (liftSubst σ))
  | lex A => lex (A.substAll (liftSubst σ))
  | call A => call (A.substAll (liftSubst σ))
  | cex A => cex (A.substAll (liftSubst σ))

@[simp] theorem pol_substAll (σ : ℕ → Term) (A : Formula) : (A.substAll σ).pol = A.pol := by
  induction A generalizing σ <;> simp_all [substAll, pol]

theorem shiftFrom_substAll (σ : ℕ → Term) (c : ℕ) (A : Formula) :
    (A.substAll σ).shiftFrom c = A.substAll (fun i => (σ i).shift c) := by
  have hlift : ∀ (σ : ℕ → Term) (c : ℕ),
      (fun i => (liftSubst σ i).shift (c + 1)) = liftSubst (fun i => (σ i).shift c) := by
    intro σ c; funext i
    cases i with
    | zero => simp [liftSubst, Term.shift]
    | succ i => simp [liftSubst, Term.shift_shift_zero]
  induction A generalizing σ c with
  | atom p ts =>
    simp only [substAll, shiftFrom, List.map_map, atom.injEq, true_and]
    apply List.map_congr_left
    intro u _
    exact Term.shift_substAll σ c u
  | lall A ih => simp only [substAll, shiftFrom, ih, hlift]
  | lex A ih => simp only [substAll, shiftFrom, ih, hlift]
  | call A ih => simp only [substAll, shiftFrom, ih, hlift]
  | cex A ih => simp only [substAll, shiftFrom, ih, hlift]
  | _ => simp_all [substAll, shiftFrom]

theorem substAt_substAll (σ : ℕ → Term) (k : ℕ) (s : Term) (A : Formula) :
    (A.substAll σ).substAt k s = A.substAll (fun i => Term.subst k s (σ i)) := by
  have hlift : ∀ (σ : ℕ → Term) (k : ℕ) (s : Term),
      (fun i => Term.subst (k + 1) (s.shift 0) (liftSubst σ i)) =
        liftSubst (fun i => Term.subst k s (σ i)) := by
    intro σ k s; funext i
    cases i with
    | zero => simp [liftSubst, Term.subst]
    | succ i => simp [liftSubst, Term.subst_succ_shift_zero]
  induction A generalizing σ k s with
  | atom p ts =>
    simp only [substAll, substAt, List.map_map, atom.injEq, true_and]
    apply List.map_congr_left
    intro u _
    exact Term.subst_substAll σ k s u
  | lall A ih => simp only [substAll, substAt, ih, hlift]
  | lex A ih => simp only [substAll, substAt, ih, hlift]
  | call A ih => simp only [substAll, substAt, ih, hlift]
  | cex A ih => simp only [substAll, substAt, ih, hlift]
  | _ => simp_all [substAll, substAt]

/-! ## Substitution of a formula for a predicate symbol -/

/-- The term substitution used to form `A[t₁, …, tₙ]` for an atom `a t₁ … tₙ` occurring under
`d` binders: `xᵢ ↦ tᵢ`, and the parameter `n + j` of `A` becomes `j + d`. -/
def argSubst (ts : List Term) (d : ℕ) (i : ℕ) : Term :=
  if h : i < ts.length then ts[i] else .var (i - ts.length + d)

/-- `substPredAt a A d B`: replace every atom `a t₁ … tₙ` of `B` (which lies under `d`
enclosing binders) by `A[t₁, …, tₙ]`. -/
def substPredAt (a : Pred) (A : Formula) : ℕ → Formula → Formula
  | d, atom p ts => if p = a then A.substAll (argSubst ts d) else atom p ts
  | _, one => one
  | _, zero => zero
  | _, bot => bot
  | _, top => top
  | d, neg B => neg (substPredAt a A d B)
  | d, bang B => bang (substPredAt a A d B)
  | d, quest B => quest (substPredAt a A d B)
  | d, tensor B C => tensor (substPredAt a A d B) (substPredAt a A d C)
  | d, par B C => par (substPredAt a A d B) (substPredAt a A d C)
  | d, lolli B C => lolli (substPredAt a A d B) (substPredAt a A d C)
  | d, with_ B C => with_ (substPredAt a A d B) (substPredAt a A d C)
  | d, plus B C => plus (substPredAt a A d B) (substPredAt a A d C)
  | d, conj B C => conj (substPredAt a A d B) (substPredAt a A d C)
  | d, disj B C => disj (substPredAt a A d B) (substPredAt a A d C)
  | d, imp B C => imp (substPredAt a A d B) (substPredAt a A d C)
  | d, iimp B C => iimp (substPredAt a A d B) (substPredAt a A d C)
  | d, lall B => lall (substPredAt a A (d + 1) B)
  | d, lex B => lex (substPredAt a A (d + 1) B)
  | d, call B => call (substPredAt a A (d + 1) B)
  | d, cex B => cex (substPredAt a A (d + 1) B)

/-- `B[λx₁…xₙ.A / a]`: replace every atom `a t₁ … tₙ` of `B` by `A[t₁, …, tₙ]`. -/
def substPred (a : Pred) (A B : Formula) : Formula := substPredAt a A 0 B

/-- If `A` has the polarity of `a`, substitution preserves polarities. -/
theorem pol_substPredAt {a : Pred} {A : Formula} (hA : A.pol = a.pol) (d : ℕ) (B : Formula) :
    (substPredAt a A d B).pol = B.pol := by
  induction B generalizing d with
  | atom p ts =>
    by_cases h : p = a
    · subst h; simp [substPredAt, hA, pol]
    · simp [substPredAt, h]
  | _ => simp_all [substPredAt, pol]

theorem pol_substPred {a : Pred} {A : Formula} (hA : A.pol = a.pol) (B : Formula) :
    (substPred a A B).pol = B.pol := pol_substPredAt hA 0 B

/-- Substitution commutes with the shift of free variables (no capture of parameters). -/
theorem shiftFrom_substPredAt (a : Pred) (A : Formula) (B : Formula) :
    ∀ (c e : ℕ), c ≤ e →
      (substPredAt a A e B).shiftFrom c = substPredAt a A (e + 1) (B.shiftFrom c) := by
  induction B with
  | atom p ts =>
    intro c e hce
    by_cases h : p = a
    · subst h
      simp only [substPredAt, shiftFrom, if_true, shiftFrom_substAll]
      congr 1
      funext i
      simp only [argSubst, List.length_map]
      split_ifs with hi
      · simp
      · simp only [Term.shift]
        rw [if_neg (by omega)]
        congr 1
    · simp [substPredAt, shiftFrom, h]
  | lall B ih => intro c e hce; simp only [substPredAt, shiftFrom, ih (c + 1) (e + 1) (by omega)]
  | lex B ih => intro c e hce; simp only [substPredAt, shiftFrom, ih (c + 1) (e + 1) (by omega)]
  | call B ih => intro c e hce; simp only [substPredAt, shiftFrom, ih (c + 1) (e + 1) (by omega)]
  | cex B ih => intro c e hce; simp only [substPredAt, shiftFrom, ih (c + 1) (e + 1) (by omega)]
  | _ => intro c e hce; simp_all [substPredAt, shiftFrom]

theorem shift_substPredAt (a : Pred) (A : Formula) (d : ℕ) (B : Formula) :
    (substPredAt a A d B).shift = substPredAt a A (d + 1) B.shift :=
  shiftFrom_substPredAt a A B 0 d (Nat.zero_le _)

/-- Substitution commutes with the instantiation of a bound variable. -/
theorem substAt_substPredAt (a : Pred) (A : Formula) (d : ℕ) (B : Formula) :
    ∀ (k : ℕ) (t : Term),
      (substPredAt a A (d + 1 + k) B).substAt k t = substPredAt a A (d + k) (B.substAt k t) := by
  induction B with
  | atom p ts =>
    intro k t
    by_cases h : p = a
    · subst h
      simp only [substPredAt, substAt, if_true, substAt_substAll]
      congr 1
      funext i
      simp only [argSubst, List.length_map]
      split_ifs with hi
      · simp
      · simp only [Term.subst]
        rw [if_neg (by omega), if_neg (by omega)]
        congr 1
        omega
    · simp [substPredAt, substAt, h]
  | lall B ih =>
    intro k t; simp only [substPredAt, substAt]; have := ih (k + 1) (t.shift 0)
    simp only [← Nat.add_assoc] at this ⊢; rw [this]
  | lex B ih =>
    intro k t; simp only [substPredAt, substAt]; have := ih (k + 1) (t.shift 0)
    simp only [← Nat.add_assoc] at this ⊢; rw [this]
  | call B ih =>
    intro k t; simp only [substPredAt, substAt]; have := ih (k + 1) (t.shift 0)
    simp only [← Nat.add_assoc] at this ⊢; rw [this]
  | cex B ih =>
    intro k t; simp only [substPredAt, substAt]; have := ih (k + 1) (t.shift 0)
    simp only [← Nat.add_assoc] at this ⊢; rw [this]
  | _ => intro k t; simp_all [substPredAt, substAt]

theorem inst_substPredAt (a : Pred) (A : Formula) (d : ℕ) (B : Formula) (t : Term) :
    (substPredAt a A (d + 1) B).inst t = substPredAt a A d (B.inst t) :=
  substAt_substPredAt a A d B 0 t

end Formula

/-! ## Fragments are closed under substitution -/

namespace Formula

@[simp] theorem isClassical_substAll (σ : ℕ → Term) (A : Formula) :
    (A.substAll σ).IsClassical ↔ A.IsClassical := by
  induction A generalizing σ <;> simp_all [substAll, IsClassical]

@[simp] theorem isIntuitionistic_substAll (σ : ℕ → Term) (A : Formula) :
    (A.substAll σ).IsIntuitionistic ↔ A.IsIntuitionistic := by
  induction A generalizing σ <;> simp_all [substAll, IsIntuitionistic]

@[simp] theorem isNeutralInt_substAll (σ : ℕ → Term) (A : Formula) :
    (A.substAll σ).IsNeutralInt ↔ A.IsNeutralInt := by
  induction A generalizing σ <;> simp_all [substAll, IsNeutralInt]

@[simp] theorem isLinear_substAll (σ : ℕ → Term) (A : Formula) :
    (A.substAll σ).IsLinear ↔ A.IsLinear := by
  induction A generalizing σ <;> simp_all [substAll, IsLinear]

theorem isClassical_substPredAt {a : Pred} {A B : Formula} (hA : A.IsClassical)
    (hB : B.IsClassical) (d : ℕ) : (substPredAt a A d B).IsClassical := by
  induction B generalizing d with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsClassical]
  | _ => simp_all [substPredAt, IsClassical]

theorem isIntuitionistic_substPredAt {a : Pred} {A B : Formula} (hA : A.IsIntuitionistic)
    (hB : B.IsIntuitionistic) (d : ℕ) : (substPredAt a A d B).IsIntuitionistic := by
  induction B generalizing d with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsIntuitionistic]
  | _ => simp_all [substPredAt, IsIntuitionistic]

theorem isNeutralInt_substPredAt {a : Pred} {A B : Formula} (hA : A.IsNeutralInt)
    (hB : B.IsNeutralInt) (d : ℕ) : (substPredAt a A d B).IsNeutralInt := by
  induction B generalizing d with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsNeutralInt]
  | _ => simp_all [substPredAt, IsNeutralInt]

theorem isLinear_substPredAt {a : Pred} {A B : Formula} (hA : A.IsLinear)
    (hB : B.IsLinear) (d : ℕ) : (substPredAt a A d B).IsLinear := by
  induction B generalizing d with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsLinear]
  | _ => simp_all [substPredAt, IsLinear]

end Formula

open Formula

/-- The formulas of a fragment. -/
def Fragment.Mem : Fragment → Formula → Prop
  | .classical => IsClassical
  | .intuitionistic => IsIntuitionistic
  | .neutralIntuitionistic => IsNeutralInt
  | .linear => IsLinear

/-- **Substitution property** (§6): each of the four fragments is closed under substitution:
if `B` and `A` are formulas of the fragment `F`, then so is `B[λx⃗.A / a]`. -/
theorem Fragment.mem_substPred (F : Fragment) {a : Pred} {A B : Formula} (hA : F.Mem A)
    (hB : F.Mem B) : F.Mem (substPred a A B) := by
  cases F
  · exact isClassical_substPredAt hA hB 0
  · exact isIntuitionistic_substPredAt hA hB 0
  · exact isNeutralInt_substPredAt hA hB 0
  · exact isLinear_substPredAt hA hB 0

/-! ## Substitution in sequents -/

/-- Substitution `S[λx⃗.A / a]` in all formulas of a sequent (at binder depth `d`). -/
def Sequent.substPredAt (a : Pred) (A : Formula) (d : ℕ) (S : Sequent) : Sequent :=
  ⟪S.L.map (Formula.substPredAt a A d) ; S.CL.map (Formula.substPredAt a A d) ⊢
    S.CR.map (Formula.substPredAt a A d) ; S.R.map (Formula.substPredAt a A d)⟫

/-- `S[λx⃗.A / a]`: substitution in all formulas of a sequent. -/
def Sequent.substPred (a : Pred) (A : Formula) (S : Sequent) : Sequent :=
  S.substPredAt a A 0

theorem mu_substPredAt {a : Pred} {A : Formula} (hA : A.pol = a.pol) (d : ℕ) (S : Sequent) :
    mu (S.substPredAt a A d) = mu S := by
  simp [mu, Sequent.substPredAt, Multiset.filter_map,
    Formula.pol_substPredAt hA]

theorem allIn_substPredAt {a : Pred} {A : Formula} {d : ℕ} {P : Formula → Prop} (hP : ∀ B, P B → P (Formula.substPredAt a A d B))
    {S : Sequent} (hS : AllIn P S) : AllIn P (S.substPredAt a A d) := by
  intro B hB
  simp only [Sequent.formulas, Sequent.substPredAt, Multiset.mem_add, Multiset.mem_map] at hB
  rcases hB with ((⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩) | ⟨C, hC, rfl⟩) | ⟨C, hC, rfl⟩ <;>
    exact hP C (hS C (by simp [Sequent.formulas, hC]))

theorem Fragment.mem_substPredAt (F : Fragment) {a : Pred} {A B : Formula} (hA : F.Mem A)
    (hB : F.Mem B) (d : ℕ) : F.Mem (Formula.substPredAt a A d B) := by
  cases F
  · exact isClassical_substPredAt hA hB d
  · exact isIntuitionistic_substPredAt hA hB d
  · exact isNeutralInt_substPredAt hA hB d
  · exact isLinear_substPredAt hA hB d

theorem Fragment.seq_substPredAt (F : Fragment) {a : Pred} {A : Formula} (hAF : F.Mem A)
    (hA : A.pol = a.pol) (d : ℕ) {S : Sequent} (hS : F.Seq S) :
    F.Seq (S.substPredAt a A d) := by
  cases F with
  | classical =>
    exact ⟨allIn_substPredAt (P := IsClassical) (fun B hB => isClassical_substPredAt hAF hB d) hS.1,
      (mu_substPredAt hA d S).symm ▸ hS.2⟩
  | intuitionistic =>
    refine ⟨allIn_substPredAt (P := IsIntuitionistic) (fun B hB => isIntuitionistic_substPredAt hAF hB d) hS.1, ?_, ?_⟩
    · simp [Sequent.substPredAt, hS.2.1]
    · simp [Sequent.substPredAt, hS.2.2]
  | neutralIntuitionistic =>
    refine ⟨allIn_substPredAt (P := IsNeutralInt) (fun B hB => isNeutralInt_substPredAt hAF hB d) hS.1, ?_, ?_, ?_⟩
    · simp [Sequent.substPredAt, hS.2.1]
    · simp [Sequent.substPredAt, hS.2.2.1]
    · simp [Sequent.substPredAt, hS.2.2.2]
  | linear => exact allIn_substPredAt (P := IsLinear) (fun B hB => isLinear_substPredAt hAF hB d) hS

/-- If `A` is a formula of the fragment `F` with the polarity of `a`, then substitution maps
sequents of `F` (e.g. classical sequents) to sequents of `F`. -/
theorem Fragment.seq_substPred (F : Fragment) {a : Pred} {A : Formula} (hAF : F.Mem A)
    (hA : A.pol = a.pol) {S : Sequent} (hS : F.Seq S) : F.Seq (S.substPred a A) :=
  F.seq_substPredAt hAF hA 0 hS

/-! ## Substitution preserves provability -/

theorem map_sh_substPredAt (a : Pred) (A : Formula) (d : ℕ) (Γ : Multiset Formula) :
    (sh Γ).map (Formula.substPredAt a A (d + 1)) = sh (Γ.map (Formula.substPredAt a A d)) := by
  simp only [sh, Multiset.map_map, Function.comp_def, Formula.shift_substPredAt]

/-- The premise-matching relation: `p'` is `p` with the substitution applied at some depth. -/
abbrev SubstPrem (a : Pred) (A : Formula) (p' p : Sequent) : Prop :=
  ∃ e, p' = p.substPredAt a A e

local macro "prem_tac " d:term : tactic => `(tactic| (
  repeat' apply List.Forall₂.cons
  all_goals first
    | exact List.Forall₂.nil
    | (refine ⟨$d, ?_⟩
       simp only [Sequent.substPredAt, Multiset.map_cons, Multiset.map_add,
          Multiset.map_singleton, Multiset.map_zero, Multiset.insert_eq_cons,
          Formula.substPredAt, map_sh_substPredAt, Formula.inst_substPredAt]
       done)
    | (refine ⟨$d + 1, ?_⟩
       simp only [Sequent.substPredAt, Multiset.map_cons, Multiset.map_add,
          Multiset.map_singleton, Multiset.map_zero, Multiset.insert_eq_cons,
          Formula.substPredAt, map_sh_substPredAt, Formula.inst_substPredAt]
       done)))

set_option maxHeartbeats 4000000 in
/-- Each cut-free rule instance is mapped by substitution to a rule instance. -/
theorem Rule.substPredAt {a : Pred} {A : Formula} (hA : A.pol = a.pol) {ps : List Sequent}
    {c : Sequent} (hr : Rule ps c) (d : ℕ) :
    ∃ ps', Rule ps' (c.substPredAt a A d) ∧ List.Forall₂ (SubstPrem a A) ps' ps := by
  cases hr <;>
    try simp only [Sequent.substPredAt, Multiset.map_cons, Multiset.map_add,
      Multiset.map_singleton, Multiset.map_zero, Multiset.insert_eq_cons, Formula.substPredAt]
  case ax =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.ax
    · prem_tac d
  case weakR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.weakR
    · prem_tac d
  case weakL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.weakL
    · prem_tac d
  case contrR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.contrR
    · prem_tac d
  case contrL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.contrL
    · prem_tac d
  case inR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.inR
    · prem_tac d
  case inL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.inL
    · prem_tac d
  case outR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.outR
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case outL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.outL
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case oneR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.oneR
    · prem_tac d
  case botL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.botL
    · prem_tac d
  case tensorR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.tensorR
    · prem_tac d
  case tensorL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.tensorL
    · prem_tac d
  case parR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.parR
    · prem_tac d
  case parL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.parL
    · prem_tac d
  case lolliR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lolliR
    · prem_tac d
  case lolliL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lolliL
    · prem_tac d
  case topR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.topR
    · prem_tac d
  case zeroL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.zeroL
    · prem_tac d
  case withR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.withR
    · prem_tac d
  case withL₁ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.withL₁
    · prem_tac d
  case withL₂ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.withL₂
    · prem_tac d
  case plusR₁ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.plusR₁
    · prem_tac d
  case plusR₂ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.plusR₂
    · prem_tac d
  case plusL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.plusL
    · prem_tac d
  case negL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.negL
    · prem_tac d
  case negR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.negR
    · prem_tac d
  case bangR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.bangR
    · prem_tac d
  case bangL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.bangL
    · prem_tac d
  case questR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.questR
    · prem_tac d
  case questL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.questL
    · prem_tac d
  case lallR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lallR
    · prem_tac d
  case lallL _ _ _ _ _ t =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lallL (t := t)
    · prem_tac d
  case lexR _ _ _ _ _ t =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lexR (t := t)
    · prem_tac d
  case lexL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lexL
    · prem_tac d
  case conjR_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjL_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjR_AQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_AQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjL_AQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_AQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjR_PB =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_PB
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjL_PB =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_PB
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjR_AB =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_AB
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjL_AB₁ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_AB₁
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case conjL_AB₂ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_AB₂
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case iimpR_P =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpR_P
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case iimpL_P =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpL_P
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case iimpR_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpR_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case iimpL_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpL_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case callR_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callR_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case callL_A _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callL_A (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case callR_N =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callR_N
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case callL_N _ _ _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callL_N (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₁_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₂_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₁_SQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_SQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₂_SQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_SQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_SQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_SQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR_MQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR_MQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_MQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_MQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₁_PT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_PT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₂_PT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_PT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_PT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_PT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₁_ST =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_ST
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₂_ST =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_ST
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_ST =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_ST
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₁_MT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_MT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₂_MT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_MT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_MT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_MT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₁_SN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_SN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR₂_SN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_SN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_SN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_SN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjR_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case disjL_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case cexR_P _ _ _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexR_P (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case cexL_P =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexL_P
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case cexR_A _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexR_A (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case cexL_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexL_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impR₁_NP =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR₁_NP
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impR₂_NP =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR₂_NP
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impL_NP =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_NP
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impR_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impL_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impR_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impL_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impR_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d
  case impL_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac d

/-- Each cut instance is mapped by substitution to a cut instance. -/
theorem CutRule.substPredAt {a : Pred} {A : Formula} {ps : List Sequent}
    {c : Sequent} (hr : CutRule ps c) (d : ℕ) :
    ∃ ps', CutRule ps' (c.substPredAt a A d) ∧ List.Forall₂ (SubstPrem a A) ps' ps := by
  cases hr <;>
    simp only [Sequent.substPredAt, Multiset.map_add]
  case cut _ _ _ _ _ _ C =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply CutRule.cut (A := Formula.substPredAt a A d C)
    · prem_tac d
  case cutR _ _ _ _ C =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply CutRule.cutR (A := Formula.substPredAt a A d C)
    · prem_tac d
  case cutL _ _ _ _ C =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply CutRule.cutL (A := Formula.substPredAt a A d C)
    · prem_tac d

theorem forall₂_exists_of_mem_left {α β : Type*} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {x : α} (hx : x ∈ l₁) : ∃ y ∈ l₂, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨y, hy, h⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem Derivable.substPredAt {R : List Sequent → Sequent → Prop} {P : Sequent → Prop}
    {a : Pred} {A : Formula}
    (hR : ∀ ps c d, R ps c → ∃ ps', R ps' (c.substPredAt a A d) ∧
      List.Forall₂ (SubstPrem a A) ps' ps)
    (hP : ∀ S d, P S → P (S.substPredAt a A d)) {S : Sequent} (h : Derivable R P S) (d : ℕ) :
    Derivable R P (S.substPredAt a A d) := by
  induction h generalizing d with
  | mk ps c hr hc _ ih =>
    obtain ⟨ps', hr', hf⟩ := hR ps c d hr
    refine .mk ps' _ hr' (hP c d hc) fun p' hp' => ?_
    obtain ⟨p, hp, e, rfl⟩ := forall₂_exists_of_mem_left hf hp'
    exact ih p hp e

/-- **Substitution preserves cut-free provability**: if `S` has a cut-free proof in LU and
`A` has the polarity of `a`, then `S[λx⃗.A / a]` has a cut-free proof. -/
theorem CutFreeProvable.substPred {a : Pred} {A : Formula} (hA : A.pol = a.pol) {S : Sequent}
    (h : CutFreeProvable S) : CutFreeProvable (S.substPred a A) :=
  Derivable.substPredAt (fun _ _ d hr => hr.substPredAt hA d) (fun _ _ _ => trivial) h 0

/-- **Substitution preserves provability** in LU (with cut). -/
theorem Provable.substPred {a : Pred} {A : Formula} (hA : A.pol = a.pol) {S : Sequent}
    (h : Provable S) : Provable (S.substPred a A) :=
  Derivable.substPredAt
    (fun _ _ d hr => hr.elim
      (fun hr => (hr.substPredAt hA d).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
      (fun hr => (hr.substPredAt d).imp fun _ h => ⟨Or.inr h.1, h.2⟩))
    (fun _ _ _ => trivial) h 0

/-- **Substitution preserves provability within a fragment**: if `S` is provable within the
fragment `F` and `A` is a formula of `F` with the polarity of `a`, then `S[λx⃗.A / a]` is
provable within `F`. -/
theorem ProvableWithin.substPred {F : Fragment} {a : Pred} {A : Formula} (hAF : F.Mem A)
    (hA : A.pol = a.pol) {S : Sequent} (h : ProvableWithin F S) :
    ProvableWithin F (S.substPred a A) :=
  Derivable.substPredAt (fun _ _ d hr => hr.substPredAt hA d)
    (fun _ d hS => F.seq_substPredAt hAF hA d hS) h 0

end LU
