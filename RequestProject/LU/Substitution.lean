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

Formulas are well-scoped.  The formula `A` substituted for an atom of arity `k` is a
`Formula (m + k)`: its variables `0, …, m-1` are its *parameters* and its variables
`m, …, m+k-1` are the distinguished variables `x₁, …, xₖ`.  When `B : Formula n` is traversed,
a substitution `ρ : Subst m n` records how the parameters of `A` are read in the current
scope; it is weakened when a binder of `B` is crossed, so that the parameters are never
captured ("usual precautions").  An atom `a t₁ … tₖ` is replaced by
`A.subst (Fin.append ρ t)`, i.e. `A[ρ, t₁, …, tₖ]`.  At top level `m = n` and `ρ` is the
identity: `B[λx⃗.A / a]` is `Formula.substPred a A B` for `A : Formula (n + a.arity)` and
`B : Formula n`.

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

variable {n : ℕ}

theorem Term.shift_subst_lift {k m : ℕ} (σ : Subst k m) (t : Term k) :
    t.shift.subst (Subst.lift σ) = (t.subst σ).shift := by
  rw [Subst.lift, Term.shift_subst_cons, Term.shift_subst]

namespace Formula

/-! ## Substitution of a formula for a predicate symbol -/

/-- `substPredAt a A ρ B`: replace every atom `a t₁ … tₖ` of `B : Formula n` by
`A[ρ, t₁, …, tₖ]`, where `ρ : Subst m n` gives the values of the parameters of
`A : Formula (m + k)` in the current scope. -/
def substPredAt (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) :
    {n : ℕ} → Subst m n → Formula n → Formula n
  | _, ρ, atom p ts =>
    if h : p = a then A.subst (Fin.append ρ (fun i => ts (Fin.cast (by rw [h]) i)))
    else atom p ts
  | _, _, one => one
  | _, _, zero => zero
  | _, _, bot => bot
  | _, _, top => top
  | _, ρ, neg B => neg (substPredAt a A ρ B)
  | _, ρ, bang B => bang (substPredAt a A ρ B)
  | _, ρ, quest B => quest (substPredAt a A ρ B)
  | _, ρ, tensor B C => tensor (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, par B C => par (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, lolli B C => lolli (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, with_ B C => with_ (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, plus B C => plus (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, conj B C => conj (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, disj B C => disj (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, imp B C => imp (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, iimp B C => iimp (substPredAt a A ρ B) (substPredAt a A ρ C)
  | _, ρ, lall B => lall (substPredAt a A (fun i => (ρ i).shift) B)
  | _, ρ, lex B => lex (substPredAt a A (fun i => (ρ i).shift) B)
  | _, ρ, call B => call (substPredAt a A (fun i => (ρ i).shift) B)
  | _, ρ, cex B => cex (substPredAt a A (fun i => (ρ i).shift) B)

/-- `B[λx₁…xₖ.A / a]`: replace every atom `a t₁ … tₖ` of `B` by `A[t₁, …, tₖ]`; the first `n`
variables of `A : Formula (n + a.arity)` are its parameters, read in the scope of `B`. -/
def substPred (a : Pred) (A : Formula (n + a.arity)) (B : Formula n) : Formula n :=
  substPredAt a A Term.var B

/-- If `A` has the polarity of `a`, substitution preserves polarities. -/
theorem pol_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)} (hA : A.pol = a.pol)
    (ρ : Subst m n) (B : Formula n) : (substPredAt a A ρ B).pol = B.pol := by
  induction B with
  | atom p ts =>
    by_cases h : p = a
    · subst h; simp [substPredAt, hA, pol]
    · simp [substPredAt, h]
  | _ => simp_all [substPredAt, pol]

theorem pol_substPred {a : Pred} {A : Formula (n + a.arity)} (hA : A.pol = a.pol)
    (B : Formula n) : (substPred a A B).pol = B.pol := pol_substPredAt hA _ B

/-- Substitution for an atom commutes with substitution of terms (no capture of
parameters). -/
theorem subst_substPredAt (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) (B : Formula n) :
    ∀ {k : ℕ} (ρ : Subst m n) (σ : Subst n k),
      (substPredAt a A ρ B).subst σ = substPredAt a A (fun i => (ρ i).subst σ) (B.subst σ) := by
  induction B with
  | atom p ts =>
    intro k ρ σ
    by_cases h : p = a
    · subst h
      simp only [substPredAt, subst, dite_true, subst_subst]
      congr 1
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · simp [substPredAt, subst, h]
  | lall B ih | lex B ih | call B ih | cex B ih =>
    intro k ρ σ
    simp only [substPredAt, subst, ih, Term.shift_subst_lift]
  | _ => intro k ρ σ; simp_all [substPredAt, subst]

/-- Substitution for an atom commutes with weakening. -/
theorem shift_substPredAt (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) (ρ : Subst m n)
    (B : Formula n) :
    (substPredAt a A ρ B).shift = substPredAt a A (fun i => (ρ i).shift) B.shift := by
  simp only [shift, subst_substPredAt]
  congr 1
  funext i
  simp only [Term.shift, Term.rename_eq_subst]
  rfl

/-- Substitution for an atom commutes with the instantiation of a bound variable. -/
theorem inst_substPredAt (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) (ρ : Subst m n)
    (B : Formula (n + 1)) (t : Term n) :
    (substPredAt a A (fun i => (ρ i).shift) B).inst t = substPredAt a A ρ (B.inst t) := by
  simp only [inst, subst_substPredAt]
  congr 1
  funext i
  simp [Subst.single]

end Formula

/-! ## Fragments are closed under substitution -/

namespace Formula

theorem isClassical_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)} {B : Formula n}
    (hA : A.IsClassical) (hB : B.IsClassical) (ρ : Subst m n) :
    (substPredAt a A ρ B).IsClassical := by
  induction B with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsClassical]
  | _ => simp_all [substPredAt, IsClassical]

theorem isIntuitionistic_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)}
    {B : Formula n} (hA : A.IsIntuitionistic) (hB : B.IsIntuitionistic) (ρ : Subst m n) :
    (substPredAt a A ρ B).IsIntuitionistic := by
  induction B with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsIntuitionistic]
  | _ => simp_all [substPredAt, IsIntuitionistic]

theorem isNeutralInt_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)}
    {B : Formula n} (hA : A.IsNeutralInt) (hB : B.IsNeutralInt) (ρ : Subst m n) :
    (substPredAt a A ρ B).IsNeutralInt := by
  induction B with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsNeutralInt]
  | _ => simp_all [substPredAt, IsNeutralInt]

theorem isLinear_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)} {B : Formula n}
    (hA : A.IsLinear) (hB : B.IsLinear) (ρ : Subst m n) : (substPredAt a A ρ B).IsLinear := by
  induction B with
  | atom p ts => by_cases h : p = a <;> simp_all [substPredAt, IsLinear]
  | _ => simp_all [substPredAt, IsLinear]

end Formula

open Formula

/-- The formulas of a fragment. -/
def Fragment.Mem {n : ℕ} : Fragment → Formula n → Prop
  | .classical => IsClassical
  | .intuitionistic => IsIntuitionistic
  | .neutralIntuitionistic => IsNeutralInt
  | .linear => IsLinear

theorem Fragment.mem_substPredAt (F : Fragment) {a : Pred} {m : ℕ} {A : Formula (m + a.arity)}
    {B : Formula n} (hA : F.Mem A) (hB : F.Mem B) (ρ : Subst m n) :
    F.Mem (Formula.substPredAt a A ρ B) := by
  cases F
  · exact isClassical_substPredAt hA hB ρ
  · exact isIntuitionistic_substPredAt hA hB ρ
  · exact isNeutralInt_substPredAt hA hB ρ
  · exact isLinear_substPredAt hA hB ρ

/-- **Substitution property** (§6): each of the four fragments is closed under substitution:
if `B` and `A` are formulas of the fragment `F`, then so is `B[λx⃗.A / a]`. -/
theorem Fragment.mem_substPred (F : Fragment) {a : Pred} {A : Formula (n + a.arity)}
    {B : Formula n} (hA : F.Mem A) (hB : F.Mem B) : F.Mem (substPred a A B) :=
  F.mem_substPredAt hA hB _

/-! ## Substitution in sequents -/

/-- Substitution `S[λx⃗.A / a]` in all formulas of a sequent, the parameters of `A` being
read through `ρ` in the scope of `S`. -/
def Sequent.substPredAt (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) (S : Sequent)
    (ρ : Subst m S.scope) : Sequent :=
  ⟪S.L.map (Formula.substPredAt a A ρ) ; S.CL.map (Formula.substPredAt a A ρ) ⊢
    S.CR.map (Formula.substPredAt a A ρ) ; S.R.map (Formula.substPredAt a A ρ)⟫

/-- `S[λx⃗.A / a]`: substitution in all formulas of a sequent; the first `S.scope` variables of
`A` are its parameters, read in the scope of `S`. -/
def Sequent.substPred (S : Sequent) (a : Pred) (A : Formula (S.scope + a.arity)) : Sequent :=
  S.substPredAt a A Term.var

theorem mu_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)} (hA : A.pol = a.pol)
    (S : Sequent) (ρ : Subst m S.scope) : mu (S.substPredAt a A ρ) = mu S := by
  simp [mu, Sequent.substPredAt, Multiset.filter_map, Formula.pol_substPredAt hA]

theorem allIn_substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)}
    {P : ∀ {n : ℕ}, Formula n → Prop}
    (hP : ∀ {n : ℕ} (ρ : Subst m n) (B : Formula n), P B → P (Formula.substPredAt a A ρ B))
    {S : Sequent} (ρ : Subst m S.scope) (hS : AllIn P S) : AllIn P (S.substPredAt a A ρ) := by
  intro B hB
  simp only [Sequent.formulas, Sequent.substPredAt, Multiset.mem_add, Multiset.mem_map] at hB
  rcases hB with ((⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩) | ⟨C, hC, rfl⟩) | ⟨C, hC, rfl⟩ <;>
    exact hP ρ C (hS C (by simp [Sequent.formulas, hC]))

theorem Fragment.seq_substPredAt (F : Fragment) {a : Pred} {m : ℕ} {A : Formula (m + a.arity)}
    (hAF : F.Mem A) (hA : A.pol = a.pol) {S : Sequent} (ρ : Subst m S.scope) (hS : F.Seq S) :
    F.Seq (S.substPredAt a A ρ) := by
  cases F with
  | classical =>
    exact ⟨allIn_substPredAt (P := IsClassical)
      (fun ρ B hB => isClassical_substPredAt hAF hB ρ) ρ hS.1,
      (mu_substPredAt hA S ρ).symm ▸ hS.2⟩
  | intuitionistic =>
    refine ⟨allIn_substPredAt (P := IsIntuitionistic)
      (fun ρ B hB => isIntuitionistic_substPredAt hAF hB ρ) ρ hS.1, ?_, ?_⟩
    · simp [Sequent.substPredAt, hS.2.1]
    · simp [Sequent.substPredAt, hS.2.2]
  | neutralIntuitionistic =>
    refine ⟨allIn_substPredAt (P := IsNeutralInt)
      (fun ρ B hB => isNeutralInt_substPredAt hAF hB ρ) ρ hS.1, ?_, ?_, ?_⟩
    · simp [Sequent.substPredAt, hS.2.1]
    · simp [Sequent.substPredAt, hS.2.2.1]
    · simp [Sequent.substPredAt, hS.2.2.2]
  | linear =>
    exact allIn_substPredAt (P := IsLinear) (fun ρ B hB => isLinear_substPredAt hAF hB ρ) ρ hS

/-- If `A` is a formula of the fragment `F` with the polarity of `a`, then substitution maps
sequents of `F` (e.g. classical sequents) to sequents of `F`. -/
theorem Fragment.seq_substPred (F : Fragment) {a : Pred} {S : Sequent}
    {A : Formula (S.scope + a.arity)} (hAF : F.Mem A) (hA : A.pol = a.pol) (hS : F.Seq S) :
    F.Seq (S.substPred a A) :=
  F.seq_substPredAt hAF hA _ hS

/-! ## Substitution preserves provability -/

theorem map_sh_substPredAt (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) (ρ : Subst m n)
    (Γ : Multiset (Formula n)) :
    (sh Γ).map (Formula.substPredAt a A (fun i => (ρ i).shift)) =
      sh (Γ.map (Formula.substPredAt a A ρ)) := by
  simp only [sh, Multiset.map_map, Function.comp_def, Formula.shift_substPredAt]

/-- The premise-matching relation: `p'` is `p` with the substitution applied at some depth. -/
abbrev SubstPrem (a : Pred) {m : ℕ} (A : Formula (m + a.arity)) (p' p : Sequent) : Prop :=
  ∃ ρ : Subst m p.scope, p' = p.substPredAt a A ρ

local macro "prem_tac " d:term : tactic => `(tactic| (
  repeat' apply List.Forall₂.cons
  all_goals first
    | exact List.Forall₂.nil
    | (refine ⟨$d, ?_⟩
       simp only [Sequent.substPredAt, Multiset.map_cons, Multiset.map_add,
          Multiset.map_singleton, Multiset.map_zero, Multiset.insert_eq_cons,
          Formula.substPredAt, map_sh_substPredAt, Formula.inst_substPredAt]
       done)
    | (refine ⟨fun i => ($d i).shift, ?_⟩
       simp only [Sequent.substPredAt, Multiset.map_cons, Multiset.map_add,
          Multiset.map_singleton, Multiset.map_zero, Multiset.insert_eq_cons,
          Formula.substPredAt, map_sh_substPredAt, Formula.inst_substPredAt]
       done)))

set_option maxHeartbeats 4000000 in
/-- Each cut-free rule instance is mapped by substitution to a rule instance. -/
theorem Rule.substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)} (hA : A.pol = a.pol)
    {ps : List Sequent} {c : Sequent} (hr : Rule ps c) (ρ : Subst m c.scope) :
    ∃ ps', Rule ps' (c.substPredAt a A ρ) ∧ List.Forall₂ (SubstPrem a A) ps' ps := by
  cases hr <;>
    try simp only [Sequent.substPredAt, Multiset.map_cons, Multiset.map_add,
      Multiset.map_singleton, Multiset.map_zero, Multiset.insert_eq_cons, Formula.substPredAt]
  case ax =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.ax
    · prem_tac ρ
  case weakR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.weakR
    · prem_tac ρ
  case weakL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.weakL
    · prem_tac ρ
  case contrR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.contrR
    · prem_tac ρ
  case contrL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.contrL
    · prem_tac ρ
  case inR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.inR
    · prem_tac ρ
  case inL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.inL
    · prem_tac ρ
  case outR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.outR
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case outL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.outL
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case oneR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.oneR
    · prem_tac ρ
  case botL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.botL
    · prem_tac ρ
  case tensorR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.tensorR
    · prem_tac ρ
  case tensorL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.tensorL
    · prem_tac ρ
  case parR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.parR
    · prem_tac ρ
  case parL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.parL
    · prem_tac ρ
  case lolliR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lolliR
    · prem_tac ρ
  case lolliL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lolliL
    · prem_tac ρ
  case topR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.topR
    · prem_tac ρ
  case zeroL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.zeroL
    · prem_tac ρ
  case withR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.withR
    · prem_tac ρ
  case withL₁ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.withL₁
    · prem_tac ρ
  case withL₂ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.withL₂
    · prem_tac ρ
  case plusR₁ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.plusR₁
    · prem_tac ρ
  case plusR₂ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.plusR₂
    · prem_tac ρ
  case plusL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.plusL
    · prem_tac ρ
  case negL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.negL
    · prem_tac ρ
  case negR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.negR
    · prem_tac ρ
  case bangR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.bangR
    · prem_tac ρ
  case bangL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.bangL
    · prem_tac ρ
  case questR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.questR
    · prem_tac ρ
  case questL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.questL
    · prem_tac ρ
  case lallR =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lallR
    · prem_tac ρ
  case lallL _ _ _ _ _ t =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lallL (t := t)
    · prem_tac ρ
  case lexR _ _ _ _ _ t =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lexR (t := t)
    · prem_tac ρ
  case lexL =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.lexL
    · prem_tac ρ
  case conjR_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjL_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjR_AQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_AQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjL_AQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_AQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjR_PB =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_PB
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjL_PB =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_PB
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjR_AB =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjR_AB
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjL_AB₁ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_AB₁
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case conjL_AB₂ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.conjL_AB₂
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case iimpR_P =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpR_P
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case iimpL_P =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpL_P
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case iimpR_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpR_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case iimpL_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.iimpL_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case callR_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callR_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case callL_A _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callL_A (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case callR_N =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callR_N
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case callL_N _ _ _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.callL_N (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₁_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₂_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₁_SQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_SQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₂_SQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_SQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_SQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_SQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR_MQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR_MQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_MQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_MQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₁_PT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_PT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₂_PT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_PT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_PT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_PT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₁_ST =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_ST
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₂_ST =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_ST
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_ST =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_ST
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₁_MT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_MT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₂_MT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_MT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_MT =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_MT
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₁_SN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₁_SN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR₂_SN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR₂_SN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_SN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_SN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjR_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjR_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case disjL_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.disjL_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case cexR_P _ _ _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexR_P (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case cexL_P =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexL_P
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case cexR_A _ _ _ t _ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexR_A (t := t)
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case cexL_A =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.cexL_A
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impR₁_NP =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR₁_NP
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impR₂_NP =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR₂_NP
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impL_NP =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_NP
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impR_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impL_PQ =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_PQ
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impR_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impL_MN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_MN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impR_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impR_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ
  case impL_PN =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply Rule.impL_PN
      all_goals (simp only [Formula.pol_substPredAt hA]; assumption)
    · prem_tac ρ

/-- Each cut instance is mapped by substitution to a cut instance. -/
theorem CutRule.substPredAt {a : Pred} {m : ℕ} {A : Formula (m + a.arity)} {ps : List Sequent}
    {c : Sequent} (hr : CutRule ps c) (ρ : Subst m c.scope) :
    ∃ ps', CutRule ps' (c.substPredAt a A ρ) ∧ List.Forall₂ (SubstPrem a A) ps' ps := by
  cases hr <;>
    simp only [Sequent.substPredAt, Multiset.map_add]
  case cut _ _ _ _ _ _ C =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply CutRule.cut (A := Formula.substPredAt a A ρ C)
    · prem_tac ρ
  case cutR _ _ _ _ C =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply CutRule.cutR (A := Formula.substPredAt a A ρ C)
    · prem_tac ρ
  case cutL _ _ _ _ C =>
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply CutRule.cutL (A := Formula.substPredAt a A ρ C)
    · prem_tac ρ

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
    {a : Pred} {m : ℕ} {A : Formula (m + a.arity)}
    (hR : ∀ ps c (ρ : Subst m c.scope), R ps c → ∃ ps', R ps' (c.substPredAt a A ρ) ∧
      List.Forall₂ (SubstPrem a A) ps' ps)
    (hP : ∀ S (ρ : Subst m S.scope), P S → P (S.substPredAt a A ρ)) {S : Sequent}
    (h : Derivable R P S) (ρ : Subst m S.scope) :
    Derivable R P (S.substPredAt a A ρ) := by
  induction h with
  | mk ps c hr hc _ ih =>
    obtain ⟨ps', hr', hf⟩ := hR ps c ρ hr
    refine .mk ps' _ hr' (hP c ρ hc) fun p' hp' => ?_
    obtain ⟨p, hp, e, rfl⟩ := forall₂_exists_of_mem_left hf hp'
    exact ih p hp e

/-- **Substitution preserves cut-free provability**: if `S` has a cut-free proof in LU and
`A` has the polarity of `a`, then `S[λx⃗.A / a]` has a cut-free proof. -/
theorem CutFreeProvable.substPred {a : Pred} {S : Sequent} {A : Formula (S.scope + a.arity)}
    (hA : A.pol = a.pol) (h : CutFreeProvable S) : CutFreeProvable (S.substPred a A) :=
  Derivable.substPredAt (fun _ _ ρ hr => hr.substPredAt hA ρ) (fun _ _ _ => trivial) h _

/-- **Substitution preserves provability** in LU (with cut). -/
theorem Provable.substPred {a : Pred} {S : Sequent} {A : Formula (S.scope + a.arity)}
    (hA : A.pol = a.pol) (h : Provable S) : Provable (S.substPred a A) :=
  Derivable.substPredAt
    (fun _ _ ρ hr => hr.elim
      (fun hr => (hr.substPredAt hA ρ).imp fun _ h => ⟨Or.inl h.1, h.2⟩)
      (fun hr => (hr.substPredAt ρ).imp fun _ h => ⟨Or.inr h.1, h.2⟩))
    (fun _ _ _ => trivial) h _

/-- **Substitution preserves provability within a fragment**: if `S` is provable within the
fragment `F` and `A` is a formula of `F` with the polarity of `a`, then `S[λx⃗.A / a]` is
provable within `F`. -/
theorem ProvableWithin.substPred {F : Fragment} {a : Pred} {S : Sequent}
    {A : Formula (S.scope + a.arity)} (hAF : F.Mem A) (hA : A.pol = a.pol)
    (h : ProvableWithin F S) : ProvableWithin F (S.substPred a A) :=
  Derivable.substPredAt (fun _ _ ρ hr => hr.substPredAt hA ρ)
    (fun _ ρ hS => F.seq_substPredAt hAF hA ρ hS) h _

end LU
