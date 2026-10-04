module

public import RequestProject.LU.LinearLogic
public import RequestProject.LU.Subformula

/-!
# §4: from LU (with neutral atoms) back to linear logic

> Conversely, this new calculus (as long as we restrict ourselves to neutral atomic
> propositions) can be translated into the usual linear logic as follows: a sequent
> `Γ; Γ'₊, Γ'' ⊢ Δ''_?, Δ'₋; Δ` translates as `Γ, Γ'₊, !Γ'' ⊢ ?Δ''_?, Δ'₋, Δ` in the old
> syntax for linear logic.  Then we have to mimick all rules of the new calculus in the
> old one, which offers no difficulty.  Of course, we have to prove in the old calculus a
> stronger form of the rule for '!', namely that one can pass from `Γ ⊢ Δ, A` to
> `Γ ⊢ Δ, !A`, as soon as `Γ` is positive and `Δ` negative.  But since our atoms are
> neutral, positive formulas are built from `0`, `1`, and formulas `!A` by means of `⊕`, `⊗`
> and `∃x` (and symmetrically for negative formulas), and we can make an easy inductive
> argument.

We use the simpler (and equivalent, by the lemma below) translation in which *every*
formula of the central zone receives an exponential: `Γ;Γ' ⊢ Δ';Δ` becomes
`Γ, !Γ' ⊢ ?Δ', Δ`.  The "easy inductive argument" is `Formula.IsNeutralLinear.bang_quest`:
for a linear formula all of whose atoms are neutral,

* if `P` is positive then `P ⊢ !P` is provable in LL, and
* if `N` is negative then `?N ⊢ N` is provable in LL.

(From `P ⊢ !P` the strengthened `!` rule follows by cuts.)  The main result is
`LL.of_derivable_neutralLinear`: every LU derivation (with cuts) all of whose sequents are
made of neutral linear formulas translates into an LL derivation (with cut) of the
translated sequent.  In particular (`LL.of_provable_neutralLinear`), for such a derivation
of `Γ; ⊢ ;Δ`, the sequent `Γ ⊢ Δ` is provable in linear logic.  Together with
`LL.provable` this is the equivalence of §4 (stated as `provable_iff_LL` in
`Table3Soundness.lean`).
-/

@[expose] public section

namespace LU

variable {n : ℕ}

open Formula

/-! ## Neutral linear formulas -/

/-- Linear formulas all of whose atoms are neutral ("declaring all atomic propositions to
be neutral", §4). -/
def Formula.IsNeutralLinear {n : ℕ} : Formula n → Prop
  | atom p _ => p.pol = .neu
  | one => True
  | zero => True
  | bot => True
  | top => True
  | neg A => A.IsNeutralLinear
  | bang A => A.IsNeutralLinear
  | quest A => A.IsNeutralLinear
  | tensor A B => A.IsNeutralLinear ∧ B.IsNeutralLinear
  | par A B => A.IsNeutralLinear ∧ B.IsNeutralLinear
  | lolli A B => A.IsNeutralLinear ∧ B.IsNeutralLinear
  | with_ A B => A.IsNeutralLinear ∧ B.IsNeutralLinear
  | plus A B => A.IsNeutralLinear ∧ B.IsNeutralLinear
  | lall A => A.IsNeutralLinear
  | lex A => A.IsNeutralLinear
  | _ => False

@[simp] theorem Formula.isNeutralLinear_subst {m : ℕ} (A : Formula n) (σ : Subst n m) :
    (A.subst σ).IsNeutralLinear ↔ A.IsNeutralLinear := by
  induction A generalizing m <;> simp_all [subst, IsNeutralLinear]

theorem subClosed_neutralLinear : SubClosed IsNeutralLinear where
  neg _ h := h
  bang _ h := h
  quest _ h := h
  tensor _ _ h := h
  par _ _ h := h
  lolli _ _ h := h
  with_ _ _ h := h
  plus _ _ h := h
  conj _ _ h := h.elim
  disj _ _ h := h.elim
  imp _ _ h := h.elim
  iimp _ _ h := h.elim
  lall _ h := h
  lex _ h := h
  call _ h := h.elim
  cex _ h := h.elim
  shift A h := by simpa [shift] using h
  inst A t h := by simpa [inst] using h

theorem Formula.IsNeutralLinear.isLinear {A : Formula n} (h : A.IsNeutralLinear) :
    A.IsLinear := by
  induction A <;> simp_all [IsNeutralLinear, IsLinear]

/-- Close an equation between multisets built from `+`, `::ₘ`, `{·}`, `0`, `map` and `sh`. -/
local macro "mset_tac" : tactic => `(tactic| ((try simp only [← Multiset.singleton_add,
  Multiset.insert_eq_cons, sh, Multiset.map_add, Multiset.map_singleton, Multiset.map_zero,
  Multiset.map_cons]) <;> (try simp only [← Multiset.singleton_add]) <;> abel))

/-- `llc h`: use `h` up to an equation between the multisets of both sides. -/
local macro "llc " h:term : term => `(LL.congr $h (by mset_tac) (by mset_tac))

/-! ## Some derived rules of LL -/

namespace LL

theorem cut' {Γ Λ Δ Θ : Multiset (Formula n)} (A : Formula n) (h₁ : LL true Γ (A ::ₘ Δ))
    (h₂ : LL true (A ::ₘ Λ) Θ) : LL true (Γ + Λ) (Δ + Θ) := .cut A rfl h₁ h₂

/-- Contraction of a whole multiset `!M`. -/
theorem bangC_all {b : Bool} (M : Multiset (Formula n)) :
    ∀ {Γ Δ : Multiset (Formula n)}, LL b (M.map bang + M.map bang + Γ) Δ →
      LL b (M.map bang + Γ) Δ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Δ h; simpa using h
  | cons a M ih =>
    intro Γ Δ h
    have h1 : LL b (M.map bang + M.map bang + (bang a ::ₘ bang a ::ₘ Γ)) Δ := llc h
    have h2 : LL b (bang a ::ₘ bang a ::ₘ (M.map bang + Γ)) Δ := llc (ih h1)
    exact llc (LL.bangC h2)

/-- Contraction of a whole multiset `?M`. -/
theorem questC_all {b : Bool} (M : Multiset (Formula n)) :
    ∀ {Γ Δ : Multiset (Formula n)}, LL b Γ (M.map quest + M.map quest + Δ) →
      LL b Γ (M.map quest + Δ) := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Δ h; simpa using h
  | cons a M ih =>
    intro Γ Δ h
    have h1 : LL b Γ (M.map quest + M.map quest + (quest a ::ₘ quest a ::ₘ Δ)) := llc h
    have h2 : LL b Γ (quest a ::ₘ quest a ::ₘ (M.map quest + Δ)) := llc (ih h1)
    exact llc (LL.questC h2)

/-- Contraction of the translated central zones `!Γ'` and `?Δ'`. -/
theorem contr_central {b : Bool} {Γ' Δ' Γ Δ : Multiset (Formula n)}
    (h : LL b (Γ.map bang + Γ.map bang + Γ') (Δ.map quest + Δ.map quest + Δ')) :
    LL b (Γ.map bang + Γ') (Δ.map quest + Δ') :=
  bangC_all Γ (questC_all Δ h)

/-- Inserting a formula in a central zone translated by a map `F` producing `!`-formulas
(left): with the formula already present, this is a contraction (resp. a weakening). -/
theorem central_insertL {m : ℕ} {b : Bool} {F : Formula m → Formula n}
    (hF : ∀ B, ∃ X, F B = bang X) {A : Formula m} {C : Finset (Formula m)}
    {Γ Δ : Multiset (Formula n)} :
    LL b (F A ::ₘ (Γ + C.val.map F)) Δ ↔ LL b (Γ + (insert A C).val.map F) Δ := by
  by_cases hA : A ∈ C
  · rw [Finset.insert_eq_of_mem hA]
    obtain ⟨X, hX⟩ := hF A
    obtain ⟨C', hC'⟩ : ∃ C', C.val = A ::ₘ C' := ⟨C.val.erase A, (Multiset.cons_erase hA).symm⟩
    rw [hC', Multiset.map_cons, hX]
    constructor
    · intro h
      have h1 : LL b (bang X ::ₘ bang X ::ₘ (Γ + C'.map F)) Δ := llc h
      exact llc (LL.bangC h1)
    · intro h
      exact LL.bangW X h
  · rw [Finset.insert_val_of_notMem hA, Multiset.map_cons]
    constructor <;> intro h <;> exact llc h

/-- Inserting a formula in a central zone translated by a map `F` producing `?`-formulas
(right). -/
theorem central_insertR {m : ℕ} {b : Bool} {F : Formula m → Formula n}
    (hF : ∀ B, ∃ X, F B = quest X) {A : Formula m} {C : Finset (Formula m)}
    {Γ Δ : Multiset (Formula n)} :
    LL b Γ (F A ::ₘ (C.val.map F + Δ)) ↔ LL b Γ ((insert A C).val.map F + Δ) := by
  by_cases hA : A ∈ C
  · rw [Finset.insert_eq_of_mem hA]
    obtain ⟨X, hX⟩ := hF A
    obtain ⟨C', hC'⟩ : ∃ C', C.val = A ::ₘ C' := ⟨C.val.erase A, (Multiset.cons_erase hA).symm⟩
    rw [hC', Multiset.map_cons, hX]
    constructor
    · intro h
      have h1 : LL b Γ (quest X ::ₘ quest X ::ₘ (C'.map F + Δ)) := llc h
      exact llc (LL.questC h1)
    · intro h
      exact llc (LL.questW X h)
  · rw [Finset.insert_val_of_notMem hA, Multiset.map_cons]
    constructor <;> intro h <;> exact llc h

end LL

/-! ## The "easy inductive argument" -/

/-- **Strengthened `!` rule** (§4).  For a linear formula with neutral atoms: if `A` is
positive then `A ⊢ !A` is provable in LL, and if `A` is negative then `?A ⊢ A` is provable
in LL. -/
theorem Formula.IsNeutralLinear.bang_quest {A : Formula n} (hA : A.IsNeutralLinear) :
    (A.pol = .pos → LL true {A} {bang A}) ∧ (A.pol = .neg → LL true {quest A} {A}) := by
  induction A with
  | atom p ts => simp_all [IsNeutralLinear, pol]
  | @one k =>
    refine ⟨fun _ => ?_, fun h => by simp [pol] at h⟩
    have h1 : LL true (Multiset.map bang 0) ((one : Formula k) ::ₘ Multiset.map quest 0) :=
      llc LL.oneR
    have h2 : LL true 0 {bang one} := llc (LL.bangR h1)
    exact llc (LL.oneL h2)
  | zero => exact ⟨fun _ => llc (LL.zeroL 0 {bang zero}), fun h => by simp [pol] at h⟩
  | @bot k =>
    refine ⟨fun h => by simp [pol] at h, fun _ => ?_⟩
    have h1 : LL true ((bot : Formula k) ::ₘ Multiset.map bang 0) (Multiset.map quest 0) :=
      llc LL.botL
    have h2 : LL true {quest bot} 0 := llc (LL.questL h1)
    exact llc (LL.botR h2)
  | top => exact ⟨fun h => by simp [pol] at h, fun _ => llc (LL.topR {quest top} 0)⟩
  | neg A ih =>
    replace ih := ih hA
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hA' : A.pol = .neg := by cases hp : A.pol <;> simp_all [pol, Pol.dual]
      -- `⊢ ¬A, A` ⟶ `⊢ ¬A, ?A` ⟶ `⊢ !¬A, ?A` ⟶ (cut `?A ⊢ A`) `⊢ !¬A, A` ⟶ `¬A ⊢ !¬A`
      have h1 : LL true 0 (A ::ₘ {neg A}) := llc (LL.negR (LL.ax A))
      have h2 : LL true (Multiset.map bang 0) (neg A ::ₘ Multiset.map quest {A}) :=
        llc (LL.questD h1)
      have h3 : LL true 0 (quest A ::ₘ {bang (neg A)}) := llc (LL.bangR h2)
      have h4 : LL true 0 (A ::ₘ {bang (neg A)}) := llc (LL.cut' (Λ := 0) _ h3 (ih.2 hA'))
      exact llc (LL.negL h4)
    · have hA' : A.pol = .pos := by cases hp : A.pol <;> simp_all [pol, Pol.dual]
      -- `¬A, A ⊢` ⟶ `¬A, !A ⊢` ⟶ `?¬A, !A ⊢` ⟶ (cut `A ⊢ !A`) `?¬A, A ⊢` ⟶ `?¬A ⊢ ¬A`
      have h1 : LL true (A ::ₘ {neg A}) 0 := llc (LL.negL ((LL.ax A).congr rfl rfl))
      have h2 : LL true (neg A ::ₘ Multiset.map bang {A}) (Multiset.map quest 0) :=
        llc (LL.bangD h1)
      have h3 : LL true (bang A ::ₘ {quest (neg A)}) 0 := llc (LL.questL h2)
      have h4 : LL true (A ::ₘ {quest (neg A)}) 0 := llc (LL.cut' _ (ih.1 hA') h3)
      exact llc (LL.negR h4)
  | bang A ih =>
    refine ⟨fun _ => ?_, fun h => by simp [pol] at h⟩
    have h1 : LL true (Multiset.map bang {A}) (bang A ::ₘ Multiset.map quest 0) :=
      llc (LL.ax (bang A))
    exact llc (LL.bangR h1)
  | quest A ih =>
    refine ⟨fun h => by simp [pol] at h, fun _ => ?_⟩
    have h1 : LL true (quest A ::ₘ Multiset.map bang 0) (Multiset.map quest {A}) :=
      llc (LL.ax (quest A))
    exact llc (LL.questL h1)
  | tensor A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hA
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ⟨hA', hB'⟩ : A.pol = .pos ∧ B.pol = .pos := by
        cases hp : A.pol <;> cases hq : B.pol <;> simp_all [pol, Pol.tensor]
      have h1 : LL true (A ::ₘ {B}) {tensor A B} := llc (LL.tensorR (LL.ax A) (LL.ax B))
      have h2 : LL true (B ::ₘ {bang A}) {tensor A B} := llc (LL.bangD h1)
      have h3 : LL true (Multiset.map bang {A, B}) (tensor A B ::ₘ Multiset.map quest 0) :=
        llc (LL.bangD h2)
      have h4 : LL true (bang B ::ₘ {bang A}) {bang (tensor A B)} := llc (LL.bangR h3)
      have h5 : LL true (bang A ::ₘ {B}) {bang (tensor A B)} :=
        llc (LL.cut' _ (ihB hB |>.1 hB') h4)
      have h6 : LL true (A ::ₘ {B}) {bang (tensor A B)} :=
        llc (LL.cut' _ (ihA hA |>.1 hA') h5)
      exact llc (LL.tensorL h6)
    · simp only [pol, Pol.tensor] at h; split at h <;> simp_all
  | par A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hA
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [pol, Pol.par] at h; split at h <;> simp_all
    · have ⟨hA', hB'⟩ : A.pol = .neg ∧ B.pol = .neg := by
        cases hp : A.pol <;> cases hq : B.pol <;> simp_all [pol, Pol.par]
      have h1 : LL true {par A B} (A ::ₘ {B}) := llc (LL.parL (LL.ax A) (LL.ax B))
      have h2 : LL true {par A B} (B ::ₘ {quest A}) := llc (LL.questD h1)
      have h3 : LL true (par A B ::ₘ Multiset.map bang 0) (Multiset.map quest {A, B}) :=
        llc (LL.questD h2)
      have h4 : LL true {quest (par A B)} (quest A ::ₘ {quest B}) := llc (LL.questL h3)
      have h5 : LL true {quest (par A B)} (quest B ::ₘ {A}) :=
        llc (LL.cut' (Λ := 0) _ h4 (ihA hA |>.2 hA'))
      have h6 : LL true {quest (par A B)} (A ::ₘ {B}) :=
        llc (LL.cut' (Λ := 0) _ h5 (ihB hB |>.2 hB'))
      exact llc (LL.parR h6)
  | lolli A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hA
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [pol, Pol.lolli] at h; split at h <;> simp_all
    · have ⟨hA', hB'⟩ : A.pol = .pos ∧ B.pol = .neg := by
        cases hp : A.pol <;> cases hq : B.pol <;> simp_all [pol, Pol.lolli]
      have h1 : LL true (A ::ₘ {lolli A B}) {B} := llc (LL.lolliL (LL.ax A) (LL.ax B))
      have h2 : LL true (lolli A B ::ₘ {bang A}) {B} := llc (LL.bangD h1)
      have h3 : LL true (lolli A B ::ₘ Multiset.map bang {A}) (Multiset.map quest {B}) :=
        llc (LL.questD h2)
      have h4 : LL true (bang A ::ₘ {quest (lolli A B)}) {quest B} := llc (LL.questL h3)
      have h5 : LL true (A ::ₘ {quest (lolli A B)}) {quest B} :=
        llc (LL.cut' _ (ihA hA |>.1 hA') h4)
      have h6 : LL true (A ::ₘ {quest (lolli A B)}) {B} :=
        llc (LL.cut' (Λ := 0) _ h5 (ihB hB |>.2 hB'))
      exact llc (LL.lolliR h6)
  | with_ A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hA
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [pol, Pol.with_] at h; split at h <;> simp_all
    · have ⟨hA', hB'⟩ : A.pol = .neg ∧ B.pol = .neg := by
        cases hp : A.pol <;> cases hq : B.pol <;> simp_all [pol, Pol.with_]
      have hl : LL true {quest (with_ A B)} {A} := by
        have h1 : LL true (with_ A B ::ₘ Multiset.map bang 0) (Multiset.map quest {A}) :=
          llc (LL.questD (LL.withL₁ B (LL.ax A)))
        have h2 : LL true {quest (with_ A B)} {quest A} := llc (LL.questL h1)
        exact llc (LL.cut' (Λ := 0) _ h2 (ihA hA |>.2 hA'))
      have hr : LL true {quest (with_ A B)} {B} := by
        have h1 : LL true (with_ A B ::ₘ Multiset.map bang 0) (Multiset.map quest {B}) :=
          llc (LL.questD (LL.withL₂ A (LL.ax B)))
        have h2 : LL true {quest (with_ A B)} {quest B} := llc (LL.questL h1)
        exact llc (LL.cut' (Λ := 0) _ h2 (ihB hB |>.2 hB'))
      have hl' : LL true {quest (with_ A B)} (A ::ₘ 0) := llc hl
      have hr' : LL true {quest (with_ A B)} (B ::ₘ 0) := llc hr
      exact llc (LL.withR hl' hr')
  | plus A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hA
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ⟨hA', hB'⟩ : A.pol = .pos ∧ B.pol = .pos := by
        cases hp : A.pol <;> cases hq : B.pol <;> simp_all [pol, Pol.plus]
      have hl : LL true {A} {bang (plus A B)} := by
        have h1 : LL true (Multiset.map bang {A}) (plus A B ::ₘ Multiset.map quest 0) :=
          llc (LL.bangD (LL.plusR₁ B (LL.ax A)))
        have h2 : LL true {bang A} {bang (plus A B)} := llc (LL.bangR h1)
        exact llc (LL.cut' _ (ihA hA |>.1 hA') h2)
      have hr : LL true {B} {bang (plus A B)} := by
        have h1 : LL true (Multiset.map bang {B}) (plus A B ::ₘ Multiset.map quest 0) :=
          llc (LL.bangD (LL.plusR₂ A (LL.ax B)))
        have h2 : LL true {bang B} {bang (plus A B)} := llc (LL.bangR h1)
        exact llc (LL.cut' _ (ihB hB |>.1 hB') h2)
      have hl' : LL true (A ::ₘ 0) {bang (plus A B)} := llc hl
      have hr' : LL true (B ::ₘ 0) {bang (plus A B)} := llc hr
      exact llc (LL.plusL hl' hr')
    · simp only [pol, Pol.plus] at h; split at h <;> simp_all
  | lall A ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [pol, Pol.lall] at h; split at h <;> simp_all
    · have hA' : A.pol = .neg := by cases hp : A.pol <;> simp_all [pol, Pol.lall]
      have h0 : LL true ((A.subst (Subst.lift (Subst.weaken _))).inst (.var 0) ::ₘ 0) {A} := by simpa using LL.ax A
      have h1 : LL true (lall (A.subst (Subst.lift (Subst.weaken _))) ::ₘ Multiset.map bang 0)
          (Multiset.map quest {A}) := llc (LL.questD (LL.lallL (.var 0) h0))
      have h2 : LL true {quest (lall (A.subst (Subst.lift (Subst.weaken _))))} {quest A} := llc (LL.questL h1)
      have h3 : LL true {quest (lall (A.subst (Subst.lift (Subst.weaken _))))} {A} :=
        llc (LL.cut' (Λ := 0) _ h2 (ih hA |>.2 hA'))
      have h4 : LL true (sh {quest (lall A)}) (A ::ₘ sh 0) := by
        simpa [sh, Formula.shift, Formula.subst] using h3
      exact LL.lallR h4
  | lex A ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hA' : A.pol = .pos := by cases hp : A.pol <;> simp_all [pol, Pol.lex]
      have h0 : LL true {A} ((A.subst (Subst.lift (Subst.weaken _))).inst (.var 0) ::ₘ 0) := by simpa using LL.ax A
      have h1 : LL true (Multiset.map bang {A}) (lex (A.subst (Subst.lift (Subst.weaken _))) ::ₘ Multiset.map quest 0) :=
        llc (LL.bangD (LL.lexR (.var 0) h0))
      have h2 : LL true {bang A} {bang (lex (A.subst (Subst.lift (Subst.weaken _))))} := llc (LL.bangR h1)
      have h3 : LL true {A} {bang (lex (A.subst (Subst.lift (Subst.weaken _))))} :=
        llc (LL.cut' _ (ih hA |>.1 hA') h2)
      have h4 : LL true (A ::ₘ sh 0) (sh {bang (lex A)}) := by
        simpa [sh, Formula.shift, Formula.subst] using h3
      exact LL.lexL h4
    · simp only [pol, Pol.lex] at h; split at h <;> simp_all
  | _ => simp [IsNeutralLinear] at hA

/-! ## The strengthened `!` rule -/

namespace LL

theorem bangD_all {b : Bool} (M : Multiset (Formula n)) :
    ∀ {Γ Δ : Multiset (Formula n)}, LL b (M + Γ) Δ → LL b (M.map bang + Γ) Δ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Δ h; simpa using h
  | cons a M ih =>
    intro Γ Δ h
    have h1 : LL b (M + (a ::ₘ Γ)) Δ := llc h
    have h2 : LL b (a ::ₘ (M.map bang + Γ)) Δ := llc (ih h1)
    exact llc (LL.bangD h2)

theorem questD_all {b : Bool} (M : Multiset (Formula n)) :
    ∀ {Γ Δ : Multiset (Formula n)}, LL b Γ (M + Δ) → LL b Γ (M.map quest + Δ) := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Δ h; simpa using h
  | cons a M ih =>
    intro Γ Δ h
    have h1 : LL b Γ (M + (a ::ₘ Δ)) := llc h
    have h2 : LL b Γ (a ::ₘ (M.map quest + Δ)) := llc (ih h1)
    exact llc (LL.questD h2)

/-- Remove the `!` of positive neutral linear formulas on the left (by cuts with `P ⊢ !P`). -/
theorem unbang_all (M : Multiset (Formula n)) (hM : ∀ P ∈ M, P.IsNeutralLinear ∧ P.pol = .pos) :
    ∀ {Γ Δ : Multiset (Formula n)}, LL true (M.map bang + Γ) Δ → LL true (M + Γ) Δ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Δ h; simpa using h
  | cons a M ih =>
    intro Γ Δ h
    have ha := hM a (Multiset.mem_cons_self _ _)
    have h1 : LL true (bang a ::ₘ (M.map bang + Γ)) Δ := llc h
    have h2 : LL true (M.map bang + (a ::ₘ Γ)) Δ := llc (LL.cut' _ (ha.1.bang_quest.1 ha.2) h1)
    exact llc (ih (fun P hP => hM P (Multiset.mem_cons_of_mem hP)) h2)

/-- Remove the `?` of negative neutral linear formulas on the right (by cuts with `?N ⊢ N`). -/
theorem unquest_all (M : Multiset (Formula n)) (hM : ∀ N ∈ M, N.IsNeutralLinear ∧ N.pol = .neg) :
    ∀ {Γ Δ : Multiset (Formula n)}, LL true Γ (M.map quest + Δ) → LL true Γ (M + Δ) := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Δ h; simpa using h
  | cons a M ih =>
    intro Γ Δ h
    have ha := hM a (Multiset.mem_cons_self _ _)
    have h1 : LL true Γ (quest a ::ₘ (M.map quest + Δ)) := llc h
    have h2 : LL true Γ (M.map quest + (a ::ₘ Δ)) :=
      llc (LL.cut' (Λ := 0) _ h1 (ha.1.bang_quest.2 ha.2))
    exact llc (ih (fun P hP => hM P (Multiset.mem_cons_of_mem hP)) h2)

/-- **The strengthened rule for `!`** (§4): in linear logic with neutral atoms, one can pass
from `Γ ⊢ Δ, A` to `Γ ⊢ Δ, !A` as soon as `Γ` is positive and `Δ` negative. -/
theorem bangR_strong {Γ Δ : Multiset (Formula n)} {A : Formula n}
    (hΓ : ∀ P ∈ Γ, P.IsNeutralLinear ∧ P.pol = .pos)
    (hΔ : ∀ N ∈ Δ, N.IsNeutralLinear ∧ N.pol = .neg) (h : LL true Γ (A ::ₘ Δ)) :
    LL true Γ (bang A ::ₘ Δ) := by
  have h1 : LL true (Γ.map bang + 0) (A ::ₘ Δ) := bangD_all Γ (llc h)
  have h2 : LL true (Γ.map bang) (A ::ₘ Δ.map quest) := llc (questD_all Δ (Γ := Γ.map bang)
    (Δ := {A}) (llc h1))
  have h3 : LL true (Γ.map bang + 0) (Δ.map quest + {bang A}) := llc (LL.bangR h2)
  have h4 : LL true (Γ + 0) (Δ.map quest + {bang A}) := unbang_all Γ hΓ h3
  exact llc (unquest_all Δ hΔ h4)

end LL

/-! ## Translating LU derivations into LL -/

theorem sh_add (Γ Δ : Multiset (Formula n)) : sh (Γ + Δ) = sh Γ + sh Δ := Multiset.map_add _ _ _

theorem sh_map_bang (Γ : Multiset (Formula n)) : sh (Γ.map bang) = (sh Γ).map bang := by
  simp [sh, Multiset.map_map, Formula.shift, Formula.subst]

theorem sh_map_quest (Γ : Multiset (Formula n)) : sh (Γ.map quest) = (sh Γ).map quest := by
  simp [sh, Multiset.map_map, Formula.shift, Formula.subst]

set_option maxHeartbeats 4000000 in
/-- **Translation of LU into LL** (§4).  An LU derivation (possibly with cuts) all of whose
sequents consist of linear formulas with neutral atoms, of a sequent `Γ;Γ' ⊢ Δ';Δ`, yields an
LL derivation (with cut) of `Γ, !Γ' ⊢ ?Δ', Δ`. -/
theorem LL.of_derivable_neutralLinear {S : Sequent n}
    (h : Derivable LURule (AllIn IsNeutralLinear) S) :
    LL true (S.L + S.CL.val.map bang) (S.CR.val.map quest + S.R) := by
  induction h with
  | mk ps c hr hc hs hu ihs ihu =>
  have ih := Premise.forall_all
    (Q := fun s => LL true (s.L + s.CL.val.map bang) (s.CR.val.map quest + s.R)) ihs ihu
  clear hs hu ihs ihu
  have hB : ∀ {k : ℕ} (B : Formula k), ∃ X, bang B = bang X := fun B => ⟨B, rfl⟩
  have hQ : ∀ {k : ℕ} (B : Formula k), ∃ X, quest B = quest X := fun B => ⟨B, rfl⟩
  rcases hr with hr | hr
  · cases hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        IsEmpty.forall_iff, implies_true, Premise.all_same, Premise.all_up] at ih <;>
      (try (simp [allIn_mk, IsNeutralLinear] at hc; done)) <;>
      dsimp only at ih ⊢
    case ax A => exact llc (LL.ax A)
    case weakR Γ Γ' Δ' Δ A => exact (LL.central_insertR hQ).1 (llc (LL.questW A ih))
    case weakL Γ Γ' Δ' Δ A => exact (LL.central_insertL hB).1 (LL.bangW A ih)
    case inR Γ Γ' Δ' Δ A =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact (LL.central_insertR hQ).1 (LL.questD h1)
    case inL Γ Γ' Δ' Δ A =>
      have h1 : LL true (A ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih
      exact (LL.central_insertL hB).1 (LL.bangD h1)
    case outR Γ Γ' Δ' Δ N hN =>
      have hN' : N.IsNeutralLinear := hc N (by simp [Sequent.formulas])
      have h1 : LL true (Γ + Γ'.val.map bang) (quest N ::ₘ (Δ'.val.map quest + Δ)) :=
        (LL.central_insertR hQ).2 ih
      exact llc (LL.cut' (Λ := 0) _ h1 (hN'.bang_quest.2 hN))
    case outL Γ Γ' Δ' Δ P hP =>
      have hP' : P.IsNeutralLinear := hc P (by simp [Sequent.formulas])
      have h1 : LL true (bang P ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) :=
        (LL.central_insertL hB).2 ih
      exact llc (LL.cut' _ (hP'.bang_quest.1 hP) h1)
    case oneR => exact llc LL.oneR
    case botL => exact llc LL.botL
    case tensorR Γ Λ Γ' Δ' Δ Θ A B =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih.1
      have h2 : LL true (Λ + Γ'.val.map bang) (B ::ₘ (Δ'.val.map quest + Θ)) := llc ih.2
      have h3 : LL true (Γ'.val.map bang + Γ'.val.map bang + (Γ + Λ))
          (Δ'.val.map quest + Δ'.val.map quest + (tensor A B ::ₘ (Δ + Θ))) := llc (LL.tensorR h1 h2)
      exact llc (LL.contr_central h3)
    case tensorL Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A ::ₘ B ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih
      exact llc (LL.tensorL h1)
    case parR Γ Γ' Δ' Δ A B =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ B ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact llc (LL.parR h1)
    case parL Γ Λ Γ' Δ' Δ Θ A B =>
      have h1 : LL true (A ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih.1
      have h2 : LL true (B ::ₘ (Λ + Γ'.val.map bang)) (Δ'.val.map quest + Θ) := llc ih.2
      have h3 : LL true (Γ'.val.map bang + Γ'.val.map bang + (par A B ::ₘ (Γ + Λ)))
          (Δ'.val.map quest + Δ'.val.map quest + (Δ + Θ)) := llc (LL.parL h1 h2)
      exact llc (LL.contr_central h3)
    case lolliR Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A ::ₘ (Γ + Γ'.val.map bang)) (B ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact llc (LL.lolliR h1)
    case lolliL Γ Λ Γ' Δ' Δ Θ A B =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih.1
      have h2 : LL true (B ::ₘ (Λ + Γ'.val.map bang)) (Δ'.val.map quest + Θ) := llc ih.2
      have h3 : LL true (Γ'.val.map bang + Γ'.val.map bang + (lolli A B ::ₘ (Γ + Λ)))
          (Δ'.val.map quest + Δ'.val.map quest + (Δ + Θ)) := llc (LL.lolliL h1 h2)
      exact llc (LL.contr_central h3)
    case topR Γ Δ => exact llc (LL.topR Γ Δ)
    case zeroL Γ Δ => exact llc (LL.zeroL Γ Δ)
    case withR Γ Γ' Δ' Δ A B =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih.1
      have h2 : LL true (Γ + Γ'.val.map bang) (B ::ₘ (Δ'.val.map quest + Δ)) := llc ih.2
      exact llc (LL.withR h1 h2)
    case withL₁ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih
      exact llc (LL.withL₁ B h1)
    case withL₂ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (B ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih
      exact llc (LL.withL₂ A h1)
    case plusR₁ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact llc (LL.plusR₁ B h1)
    case plusR₂ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (Γ + Γ'.val.map bang) (B ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact llc (LL.plusR₂ A h1)
    case plusL Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih.1
      have h2 : LL true (B ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih.2
      exact llc (LL.plusL h1 h2)
    case negL Γ Γ' Δ' Δ A =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact llc (LL.negL h1)
    case negR Γ Γ' Δ' Δ A =>
      have h1 : LL true (A ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih
      exact llc (LL.negR h1)
    case bangR Γ' Δ' A =>
      have h1 : LL true (Γ'.val.map bang) (A ::ₘ Δ'.val.map quest) := llc ih
      exact llc (LL.bangR h1)
    case bangL Γ Γ' Δ' Δ A => exact llc ((LL.central_insertL hB).2 ih)
    case questR Γ Γ' Δ' Δ A => exact llc ((LL.central_insertR hQ).2 ih)
    case questL Γ' Δ' A =>
      have h1 : LL true (A ::ₘ Γ'.val.map bang) (Δ'.val.map quest) := llc ih
      exact llc (LL.questL h1)
    case lallR Γ Γ' Δ' Δ A =>
      have h1 : LL true (sh (Γ + Γ'.val.map bang)) (A ::ₘ sh (Δ'.val.map quest + Δ)) := by
        rw [sh_add, sh_add, sh_map_bang, sh_map_quest, ← shc_val, ← shc_val]; exact llc ih
      exact llc (LL.lallR h1)
    case lallL Γ Γ' Δ' Δ A t =>
      have h1 : LL true (A.inst t ::ₘ (Γ + Γ'.val.map bang)) (Δ'.val.map quest + Δ) := llc ih
      exact llc (LL.lallL t h1)
    case lexR Γ Γ' Δ' Δ A t =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A.inst t ::ₘ (Δ'.val.map quest + Δ)) := llc ih
      exact llc (LL.lexR t h1)
    case lexL Γ Γ' Δ' Δ A =>
      have h1 : LL true (A ::ₘ sh (Γ + Γ'.val.map bang)) (sh (Δ'.val.map quest + Δ)) := by
        rw [sh_add, sh_add, sh_map_bang, sh_map_quest, ← shc_val, ← shc_val]; exact llc ih
      exact llc (LL.lexL h1)
  · cases hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Premise.all_same] at ih <;>
      dsimp only at ih ⊢
    case cut Γ Λ Γ' Δ' Δ Θ A =>
      have h1 : LL true (Γ + Γ'.val.map bang) (A ::ₘ (Δ'.val.map quest + Δ)) := llc ih.1
      have h2 : LL true (A ::ₘ (Λ + Γ'.val.map bang)) (Δ'.val.map quest + Θ) := llc ih.2
      have h3 : LL true (Γ'.val.map bang + Γ'.val.map bang + (Γ + Λ))
          (Δ'.val.map quest + Δ'.val.map quest + (Δ + Θ)) := llc (LL.cut' A h1 h2)
      exact llc (LL.contr_central h3)
    case cutR Γ Γ' Δ' Δ A =>
      have h1 : LL true (Γ + Γ'.val.map bang) (quest A ::ₘ (Δ'.val.map quest + Δ)) :=
        (LL.central_insertR hQ).2 ih.1
      have h2 : LL true (A ::ₘ Γ'.val.map bang) (Δ'.val.map quest) := llc ih.2
      have h3 : LL true (Γ'.val.map bang + Γ'.val.map bang + Γ)
          (Δ'.val.map quest + Δ'.val.map quest + Δ) := llc (LL.cut' _ h1 (LL.questL h2))
      exact llc (LL.contr_central h3)
    case cutL Λ Γ' Δ' Θ A =>
      have h1 : LL true (Γ'.val.map bang) (A ::ₘ Δ'.val.map quest) := llc ih.1
      have h2 : LL true (bang A ::ₘ (Λ + Γ'.val.map bang)) (Δ'.val.map quest + Θ) :=
        (LL.central_insertL hB).2 ih.2
      have h3 : LL true (Γ'.val.map bang + Γ'.val.map bang + Λ)
          (Δ'.val.map quest + Δ'.val.map quest + Θ) := llc (LL.cut' _ (LL.bangR h1) h2)
      exact llc (LL.contr_central h3)

/-- §4, LU to LL: if `Γ; ⊢ ;Δ` has an LU derivation (possibly with cuts) in which every
sequent consists of linear formulas with neutral atoms, then `Γ ⊢ Δ` is provable in linear
logic. -/
theorem LL.of_provable_neutralLinear {Γ Δ : Multiset (Formula n)}
    (h : Derivable LURule (AllIn IsNeutralLinear) ⟪Γ ; ∅ ⊢ ∅ ; Δ⟫) : LL true Γ Δ := by
  simpa using LL.of_derivable_neutralLinear h

/-- §4, LU to LL, cut-free version: a cut-free LU proof of `Γ; ⊢ ;Δ` in which every formula
is linear with neutral atoms translates into an LL proof of `Γ ⊢ Δ`.  (The hypothesis is only
on the end-sequent: by the subformula property, it propagates to the whole proof.) -/
theorem LL.of_cutFreeProvable_neutralLinear {Γ Δ : Multiset (Formula n)}
    (h : CutFreeProvable ⟪Γ ; ∅ ⊢ ∅ ; Δ⟫) (hS : AllIn IsNeutralLinear ⟪Γ ; ∅ ⊢ ∅ ; Δ⟫) :
    LL true Γ Δ := by
  have h' := Derivable.allIn subClosed_neutralLinear h hS
  exact LL.of_provable_neutralLinear
    (Derivable.mono (fun _ _ hr => Or.inl hr) (fun _ hs => hs.2) h')

end LU
