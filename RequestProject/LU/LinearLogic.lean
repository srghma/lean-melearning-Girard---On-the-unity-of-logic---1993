module

public import RequestProject.LU.Fragments

/-!
# §4: usual linear logic, and its translation into LU

> This calculus is equivalent to the usual linear logic; more precisely we can translate the
> usual linear logic into this new system by declaring all atomic propositions to be
> neutral.  Then a sequent `Γ ⊢ Δ` in the usual (two-sided) linear logic becomes `Γ; ⊢ ;Δ`.
> It is easy to translate proof to proof, though the rules for the exponentials `!` and `?`
> are translated by a heavy use of structural manipulations.  For instance, to pass from
> `!Γ; ⊢ ;?Δ, A` to `!Γ; ⊢ ;?Δ, !A`, we transit through `;!Γ ⊢ ?Δ;A`, then `;!Γ ⊢ ?Δ;!A`,
> and the ultimate moves to `!Γ; ⊢ ;?Δ, !A` use the polarities of `?Δ` and `!Γ`.

We define the usual two-sided sequent calculus of (first-order) linear logic, `LL b Γ Δ`
(`Γ ⊢ Δ`), with the cut rule available iff `b = true`, and prove:

* `LL.toLU`: every LL derivation of `Γ ⊢ Δ` translates into an LU derivation of `Γ; ⊢ ;Δ`,
  cut-free if the LL derivation is cut-free; hence `LL.provable` (`LL true Γ Δ → Provable`)
  and `LL.cutFreeProvable` (`LL false Γ Δ → CutFreeProvable`).

The translation is literally the one of the paper: the promotion rule is simulated by moving
`!Γ` and `?Δ` into the central zone, applying the `!`-rule of LU, and moving them back out
(`!Γ` is positive and `?Δ` negative).  The translation does not even depend on the polarity
of the atoms: it works for any formulas (the non-linear connectives just behave as atoms
in LL).
-/

@[expose] public section

namespace LU

open Formula

/-- The usual two-sided sequent calculus of first-order linear logic (Girard 1987).
`LL b Γ Δ` means that `Γ ⊢ Δ` is provable; the cut rule may only be used if `b = true`.
The eigenvariable conditions are expressed by shifting the contexts, as in LU. -/
inductive LL (b : Bool) : Multiset Formula → Multiset Formula → Prop where
  | ax (A : Formula) : LL b {A} {A}
  | cut {Γ Λ Δ Θ : Multiset Formula} (A : Formula) (hb : b = true) :
      LL b Γ (A ::ₘ Δ) → LL b (A ::ₘ Λ) Θ → LL b (Γ + Λ) (Δ + Θ)
  | oneR : LL b 0 {one}
  | oneL {Γ Δ : Multiset Formula} : LL b Γ Δ → LL b (one ::ₘ Γ) Δ
  | botL : LL b {bot} 0
  | botR {Γ Δ : Multiset Formula} : LL b Γ Δ → LL b Γ (bot ::ₘ Δ)
  | topR (Γ Δ : Multiset Formula) : LL b Γ (top ::ₘ Δ)
  | zeroL (Γ Δ : Multiset Formula) : LL b (zero ::ₘ Γ) Δ
  | tensorR {Γ Λ Δ Θ : Multiset Formula} {A B : Formula} :
      LL b Γ (A ::ₘ Δ) → LL b Λ (B ::ₘ Θ) → LL b (Γ + Λ) (tensor A B ::ₘ (Δ + Θ))
  | tensorL {Γ Δ : Multiset Formula} {A B : Formula} :
      LL b (A ::ₘ B ::ₘ Γ) Δ → LL b (tensor A B ::ₘ Γ) Δ
  | parR {Γ Δ : Multiset Formula} {A B : Formula} :
      LL b Γ (A ::ₘ B ::ₘ Δ) → LL b Γ (par A B ::ₘ Δ)
  | parL {Γ Λ Δ Θ : Multiset Formula} {A B : Formula} :
      LL b (A ::ₘ Γ) Δ → LL b (B ::ₘ Λ) Θ → LL b (par A B ::ₘ (Γ + Λ)) (Δ + Θ)
  | lolliR {Γ Δ : Multiset Formula} {A B : Formula} :
      LL b (A ::ₘ Γ) (B ::ₘ Δ) → LL b Γ (lolli A B ::ₘ Δ)
  | lolliL {Γ Λ Δ Θ : Multiset Formula} {A B : Formula} :
      LL b Γ (A ::ₘ Δ) → LL b (B ::ₘ Λ) Θ → LL b (lolli A B ::ₘ (Γ + Λ)) (Δ + Θ)
  | withR {Γ Δ : Multiset Formula} {A B : Formula} :
      LL b Γ (A ::ₘ Δ) → LL b Γ (B ::ₘ Δ) → LL b Γ (with_ A B ::ₘ Δ)
  | withL₁ {Γ Δ : Multiset Formula} {A : Formula} (B : Formula) :
      LL b (A ::ₘ Γ) Δ → LL b (with_ A B ::ₘ Γ) Δ
  | withL₂ {Γ Δ : Multiset Formula} (A : Formula) {B : Formula} :
      LL b (B ::ₘ Γ) Δ → LL b (with_ A B ::ₘ Γ) Δ
  | plusR₁ {Γ Δ : Multiset Formula} {A : Formula} (B : Formula) :
      LL b Γ (A ::ₘ Δ) → LL b Γ (plus A B ::ₘ Δ)
  | plusR₂ {Γ Δ : Multiset Formula} (A : Formula) {B : Formula} :
      LL b Γ (B ::ₘ Δ) → LL b Γ (plus A B ::ₘ Δ)
  | plusL {Γ Δ : Multiset Formula} {A B : Formula} :
      LL b (A ::ₘ Γ) Δ → LL b (B ::ₘ Γ) Δ → LL b (plus A B ::ₘ Γ) Δ
  | negL {Γ Δ : Multiset Formula} {A : Formula} : LL b Γ (A ::ₘ Δ) → LL b (neg A ::ₘ Γ) Δ
  | negR {Γ Δ : Multiset Formula} {A : Formula} : LL b (A ::ₘ Γ) Δ → LL b Γ (neg A ::ₘ Δ)
  /-- promotion: `!Γ ⊢ A, ?Δ / !Γ ⊢ !A, ?Δ` -/
  | bangR {Γ Δ : Multiset Formula} {A : Formula} :
      LL b (Γ.map bang) (A ::ₘ Δ.map quest) → LL b (Γ.map bang) (bang A ::ₘ Δ.map quest)
  /-- dereliction (left) -/
  | bangD {Γ Δ : Multiset Formula} {A : Formula} : LL b (A ::ₘ Γ) Δ → LL b (bang A ::ₘ Γ) Δ
  /-- weakening (left) -/
  | bangW {Γ Δ : Multiset Formula} (A : Formula) : LL b Γ Δ → LL b (bang A ::ₘ Γ) Δ
  /-- contraction (left) -/
  | bangC {Γ Δ : Multiset Formula} {A : Formula} :
      LL b (bang A ::ₘ bang A ::ₘ Γ) Δ → LL b (bang A ::ₘ Γ) Δ
  /-- `?`-left: `A, !Γ ⊢ ?Δ / ?A, !Γ ⊢ ?Δ` -/
  | questL {Γ Δ : Multiset Formula} {A : Formula} :
      LL b (A ::ₘ Γ.map bang) (Δ.map quest) → LL b (quest A ::ₘ Γ.map bang) (Δ.map quest)
  /-- dereliction (right) -/
  | questD {Γ Δ : Multiset Formula} {A : Formula} : LL b Γ (A ::ₘ Δ) → LL b Γ (quest A ::ₘ Δ)
  /-- weakening (right) -/
  | questW {Γ Δ : Multiset Formula} (A : Formula) : LL b Γ Δ → LL b Γ (quest A ::ₘ Δ)
  /-- contraction (right) -/
  | questC {Γ Δ : Multiset Formula} {A : Formula} :
      LL b Γ (quest A ::ₘ quest A ::ₘ Δ) → LL b Γ (quest A ::ₘ Δ)
  | lallR {Γ Δ : Multiset Formula} {A : Formula} : LL b (sh Γ) (A ::ₘ sh Δ) → LL b Γ (lall A ::ₘ Δ)
  | lallL {Γ Δ : Multiset Formula} {A : Formula} (t : Term) :
      LL b (A.inst t ::ₘ Γ) Δ → LL b (lall A ::ₘ Γ) Δ
  | lexR {Γ Δ : Multiset Formula} {A : Formula} (t : Term) :
      LL b Γ (A.inst t ::ₘ Δ) → LL b Γ (lex A ::ₘ Δ)
  | lexL {Γ Δ : Multiset Formula} {A : Formula} : LL b (A ::ₘ sh Γ) (sh Δ) → LL b (lex A ::ₘ Γ) Δ

namespace LL

theorem congr {b : Bool} {Γ Γ₁ Δ Δ₁ : Multiset Formula} (h : LL b Γ Δ) (e₁ : Γ = Γ₁)
    (e₂ : Δ = Δ₁) : LL b Γ₁ Δ₁ := e₁ ▸ e₂ ▸ h

/-- A cut-free LL derivation is in particular an LL derivation. -/
theorem withCut {b : Bool} {Γ Δ : Multiset Formula} (h : LL b Γ Δ) : LL true Γ Δ := by
  induction h with
  | ax A => exact .ax A
  | cut A _ _ _ ih₁ ih₂ => exact .cut A rfl ih₁ ih₂
  | oneR => exact .oneR
  | oneL _ ih => exact .oneL ih
  | botL => exact .botL
  | botR _ ih => exact .botR ih
  | topR Γ Δ => exact .topR Γ Δ
  | zeroL Γ Δ => exact .zeroL Γ Δ
  | tensorR _ _ ih₁ ih₂ => exact .tensorR ih₁ ih₂
  | tensorL _ ih => exact .tensorL ih
  | parR _ ih => exact .parR ih
  | parL _ _ ih₁ ih₂ => exact .parL ih₁ ih₂
  | lolliR _ ih => exact .lolliR ih
  | lolliL _ _ ih₁ ih₂ => exact .lolliL ih₁ ih₂
  | withR _ _ ih₁ ih₂ => exact .withR ih₁ ih₂
  | withL₁ B _ ih => exact .withL₁ B ih
  | withL₂ A _ ih => exact .withL₂ A ih
  | plusR₁ B _ ih => exact .plusR₁ B ih
  | plusR₂ A _ ih => exact .plusR₂ A ih
  | plusL _ _ ih₁ ih₂ => exact .plusL ih₁ ih₂
  | negL _ ih => exact .negL ih
  | negR _ ih => exact .negR ih
  | bangR _ ih => exact .bangR ih
  | bangD _ ih => exact .bangD ih
  | bangW A _ ih => exact .bangW A ih
  | bangC _ ih => exact .bangC ih
  | questL _ ih => exact .questL ih
  | questD _ ih => exact .questD ih
  | questW A _ ih => exact .questW A ih
  | questC _ ih => exact .questC ih
  | lallR _ ih => exact .lallR ih
  | lallL t _ ih => exact .lallL t ih
  | lexR t _ ih => exact .lexR t ih
  | lexL _ ih => exact .lexL ih

end LL

/-! ## From LL to LU -/

section ToLU

variable {R : List Sequent → Sequent → Prop} (hR : ∀ ps c, Rule ps c → R ps c)

/-- Derivability in LU with rules `R` and no restriction on sequents. -/
local notation "D" => Derivable R (fun _ => True)

include hR

omit hR in
theorem D_congr {S T : Sequent} (h : D S) (e : S = T) : D T := e ▸ h

theorem D_rule0 {c : Sequent} (hr : Rule [] c) : D c :=
  .mk [] c (hR _ _ hr) trivial (by simp)

theorem D_rule1 {p c : Sequent} (hr : Rule [p] c) (h : D p) : D c :=
  .mk [p] c (hR _ _ hr) trivial (by simpa using h)

theorem D_rule2 {p q c : Sequent} (hr : Rule [p, q] c) (hp : D p) (hq : D q) : D c :=
  .mk [p, q] c (hR _ _ hr) trivial (by simp [hp, hq])

/-- Move a multiset of formulas from the left linear zone into the central zone. -/
theorem D_inL_all (M : Multiset Formula) :
    ∀ {Γ Γ' Δ' Δ : Multiset Formula}, D ⟪M + Γ ; Γ' ⊢ Δ' ; Δ⟫ → D ⟪Γ ; M + Γ' ⊢ Δ' ; Δ⟫ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Γ' Δ' Δ h; simpa using h
  | cons a M ih =>
    intro Γ Γ' Δ' Δ h
    have h1 : D ⟪M + Γ ; a ::ₘ Γ' ⊢ Δ' ; Δ⟫ :=
      D_rule1 hR (Rule.inL _ _ _ _ a) (D_congr h (by simp [Multiset.cons_add]))
    exact D_congr (ih h1) (by simp [Multiset.cons_add])

/-- Move a multiset of formulas from the right linear zone into the central zone. -/
theorem D_inR_all (M : Multiset Formula) :
    ∀ {Γ Γ' Δ' Δ : Multiset Formula}, D ⟪Γ ; Γ' ⊢ Δ' ; M + Δ⟫ → D ⟪Γ ; Γ' ⊢ M + Δ' ; Δ⟫ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Γ' Δ' Δ h; simpa using h
  | cons a M ih =>
    intro Γ Γ' Δ' Δ h
    have h1 : D ⟪Γ ; Γ' ⊢ a ::ₘ Δ' ; M + Δ⟫ :=
      D_rule1 hR (Rule.inR _ _ _ _ a) (D_congr h (by simp [Multiset.cons_add]))
    exact D_congr (ih h1) (by simp [Multiset.cons_add])

/-- Move a multiset of positive formulas from the central zone to the left linear zone. -/
theorem D_outL_all (M : Multiset Formula) (hM : ∀ P ∈ M, P.pol = .pos) :
    ∀ {Γ Γ' Δ' Δ : Multiset Formula}, D ⟪Γ ; M + Γ' ⊢ Δ' ; Δ⟫ → D ⟪M + Γ ; Γ' ⊢ Δ' ; Δ⟫ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Γ' Δ' Δ h; simpa using h
  | cons a M ih =>
    intro Γ Γ' Δ' Δ h
    have h1 : D ⟪Γ ; M + (a ::ₘ Γ') ⊢ Δ' ; Δ⟫ :=
      D_congr h (by simp [Multiset.cons_add])
    have h2 := ih (fun P hP => hM P (Multiset.mem_cons_of_mem hP)) h1
    exact D_congr (D_rule1 hR (Rule.outL _ _ _ _ a (hM a (Multiset.mem_cons_self _ _))) h2)
      (by simp [Multiset.cons_add])

/-- Move a multiset of negative formulas from the central zone to the right linear zone. -/
theorem D_outR_all (M : Multiset Formula) (hM : ∀ N ∈ M, N.pol = .neg) :
    ∀ {Γ Γ' Δ' Δ : Multiset Formula}, D ⟪Γ ; Γ' ⊢ M + Δ' ; Δ⟫ → D ⟪Γ ; Γ' ⊢ Δ' ; M + Δ⟫ := by
  induction M using Multiset.induction_on with
  | empty => intro Γ Γ' Δ' Δ h; simpa using h
  | cons a M ih =>
    intro Γ Γ' Δ' Δ h
    have h1 : D ⟪Γ ; Γ' ⊢ M + (a ::ₘ Δ') ; Δ⟫ :=
      D_congr h (by simp [Multiset.cons_add])
    have h2 := ih (fun P hP => hM P (Multiset.mem_cons_of_mem hP)) h1
    exact D_congr (D_rule1 hR (Rule.outR _ _ _ _ a (hM a (Multiset.mem_cons_self _ _))) h2)
      (by simp [Multiset.cons_add])

omit hR in
theorem pol_bang_mem {Γ : Multiset Formula} : ∀ P ∈ Γ.map bang, P.pol = .pos := by
  intro P hP; obtain ⟨A, -, rfl⟩ := Multiset.mem_map.1 hP; rfl

omit hR in
theorem pol_quest_mem {Δ : Multiset Formula} : ∀ N ∈ Δ.map quest, N.pol = .neg := by
  intro N hN; obtain ⟨A, -, rfl⟩ := Multiset.mem_map.1 hN; rfl

/-- **Translation of LL into LU** (§4).  An LL derivation of `Γ ⊢ Δ` gives an LU derivation
of `Γ; ⊢ ;Δ` using the rules `R`, provided `R` contains the rules of LU and, if the LL
derivation may use cuts, the cut rules. -/
theorem LL.toLU {b : Bool} (hC : b = true → ∀ ps c, CutRule ps c → R ps c)
    {Γ Δ : Multiset Formula} (h : LL b Γ Δ) : D ⟪Γ ; 0 ⊢ 0 ; Δ⟫ := by
  induction h with
  | ax A => exact D_rule0 hR (Rule.ax A)
  | cut A hb _ _ ih₁ ih₂ =>
    exact .mk _ _ (hC hb _ _ (CutRule.cut _ _ 0 0 _ _ A)) trivial (by simp [ih₁, ih₂])
  | oneR => exact D_rule0 hR Rule.oneR
  | oneL _ ih =>
    exact D_rule1 hR (Rule.outL _ _ _ _ one rfl) (D_rule1 hR (Rule.weakL _ _ _ _ one) ih)
  | botL => exact D_rule0 hR Rule.botL
  | botR _ ih =>
    exact D_rule1 hR (Rule.outR _ _ _ _ bot rfl) (D_rule1 hR (Rule.weakR _ _ _ _ bot) ih)
  | topR Γ Δ => exact D_rule0 hR (Rule.topR Γ Δ)
  | zeroL Γ Δ => exact D_rule0 hR (Rule.zeroL Γ Δ)
  | tensorR _ _ ih₁ ih₂ => exact D_rule2 hR (Rule.tensorR _ _ _ _ _ _ _ _) ih₁ ih₂
  | tensorL _ ih => exact D_rule1 hR (Rule.tensorL _ _ _ _ _ _) ih
  | parR _ ih => exact D_rule1 hR (Rule.parR _ _ _ _ _ _) ih
  | parL _ _ ih₁ ih₂ => exact D_rule2 hR (Rule.parL _ _ _ _ _ _ _ _) ih₁ ih₂
  | lolliR _ ih => exact D_rule1 hR (Rule.lolliR _ _ _ _ _ _) ih
  | lolliL _ _ ih₁ ih₂ => exact D_rule2 hR (Rule.lolliL _ _ _ _ _ _ _ _) ih₁ ih₂
  | withR _ _ ih₁ ih₂ => exact D_rule2 hR (Rule.withR _ _ _ _ _ _) ih₁ ih₂
  | withL₁ B _ ih => exact D_rule1 hR (Rule.withL₁ _ _ _ _ _ B) ih
  | withL₂ A _ ih => exact D_rule1 hR (Rule.withL₂ _ _ _ _ A _) ih
  | plusR₁ B _ ih => exact D_rule1 hR (Rule.plusR₁ _ _ _ _ _ B) ih
  | plusR₂ A _ ih => exact D_rule1 hR (Rule.plusR₂ _ _ _ _ A _) ih
  | plusL _ _ ih₁ ih₂ => exact D_rule2 hR (Rule.plusL _ _ _ _ _ _) ih₁ ih₂
  | negL _ ih => exact D_rule1 hR (Rule.negL _ _ _ _ _) ih
  | negR _ ih => exact D_rule1 hR (Rule.negR _ _ _ _ _) ih
  | @bangR Γ Δ A _ ih =>
    -- `!Γ; ⊢ ;?Δ, A` ⟶ `;!Γ ⊢ ?Δ;A` ⟶ `;!Γ ⊢ ?Δ;!A` ⟶ `!Γ; ⊢ ;?Δ, !A`
    have h1 : D ⟪0 ; Γ.map bang ⊢ 0 ; A ::ₘ Δ.map quest⟫ :=
      D_congr (D_inL_all hR (Γ.map bang) (Γ := 0) (Γ' := 0) (Δ' := 0)
        (Δ := A ::ₘ Δ.map quest) (D_congr ih (by simp))) (by simp)
    have h2 : D ⟪0 ; Γ.map bang ⊢ Δ.map quest ; {A}⟫ :=
      D_congr (D_inR_all hR (Δ.map quest) (Γ := 0) (Γ' := Γ.map bang) (Δ' := 0) (Δ := {A})
        (D_congr h1 (by simp [← Multiset.singleton_add, add_comm]))) (by simp)
    have h3 := D_rule1 hR (Rule.bangR _ _ A) h2
    have h4 : D ⟪0 ; Γ.map bang ⊢ 0 ; Δ.map quest + {bang A}⟫ :=
      D_outR_all hR _ pol_quest_mem (D_congr h3 (by simp))
    have h5 := D_outL_all hR _ (pol_bang_mem (Γ := Γ)) (Γ := 0) (Γ' := 0) (Δ' := 0)
      (Δ := Δ.map quest + {bang A}) (D_congr h4 (by simp))
    exact D_congr h5 (by simp [← Multiset.singleton_add, add_comm])
  | bangD _ ih => exact D_rule1 hR (Rule.bangL _ _ _ _ _) (D_rule1 hR (Rule.inL _ _ _ _ _) ih)
  | bangW A _ ih => exact D_rule1 hR (Rule.bangL _ _ _ _ _) (D_rule1 hR (Rule.weakL _ _ _ _ A) ih)
  | @bangC Γ Δ A _ ih =>
    have h1 := D_rule1 hR (Rule.inL _ _ _ _ _) (D_rule1 hR (Rule.inL _ _ _ _ _) ih)
    exact D_rule1 hR (Rule.outL _ _ _ _ (bang A) rfl) (D_rule1 hR (Rule.contrL _ _ _ _ _) h1)
  | @questL Γ Δ A _ ih =>
    have h1 : D ⟪{A} ; Γ.map bang ⊢ 0 ; Δ.map quest⟫ :=
      D_congr (D_inL_all hR (Γ.map bang) (Γ := {A}) (Γ' := 0) (Δ' := 0) (Δ := Δ.map quest)
        (D_congr ih (by simp [← Multiset.singleton_add, add_comm]))) (by simp)
    have h2 : D ⟪{A} ; Γ.map bang ⊢ Δ.map quest ; 0⟫ :=
      D_congr (D_inR_all hR (Δ.map quest) (Γ := {A}) (Γ' := Γ.map bang) (Δ' := 0) (Δ := 0) (D_congr h1 (by simp))) (by simp)
    have h3 := D_rule1 hR (Rule.questL _ _ A) h2
    have h4 : D ⟪{quest A} ; Γ.map bang ⊢ 0 ; Δ.map quest + 0⟫ :=
      D_outR_all hR _ pol_quest_mem (D_congr h3 (by simp))
    have h5 := D_outL_all hR _ (pol_bang_mem (Γ := Γ)) (Γ := {quest A}) (Γ' := 0) (Δ' := 0)
      (Δ := Δ.map quest) (D_congr h4 (by simp))
    exact D_congr h5 (by simp [← Multiset.singleton_add, add_comm])
  | questD _ ih => exact D_rule1 hR (Rule.questR _ _ _ _ _) (D_rule1 hR (Rule.inR _ _ _ _ _) ih)
  | questW A _ ih =>
    exact D_rule1 hR (Rule.questR _ _ _ _ _) (D_rule1 hR (Rule.weakR _ _ _ _ A) ih)
  | @questC Γ Δ A _ ih =>
    have h1 := D_rule1 hR (Rule.inR _ _ _ _ _) (D_rule1 hR (Rule.inR _ _ _ _ _) ih)
    exact D_rule1 hR (Rule.outR _ _ _ _ (quest A) rfl) (D_rule1 hR (Rule.contrR _ _ _ _ _) h1)
  | lallR _ ih => exact D_rule1 hR (Rule.lallR _ _ _ _ _) (D_congr ih (by simp))
  | lallL t _ ih => exact D_rule1 hR (Rule.lallL _ _ _ _ _ t) ih
  | lexR t _ ih => exact D_rule1 hR (Rule.lexR _ _ _ _ _ t) ih
  | lexL _ ih => exact D_rule1 hR (Rule.lexL _ _ _ _ _) (D_congr ih (by simp))

end ToLU

/-- §4: a sequent `Γ ⊢ Δ` provable in linear logic (with cut) is provable in LU as
`Γ; ⊢ ;Δ`. -/
theorem LL.provable {Γ Δ : Multiset Formula} (h : LL true Γ Δ) : Provable ⟪Γ ; 0 ⊢ 0 ; Δ⟫ :=
  LL.toLU (fun _ _ h => Or.inl h) (fun _ _ _ h => Or.inr h) h

/-- §4: a sequent `Γ ⊢ Δ` with a cut-free proof in linear logic has a cut-free proof in LU
as `Γ; ⊢ ;Δ` ("it is easy to translate proof to proof"). -/
theorem LL.cutFreeProvable {Γ Δ : Multiset Formula} (h : LL false Γ Δ) :
    CutFreeProvable ⟪Γ ; 0 ⊢ 0 ; Δ⟫ :=
  LL.toLU (fun _ _ h => h) (fun h => absurd h Bool.false_ne_true) h

end LU
