module

public import RequestProject.LU.FragmentSyntax

/-!
# Intuitionistic, neutral intuitionistic and linear fragments, correct by construction

Continuation of `FragmentSyntax.lean` (which treats the classical fragment) for the other
three fragments of §6:

* `IntFormula PS TS n c`: intuitionistic formulas, which are never negative, so that their
  polarity is an `IPol` (`pos` / `neu`); atoms are taken from the positive and neutral slices
  of the signature.  `IntSequent` is the type of sequents `Γ;Γ' ⊢ ;A`.
* `NFormula PS TS n`: neutral intuitionistic formulas, all of them neutral; atoms are taken
  from the neutral slice of the signature.  `NIntSequent` is the type of sequents `Γ;Γ' ⊢ ;A`
  with at most one formula in `Γ` (an `Option`).
* `LinFormula PS TS n q`: linear formulas of polarity `q`; the constructors compute the
  polarity by Table 1.  `LinSequent` is the type of sequents made of linear formulas.

For each fragment, `range_toSequent` shows that the image of the embedding is exactly the
predicate on sequents used in `Fragments.lean` (`IntSeq`, `NeutralIntSeq`, `LinearSeq`).
-/

@[expose] public section

namespace LU

variable {PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-! ## The intuitionistic fragment -/

/-- The polarity of an intuitionistic formula: intuitionistic formulas are never negative. -/
inductive IPol where
  | pos
  | neu
  deriving DecidableEq, Repr, Fintype

namespace IPol

/-- An intuitionistic polarity as a polarity. -/
def toPol : IPol → Pol
  | pos => .pos
  | neu => .neu

theorem toPol_injective : Function.Injective toPol := by
  intro a b h; cases a <;> cases b <;> simp_all [toPol]

/-- Table 2 for `∧`, restricted to non-negative arguments. -/
def conj : IPol → IPol → IPol
  | neu, neu => neu
  | _, _ => pos

@[simp] theorem toPol_conj (c d : IPol) : (conj c d).toPol = Pol.conj c.toPol d.toPol := by
  cases c <;> cases d <;> rfl

end IPol

/-- Intuitionistic formulas of polarity `c` (§6, fragment 2): positive and neutral atoms,
`1`, `0`, closed under `∧, ∨, ⊃, ⋀x, ∃x`. -/
inductive IntFormula (PS : PredSig) (TS : TermSig) : ℕ → IPol → Type where
  /-- an atom, whose symbol has polarity `c` -/
  | atom {n : ℕ} {c : IPol} (p : PS.PredOf c.toPol) (ts : Tms TS n (PS.arity p.1)) :
      IntFormula PS TS n c
  /-- `1` (`V`) -/
  | one {n : ℕ} : IntFormula PS TS n .pos
  /-- `0` (`F`) -/
  | zero {n : ℕ} : IntFormula PS TS n .pos
  /-- `A ∧ B` -/
  | conj {n : ℕ} {c d : IPol} : IntFormula PS TS n c → IntFormula PS TS n d →
      IntFormula PS TS n (IPol.conj c d)
  /-- `A ∨ B` (always positive on non-negative arguments) -/
  | disj {n : ℕ} {c d : IPol} : IntFormula PS TS n c → IntFormula PS TS n d →
      IntFormula PS TS n .pos
  /-- `A ⊃ B` (always neutral on a non-negative conclusion) -/
  | iimp {n : ℕ} {c d : IPol} : IntFormula PS TS n c → IntFormula PS TS n d →
      IntFormula PS TS n .neu
  /-- `⋀x A` (always neutral on a non-negative body) -/
  | lall {n : ℕ} {c : IPol} : IntFormula PS TS (n + 1) c → IntFormula PS TS n .neu
  /-- `∃x A` (always positive) -/
  | cex {n : ℕ} {c : IPol} : IntFormula PS TS (n + 1) c → IntFormula PS TS n .pos

namespace IntFormula

/-- The embedding of intuitionistic formulas into the formulas of LU. -/
def toFormula : {n : ℕ} → {c : IPol} → IntFormula PS TS n c → Formula PS TS n
  | _, _, atom p ts => .atom p.1 ts
  | _, _, one => .one
  | _, _, zero => .zero
  | _, _, conj A B => .conj A.toFormula B.toFormula
  | _, _, disj A B => .disj A.toFormula B.toFormula
  | _, _, iimp A B => .iimp A.toFormula B.toFormula
  | _, _, lall A => .lall A.toFormula
  | _, _, cex A => .cex A.toFormula

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-- **Polarity by construction**: the polarity of the embedded formula is the index. -/
@[simp] theorem pol_toFormula {n : ℕ} {c : IPol} (A : IntFormula PS TS n c) :
    A.toFormula.pol = c.toPol := by
  induction A with
  | atom p ts => exact p.2
  | @disj _ c d A B ihA ihB =>
    simp only [toFormula, Formula.pol, ihA, ihB]; cases c <;> cases d <;> rfl
  | @iimp _ c d A B ihA ihB =>
    simp only [toFormula, Formula.pol, ihA, ihB]; cases c <;> cases d <;> rfl
  | @lall _ c A ih => simp only [toFormula, Formula.pol, ih]; cases c <;> rfl
  | _ => simp_all [toFormula, Formula.pol] <;> rfl

/-- The embedded formula is intuitionistic. -/
theorem isIntuitionistic_toFormula {n : ℕ} {c : IPol} (A : IntFormula PS TS n c) :
    A.toFormula.IsIntuitionistic := by
  induction A with
  | @atom _ c p ts =>
    show PS.predPol p.1 ≠ .neg
    rw [p.2]; cases c <;> simp [IPol.toPol]
  | _ => simp_all [toFormula, Formula.IsIntuitionistic]

/-- Every intuitionistic formula is the embedding of an `IntFormula`. -/
theorem exists_of_isIntuitionistic {n : ℕ} (A : Formula PS TS n) (h : A.IsIntuitionistic) :
    ∃ (c : IPol) (B : IntFormula PS TS n c), B.toFormula = A := by
  induction A with
  | atom p ts =>
    have hp : PS.predPol p ≠ .neg := h
    rcases hq : PS.predPol p with _ | _ | _
    · exact ⟨.pos, atom ⟨p, hq⟩ ts, rfl⟩
    · exact ⟨.neu, atom ⟨p, hq⟩ ts, rfl⟩
    · exact absurd hq hp
  | one => exact ⟨_, one, rfl⟩
  | zero => exact ⟨_, zero, rfl⟩
  | conj A A' ih ih' =>
    obtain ⟨c, B, rfl⟩ := ih h.1
    obtain ⟨c', B', rfl⟩ := ih' h.2
    exact ⟨_, conj B B', rfl⟩
  | disj A A' ih ih' =>
    obtain ⟨c, B, rfl⟩ := ih h.1
    obtain ⟨c', B', rfl⟩ := ih' h.2
    exact ⟨_, disj B B', rfl⟩
  | iimp A A' ih ih' =>
    obtain ⟨c, B, rfl⟩ := ih h.1
    obtain ⟨c', B', rfl⟩ := ih' h.2
    exact ⟨_, iimp B B', rfl⟩
  | lall A ih =>
    obtain ⟨c, B, rfl⟩ := ih h
    exact ⟨_, lall B, rfl⟩
  | cex A ih =>
    obtain ⟨c, B, rfl⟩ := ih h
    exact ⟨_, cex B, rfl⟩
  | _ => exact h.elim

/-- The intuitionistic formulas are exactly the embeddings of `IntFormula`s. -/
theorem isIntuitionistic_iff {n : ℕ} (A : Formula PS TS n) :
    A.IsIntuitionistic ↔ ∃ (c : IPol) (B : IntFormula PS TS n c), B.toFormula = A :=
  ⟨exists_of_isIntuitionistic A, fun ⟨_, B, hB⟩ => hB ▸ isIntuitionistic_toFormula B⟩

end IntFormula

/-- Intuitionistic formulas of any polarity. -/
abbrev IntF (PS : PredSig) (TS : TermSig) (n : ℕ) : Type := Σ c : IPol, IntFormula PS TS n c

/-- Intuitionistic sequents `Γ;Γ' ⊢ ;A`, correct by construction: there is no right central
zone, and exactly one formula on the right. -/
structure IntSequent (PS : PredSig) (TS : TermSig) (n : ℕ) where
  /-- `Γ` -/
  L : Multiset (IntF PS TS n)
  /-- `Γ'` -/
  CL : Finset (IntF PS TS n)
  /-- `A` -/
  goal : IntF PS TS n

/-- The LU sequent of an intuitionistic sequent. -/
def IntSequent.toSequent {n : ℕ} (S : IntSequent PS TS n) : Sequent PS TS n :=
  ⟪S.L.map (fun A => A.2.toFormula) ; S.CL.image (fun A => A.2.toFormula) ⊢ ∅ ;
    {S.goal.2.toFormula}⟫

/-- **The intuitionistic sequents are exactly the `IntSequent`s.** -/
theorem IntSequent.range_toSequent {n : ℕ} (S : Sequent PS TS n) :
    IntSeq S ↔ ∃ T : IntSequent PS TS n, T.toSequent = S := by
  constructor
  · obtain ⟨L, CL, CR, R⟩ := S
    rintro ⟨hall, hCR, hR⟩
    simp only [AllIn, Sequent.formulas, Multiset.mem_add, Finset.mem_val] at hall
    simp only at hCR hR
    subst hCR
    obtain ⟨A, rfl⟩ := Multiset.card_eq_one.1 hR
    have lift : ∀ B, B.IsIntuitionistic → ∃ B' : IntF PS TS n, B'.2.toFormula = B :=
      fun B hB => by
        obtain ⟨c, B', hB'⟩ := IntFormula.exists_of_isIntuitionistic B hB
        exact ⟨⟨c, B'⟩, hB'⟩
    obtain ⟨L', hL⟩ := multiset_exists_map_eq (fun B : IntF PS TS n => B.2.toFormula) L
      (fun B hB => lift B (hall B (by simp [hB])))
    obtain ⟨CL', hCL⟩ := finset_exists_image_eq (fun B : IntF PS TS n => B.2.toFormula) CL
      (fun B hB => lift B (hall B (by simp [hB])))
    obtain ⟨A', hA⟩ := lift A (hall A (by simp))
    exact ⟨⟨L', CL', A'⟩, by simp [toSequent, hL, hCL, hA]⟩
  · rintro ⟨⟨L, CL, A⟩, rfl⟩
    refine ⟨fun B hB => ?_, rfl, by simp [toSequent]⟩
    simp only [toSequent, Sequent.formulas, Multiset.mem_add, Finset.mem_val,
      Finset.mem_image, Multiset.mem_map, Finset.empty_val, Multiset.notMem_zero,
      Multiset.mem_singleton, or_false] at hB
    rcases hB with (⟨B, -, rfl⟩ | ⟨B, -, rfl⟩) | rfl <;>
      exact IntFormula.isIntuitionistic_toFormula _

/-! ## The neutral intuitionistic fragment -/

/-- Neutral intuitionistic formulas (§6, fragment 3): neutral atoms, closed under
`∧, ⊃, ⋀x`.  They are all neutral, so no polarity index is needed. -/
inductive NFormula (PS : PredSig) (TS : TermSig) : ℕ → Type where
  /-- an atom, whose symbol is neutral -/
  | atom {n : ℕ} (p : PS.PredOf .neu) (ts : Tms TS n (PS.arity p.1)) : NFormula PS TS n
  /-- `A ∧ B` -/
  | conj {n : ℕ} : NFormula PS TS n → NFormula PS TS n → NFormula PS TS n
  /-- `A ⊃ B` -/
  | iimp {n : ℕ} : NFormula PS TS n → NFormula PS TS n → NFormula PS TS n
  /-- `⋀x A` -/
  | lall {n : ℕ} : NFormula PS TS (n + 1) → NFormula PS TS n

namespace NFormula

/-- The embedding of neutral intuitionistic formulas into the formulas of LU. -/
def toFormula : {n : ℕ} → NFormula PS TS n → Formula PS TS n
  | _, atom p ts => .atom p.1 ts
  | _, conj A B => .conj A.toFormula B.toFormula
  | _, iimp A B => .iimp A.toFormula B.toFormula
  | _, lall A => .lall A.toFormula

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-- **Polarity by construction**: every neutral intuitionistic formula is neutral. -/
@[simp] theorem pol_toFormula {n : ℕ} (A : NFormula PS TS n) : A.toFormula.pol = .neu := by
  induction A with
  | atom p ts => exact p.2
  | _ => simp_all [toFormula, Formula.pol]; rfl

/-- The embedded formula is neutral intuitionistic. -/
theorem isNeutralInt_toFormula {n : ℕ} (A : NFormula PS TS n) : A.toFormula.IsNeutralInt := by
  induction A with
  | atom p ts => exact p.2
  | _ => simp_all [toFormula, Formula.IsNeutralInt]

/-- Every neutral intuitionistic formula is the embedding of an `NFormula`. -/
theorem exists_of_isNeutralInt {n : ℕ} (A : Formula PS TS n) (h : A.IsNeutralInt) :
    ∃ B : NFormula PS TS n, B.toFormula = A := by
  induction A with
  | atom p ts => exact ⟨atom ⟨p, h⟩ ts, rfl⟩
  | conj A A' ih ih' =>
    obtain ⟨B, rfl⟩ := ih h.1
    obtain ⟨B', rfl⟩ := ih' h.2
    exact ⟨conj B B', rfl⟩
  | iimp A A' ih ih' =>
    obtain ⟨B, rfl⟩ := ih h.1
    obtain ⟨B', rfl⟩ := ih' h.2
    exact ⟨iimp B B', rfl⟩
  | lall A ih =>
    obtain ⟨B, rfl⟩ := ih h
    exact ⟨lall B, rfl⟩
  | _ => exact h.elim

/-- The neutral intuitionistic formulas are exactly the embeddings of `NFormula`s. -/
theorem isNeutralInt_iff {n : ℕ} (A : Formula PS TS n) :
    A.IsNeutralInt ↔ ∃ B : NFormula PS TS n, B.toFormula = A :=
  ⟨exists_of_isNeutralInt A, fun ⟨B, hB⟩ => hB ▸ isNeutralInt_toFormula B⟩

/-- The embedding is injective. -/
theorem toFormula_injective {n : ℕ} :
    Function.Injective (toFormula : NFormula PS TS n → Formula PS TS n) := by
  intro A B h
  induction A with
  | atom p ts =>
    cases B with
    | atom q us =>
      simp only [toFormula, Formula.atom.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨p, hp⟩ := p
      obtain ⟨q, hq⟩ := q
      subst h1
      cases eq_of_heq h2
      rfl
    | _ => simp [toFormula] at h
  | conj A A' ih ih' =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.conj.injEq] at h
    rw [ih h.1, ih' h.2]
  | iimp A A' ih ih' =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.iimp.injEq] at h
    rw [ih h.1, ih' h.2]
  | lall A ih =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.lall.injEq] at h
    rw [ih h]

end NFormula

/-- Neutral intuitionistic sequents `Γ;Γ' ⊢ ;A` with at most one formula in `Γ`, correct by
construction (`Γ` is an `Option`). -/
structure NIntSequent (PS : PredSig) (TS : TermSig) (n : ℕ) where
  /-- `Γ`: at most one formula -/
  L : Option (NFormula PS TS n)
  /-- `Γ'` -/
  CL : Finset (NFormula PS TS n)
  /-- `A` -/
  goal : NFormula PS TS n

/-- The LU sequent of a neutral intuitionistic sequent. -/
def NIntSequent.toSequent {n : ℕ} (S : NIntSequent PS TS n) : Sequent PS TS n :=
  ⟪S.L.elim 0 (fun A => {A.toFormula}) ; S.CL.image NFormula.toFormula ⊢ ∅ ;
    {S.goal.toFormula}⟫

/-- **The neutral intuitionistic sequents are exactly the `NIntSequent`s.** -/
theorem NIntSequent.range_toSequent {n : ℕ} (S : Sequent PS TS n) :
    NeutralIntSeq S ↔ ∃ T : NIntSequent PS TS n, T.toSequent = S := by
  constructor
  · obtain ⟨L, CL, CR, R⟩ := S
    rintro ⟨hall, hCR, hR, hL⟩
    simp only [AllIn, Sequent.formulas, Multiset.mem_add, Finset.mem_val] at hall
    simp only at hCR hR hL
    subst hCR
    obtain ⟨A, rfl⟩ := Multiset.card_eq_one.1 hR
    obtain ⟨CL', hCL⟩ := finset_exists_image_eq NFormula.toFormula CL
      (fun B hB => NFormula.exists_of_isNeutralInt B (hall B (by simp [hB])))
    obtain ⟨A', hA⟩ := NFormula.exists_of_isNeutralInt A (hall A (by simp))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hL with h0 | h1
    · obtain rfl := Multiset.card_eq_zero.1 h0
      exact ⟨⟨none, CL', A'⟩, by simp [toSequent, hCL, hA]⟩
    · obtain ⟨B, rfl⟩ := Multiset.card_eq_one.1 h1
      obtain ⟨B', hB⟩ := NFormula.exists_of_isNeutralInt B (hall B (by simp))
      exact ⟨⟨some B', CL', A'⟩, by simp [toSequent, hCL, hA, hB]⟩
  · rintro ⟨⟨L, CL, A⟩, rfl⟩
    refine ⟨fun B hB => ?_, rfl, by simp [toSequent], by cases L <;> simp [toSequent]⟩
    simp only [toSequent, Sequent.formulas, Multiset.mem_add, Finset.mem_val,
      Finset.mem_image, Finset.empty_val, Multiset.notMem_zero,
      Multiset.mem_singleton, or_false] at hB
    rcases hB with (hB | ⟨B, -, rfl⟩) | rfl
    · cases L with
      | none => simp at hB
      | some C =>
        simp only [Option.elim, Multiset.mem_singleton] at hB
        exact hB ▸ NFormula.isNeutralInt_toFormula C
    all_goals exact NFormula.isNeutralInt_toFormula _

/-! ## The linear fragment -/

/-- Linear formulas of polarity `q` (§6, fragment 4): all atoms, the constants
`1, 0, ⊥, ⊤`, closed under `(·)⊥, ⊗, ⅋, ⊸, ⊕, &, !, ?, ⋀x, ⋁x`.  The polarity is part of the
type and is computed by the constructors following Table 1. -/
inductive LinFormula (PS : PredSig) (TS : TermSig) : ℕ → Pol → Type where
  /-- an atom; its polarity is that of its symbol -/
  | atom {n : ℕ} (p : PS.Pred) (ts : Tms TS n (PS.arity p)) : LinFormula PS TS n (PS.predPol p)
  /-- `1` -/
  | one {n : ℕ} : LinFormula PS TS n .pos
  /-- `0` -/
  | zero {n : ℕ} : LinFormula PS TS n .pos
  /-- `⊥` -/
  | bot {n : ℕ} : LinFormula PS TS n .neg
  /-- `⊤` -/
  | top {n : ℕ} : LinFormula PS TS n .neg
  /-- `A⊥` -/
  | neg {n : ℕ} {q : Pol} : LinFormula PS TS n q → LinFormula PS TS n q.dual
  /-- `!A` -/
  | bang {n : ℕ} {q : Pol} : LinFormula PS TS n q → LinFormula PS TS n .pos
  /-- `?A` -/
  | quest {n : ℕ} {q : Pol} : LinFormula PS TS n q → LinFormula PS TS n .neg
  /-- `A ⊗ B` -/
  | tensor {n : ℕ} {q r : Pol} : LinFormula PS TS n q → LinFormula PS TS n r →
      LinFormula PS TS n (Pol.tensor q r)
  /-- `A ⅋ B` -/
  | par {n : ℕ} {q r : Pol} : LinFormula PS TS n q → LinFormula PS TS n r →
      LinFormula PS TS n (Pol.par q r)
  /-- `A ⊸ B` -/
  | lolli {n : ℕ} {q r : Pol} : LinFormula PS TS n q → LinFormula PS TS n r →
      LinFormula PS TS n (Pol.lolli q r)
  /-- `A & B` -/
  | with_ {n : ℕ} {q r : Pol} : LinFormula PS TS n q → LinFormula PS TS n r →
      LinFormula PS TS n (Pol.with_ q r)
  /-- `A ⊕ B` -/
  | plus {n : ℕ} {q r : Pol} : LinFormula PS TS n q → LinFormula PS TS n r →
      LinFormula PS TS n (Pol.plus q r)
  /-- `⋀x A` -/
  | lall {n : ℕ} {q : Pol} : LinFormula PS TS (n + 1) q → LinFormula PS TS n (Pol.lall q)
  /-- `⋁x A` -/
  | lex {n : ℕ} {q : Pol} : LinFormula PS TS (n + 1) q → LinFormula PS TS n (Pol.lex q)

namespace LinFormula

/-- The embedding of linear formulas into the formulas of LU. -/
def toFormula : {n : ℕ} → {q : Pol} → LinFormula PS TS n q → Formula PS TS n
  | _, _, atom p ts => .atom p ts
  | _, _, one => .one
  | _, _, zero => .zero
  | _, _, bot => .bot
  | _, _, top => .top
  | _, _, neg A => .neg A.toFormula
  | _, _, bang A => .bang A.toFormula
  | _, _, quest A => .quest A.toFormula
  | _, _, tensor A B => .tensor A.toFormula B.toFormula
  | _, _, par A B => .par A.toFormula B.toFormula
  | _, _, lolli A B => .lolli A.toFormula B.toFormula
  | _, _, with_ A B => .with_ A.toFormula B.toFormula
  | _, _, plus A B => .plus A.toFormula B.toFormula
  | _, _, lall A => .lall A.toFormula
  | _, _, lex A => .lex A.toFormula

/-- Substitution in a linear formula; its type says that it preserves the polarity. -/
def subst : {n m : ℕ} → {q : Pol} → LinFormula PS TS n q → Subst TS n m → LinFormula PS TS m q
  | _, _, _, atom p ts, σ => atom p (ts.subst σ)
  | _, _, _, one, _ => one
  | _, _, _, zero, _ => zero
  | _, _, _, bot, _ => bot
  | _, _, _, top, _ => top
  | _, _, _, neg A, σ => neg (A.subst σ)
  | _, _, _, bang A, σ => bang (A.subst σ)
  | _, _, _, quest A, σ => quest (A.subst σ)
  | _, _, _, tensor A B, σ => tensor (A.subst σ) (B.subst σ)
  | _, _, _, par A B, σ => par (A.subst σ) (B.subst σ)
  | _, _, _, lolli A B, σ => lolli (A.subst σ) (B.subst σ)
  | _, _, _, with_ A B, σ => with_ (A.subst σ) (B.subst σ)
  | _, _, _, plus A B, σ => plus (A.subst σ) (B.subst σ)
  | _, _, _, lall A, σ => lall (A.subst (Subst.lift σ))
  | _, _, _, lex A, σ => lex (A.subst (Subst.lift σ))

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-- **Polarity by construction**: the polarity of the embedded formula is the index. -/
@[simp] theorem pol_toFormula {n : ℕ} {q : Pol} (A : LinFormula PS TS n q) :
    A.toFormula.pol = q := by
  induction A <;> simp_all [toFormula, Formula.pol]

/-- Substitution commutes with the embedding. -/
theorem toFormula_subst {n m : ℕ} {q : Pol} (A : LinFormula PS TS n q) (σ : Subst TS n m) :
    (A.subst σ).toFormula = A.toFormula.subst σ := by
  induction A generalizing m <;> simp_all [subst, toFormula, Formula.subst]

/-- The embedded formula is linear. -/
theorem isLinear_toFormula {n : ℕ} {q : Pol} (A : LinFormula PS TS n q) :
    A.toFormula.IsLinear := by
  induction A <;> simp_all [toFormula, Formula.IsLinear]

/-- Every linear formula is the embedding of a `LinFormula`. -/
theorem exists_of_isLinear {n : ℕ} (A : Formula PS TS n) (h : A.IsLinear) :
    ∃ (q : Pol) (B : LinFormula PS TS n q), B.toFormula = A := by
  induction A with
  | atom p ts => exact ⟨_, atom p ts, rfl⟩
  | one => exact ⟨_, one, rfl⟩
  | zero => exact ⟨_, zero, rfl⟩
  | bot => exact ⟨_, bot, rfl⟩
  | top => exact ⟨_, top, rfl⟩
  | neg A ih =>
    obtain ⟨_, B, rfl⟩ := ih h
    exact ⟨_, neg B, rfl⟩
  | bang A ih =>
    obtain ⟨_, B, rfl⟩ := ih h
    exact ⟨_, bang B, rfl⟩
  | quest A ih =>
    obtain ⟨_, B, rfl⟩ := ih h
    exact ⟨_, quest B, rfl⟩
  | tensor A A' ih ih' =>
    obtain ⟨_, B, rfl⟩ := ih h.1
    obtain ⟨_, B', rfl⟩ := ih' h.2
    exact ⟨_, tensor B B', rfl⟩
  | par A A' ih ih' =>
    obtain ⟨_, B, rfl⟩ := ih h.1
    obtain ⟨_, B', rfl⟩ := ih' h.2
    exact ⟨_, par B B', rfl⟩
  | lolli A A' ih ih' =>
    obtain ⟨_, B, rfl⟩ := ih h.1
    obtain ⟨_, B', rfl⟩ := ih' h.2
    exact ⟨_, lolli B B', rfl⟩
  | with_ A A' ih ih' =>
    obtain ⟨_, B, rfl⟩ := ih h.1
    obtain ⟨_, B', rfl⟩ := ih' h.2
    exact ⟨_, with_ B B', rfl⟩
  | plus A A' ih ih' =>
    obtain ⟨_, B, rfl⟩ := ih h.1
    obtain ⟨_, B', rfl⟩ := ih' h.2
    exact ⟨_, plus B B', rfl⟩
  | lall A ih =>
    obtain ⟨_, B, rfl⟩ := ih h
    exact ⟨_, lall B, rfl⟩
  | lex A ih =>
    obtain ⟨_, B, rfl⟩ := ih h
    exact ⟨_, lex B, rfl⟩
  | _ => exact h.elim

/-- The linear formulas are exactly the embeddings of `LinFormula`s. -/
theorem isLinear_iff {n : ℕ} (A : Formula PS TS n) :
    A.IsLinear ↔ ∃ (q : Pol) (B : LinFormula PS TS n q), B.toFormula = A :=
  ⟨exists_of_isLinear A, fun ⟨_, B, hB⟩ => hB ▸ isLinear_toFormula B⟩

/-- A linear formula is the embedding of a `LinFormula` whose index is its polarity. -/
theorem exists_of_isLinear_pol {n : ℕ} (A : Formula PS TS n) (h : A.IsLinear) :
    ∃ B : LinFormula PS TS n A.pol, B.toFormula = A := by
  obtain ⟨q, B, rfl⟩ := exists_of_isLinear A h
  have key : ∀ q' (_ : q = q'), ∃ B' : LinFormula PS TS n q', B'.toFormula = B.toFormula := by
    rintro _ rfl; exact ⟨B, rfl⟩
  exact key _ (pol_toFormula B).symm

end LinFormula

/-- Linear formulas of any polarity. -/
abbrev LinF (PS : PredSig) (TS : TermSig) (n : ℕ) : Type := Σ q : Pol, LinFormula PS TS n q

/-- Linear sequents, correct by construction: all four zones contain linear formulas. -/
structure LinSequent (PS : PredSig) (TS : TermSig) (n : ℕ) where
  /-- `Γ` -/
  L : Multiset (LinF PS TS n)
  /-- `Γ'` -/
  CL : Finset (LinF PS TS n)
  /-- `Δ'` -/
  CR : Finset (LinF PS TS n)
  /-- `Δ` -/
  R : Multiset (LinF PS TS n)

/-- The LU sequent of a linear sequent. -/
def LinSequent.toSequent {n : ℕ} (S : LinSequent PS TS n) : Sequent PS TS n :=
  ⟪S.L.map (fun A => A.2.toFormula) ; S.CL.image (fun A => A.2.toFormula) ⊢
    S.CR.image (fun A => A.2.toFormula) ; S.R.map (fun A => A.2.toFormula)⟫

/-- **The linear sequents are exactly the `LinSequent`s.** -/
theorem LinSequent.range_toSequent {n : ℕ} (S : Sequent PS TS n) :
    LinearSeq S ↔ ∃ T : LinSequent PS TS n, T.toSequent = S := by
  have lift : ∀ B : Formula PS TS n, B.IsLinear → ∃ B' : LinF PS TS n, B'.2.toFormula = B :=
    fun B hB => by
      obtain ⟨q, B', hB'⟩ := LinFormula.exists_of_isLinear B hB
      exact ⟨⟨q, B'⟩, hB'⟩
  constructor
  · obtain ⟨L, CL, CR, R⟩ := S
    intro hall
    simp only [LinearSeq, AllIn, Sequent.formulas, Multiset.mem_add, Finset.mem_val] at hall
    obtain ⟨L', hL⟩ := multiset_exists_map_eq (fun B : LinF PS TS n => B.2.toFormula) L
      (fun B hB => lift B (hall B (by simp [hB])))
    obtain ⟨CL', hCL⟩ := finset_exists_image_eq (fun B : LinF PS TS n => B.2.toFormula) CL
      (fun B hB => lift B (hall B (by simp [hB])))
    obtain ⟨CR', hCR⟩ := finset_exists_image_eq (fun B : LinF PS TS n => B.2.toFormula) CR
      (fun B hB => lift B (hall B (by simp [hB])))
    obtain ⟨R', hR⟩ := multiset_exists_map_eq (fun B : LinF PS TS n => B.2.toFormula) R
      (fun B hB => lift B (hall B (by simp [hB])))
    exact ⟨⟨L', CL', CR', R'⟩, by simp [toSequent, hL, hCL, hCR, hR]⟩
  · rintro ⟨⟨L, CL, CR, R⟩, rfl⟩ B hB
    simp only [toSequent, Sequent.formulas, Multiset.mem_add, Finset.mem_val,
      Finset.mem_image, Multiset.mem_map] at hB
    rcases hB with ((⟨B, -, rfl⟩ | ⟨B, -, rfl⟩) | ⟨B, -, rfl⟩) | ⟨B, -, rfl⟩ <;>
      exact LinFormula.isLinear_toFormula _

end LU
