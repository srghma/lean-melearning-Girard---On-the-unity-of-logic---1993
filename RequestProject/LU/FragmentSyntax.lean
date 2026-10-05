module

public import RequestProject.LU.Fragments

/-!
# Fragments of LU, correct by construction

In `Fragments.lean` the four fragments of §6 are carved out of the full syntax by
predicates (`Formula.IsClassical`, …, `ClassicalSeq`, `IntSeq`, …).  This file gives the
*intrinsic* counterpart: for each fragment, a separate type of formulas that can only build
formulas of the fragment, and a separate type of sequents that can only build sequents of
the fragment.  Every such object is embedded into the full syntax, and we prove that the
image of the embedding is *exactly* the corresponding predicate of `Fragments.lean`.

* **Polarity-sliced signatures.**  `PS.PredOf q` is the type of the predicate symbols of
  polarity `q`.  An atom of a fragment formula takes its symbol from the slices allowed by the
  fragment, so e.g. a neutral atom simply cannot be written in a classical formula.
* **Polarity in the type.**  Classical formulas are never neutral, so their polarity is a
  `CPol` (`pos` / `neg`), and `ClFormula PS TS n c` is the type of classical formulas of
  polarity `c`; intuitionistic formulas are never negative, so `IntFormula PS TS n c` is
  indexed by an `IPol` (`pos` / `neu`); neutral intuitionistic formulas are all neutral
  (`NFormula`, no index); linear formulas are indexed by the full `Pol` (`LinFormula`).
  The constructors compute the polarity by Tables 1 and 2, and `pol_toFormula` shows that it
  agrees with `Formula.pol`.  Substitution is typed as polarity-preserving.
* **Fragment sequents.**  `ClSequent` is the *stoup* presentation of classical sequents: the
  left linear zone holds only positive formulas, the right linear zone only negative ones, and
  a separate optional slot (`Stoup`) holds the single formula allowed to break this rule
  (a negative formula on the left or a positive one on the right).  This makes the condition
  `μ ≤ 1` hold by construction.

Main result: `ClSequent.range_toSequent`,
`ClassicalSeq S ↔ ∃ T : ClSequent PS TS n, T.toSequent = S`.

The intuitionistic, neutral intuitionistic and linear fragments are treated in the same way
in `FragmentSyntaxInt.lean`.
-/

@[expose] public section

namespace LU

/-! ## Polarity-sliced signatures -/

/-- The predicate symbols of `PS` of a fixed polarity `q`. -/
abbrev PredSig.PredOf (PS : PredSig) (q : Pol) : Type := {p : PS.Pred // PS.predPol p = q}

/-- The sub-signature of the predicate symbols whose polarity satisfies `ok`
(e.g. `PS.restrict (· ≠ .neu)` has no neutral predicate symbol). -/
def PredSig.restrict (PS : PredSig) (ok : Pol → Prop) : PredSig where
  Pred := {p : PS.Pred // ok (PS.predPol p)}
  arity p := PS.arity p.1
  predPol p := PS.predPol p.1

/-- Every predicate symbol of `PS.restrict ok` has a polarity satisfying `ok`. -/
theorem PredSig.restrict_predPol (PS : PredSig) (ok : Pol → Prop) (p : (PS.restrict ok).Pred) :
    ok ((PS.restrict ok).predPol p) := p.2

/-- A signature presented by polarity: a type of predicate symbols for each polarity.
Choosing e.g. `Pred .neu := Empty` gives a signature without neutral predicates. -/
structure PolPredSig where
  /-- the predicate symbols of each polarity -/
  Pred : Pol → Type
  /-- the arity of each predicate symbol -/
  arity : ∀ {q : Pol}, Pred q → ℕ

/-- The ordinary signature of a polarity-presented signature. -/
def PolPredSig.toPredSig (PPS : PolPredSig) : PredSig where
  Pred := Σ q, PPS.Pred q
  arity p := PPS.arity p.2
  predPol p := p.1

/-- In a polarity-presented signature with no symbol of polarity `q`, no atom has
polarity `q`. -/
theorem PolPredSig.predPol_ne (PPS : PolPredSig) {q : Pol} (h : IsEmpty (PPS.Pred q))
    (p : PPS.toPredSig.Pred) : PPS.toPredSig.predPol p ≠ q := by
  rintro rfl; exact h.false p.2

variable {PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-! ## Generic lifting lemmas -/

section Lift

variable {α β : Type*}

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-- A multiset all of whose elements are in the range of `e` is in the range of `map e`. -/
theorem multiset_exists_map_eq (e : α → β) (M : Multiset β) (h : ∀ b ∈ M, ∃ a, e a = b) :
    ∃ M' : Multiset α, M'.map e = M := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨0, rfl⟩
  | cons b M ih =>
    obtain ⟨a, rfl⟩ := h b (Multiset.mem_cons_self _ _)
    obtain ⟨M', hM'⟩ := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    exact ⟨a ::ₘ M', by simp [hM']⟩

/-- A finset all of whose elements are in the range of `e` is in the range of `image e`. -/
theorem finset_exists_image_eq [DecidableEq β] (e : α → β) (s : Finset β)
    (h : ∀ b ∈ s, ∃ a, e a = b) : ∃ s' : Finset α, s'.image e = s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, rfl⟩
  | insert b s _ ih =>
    obtain ⟨a, rfl⟩ := h b (Finset.mem_insert_self _ _)
    obtain ⟨s', hs'⟩ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
    exact ⟨insert a s', by rw [Finset.image_insert, hs']⟩

end Lift

/-! ## The classical fragment -/

/-- The polarity of a classical formula: classical formulas are never neutral. -/
inductive CPol where
  | pos
  | neg
  deriving DecidableEq, Repr, Fintype

namespace CPol

/-- A classical polarity as a polarity. -/
def toPol : CPol → Pol
  | pos => .pos
  | neg => .neg

theorem toPol_injective : Function.Injective toPol := by
  intro a b h; cases a <;> cases b <;> simp_all [toPol]

/-- `(·)⊥` on classical polarities (Table 1). -/
def dual : CPol → CPol
  | pos => neg
  | neg => pos

/-- Table 2 for `∧`, restricted to non-neutral arguments. -/
def conj : CPol → CPol → CPol
  | neg, neg => neg
  | _, _ => pos

/-- Table 2 for `∨`, restricted to non-neutral arguments. -/
def disj : CPol → CPol → CPol
  | pos, pos => pos
  | _, _ => neg

/-- Table 2 for `⇒`, restricted to non-neutral arguments. -/
def imp : CPol → CPol → CPol
  | neg, pos => pos
  | _, _ => neg

@[simp] theorem toPol_dual (c : CPol) : c.dual.toPol = c.toPol.dual := by cases c <;> rfl
@[simp] theorem toPol_conj (c d : CPol) : (conj c d).toPol = Pol.conj c.toPol d.toPol := by
  cases c <;> cases d <;> rfl
@[simp] theorem toPol_disj (c d : CPol) : (disj c d).toPol = Pol.disj c.toPol d.toPol := by
  cases c <;> cases d <;> rfl
@[simp] theorem toPol_imp (c d : CPol) : (imp c d).toPol = Pol.imp c.toPol d.toPol := by
  cases c <;> cases d <;> rfl

end CPol

/-- Classical formulas of polarity `c` (§6, fragment 1): positive and negative atoms, `1`,
`0`, closed under `¬, ∧, ∨, ⇒, ∀x, ∃x`.  The polarity is part of the type. -/
inductive ClFormula (PS : PredSig) (TS : TermSig) : ℕ → CPol → Type where
  /-- an atom, whose symbol has polarity `c` -/
  | atom {n : ℕ} {c : CPol} (p : PS.PredOf c.toPol) (ts : Tms TS n (PS.arity p.1)) :
      ClFormula PS TS n c
  /-- `1` (`V`) -/
  | one {n : ℕ} : ClFormula PS TS n .pos
  /-- `0` (`F`) -/
  | zero {n : ℕ} : ClFormula PS TS n .pos
  /-- `¬A` -/
  | neg {n : ℕ} {c : CPol} : ClFormula PS TS n c → ClFormula PS TS n c.dual
  /-- `A ∧ B` -/
  | conj {n : ℕ} {c d : CPol} : ClFormula PS TS n c → ClFormula PS TS n d →
      ClFormula PS TS n (CPol.conj c d)
  /-- `A ∨ B` -/
  | disj {n : ℕ} {c d : CPol} : ClFormula PS TS n c → ClFormula PS TS n d →
      ClFormula PS TS n (CPol.disj c d)
  /-- `A ⇒ B` -/
  | imp {n : ℕ} {c d : CPol} : ClFormula PS TS n c → ClFormula PS TS n d →
      ClFormula PS TS n (CPol.imp c d)
  /-- `∀x A` (always negative) -/
  | call {n : ℕ} {c : CPol} : ClFormula PS TS (n + 1) c → ClFormula PS TS n .neg
  /-- `∃x A` (always positive) -/
  | cex {n : ℕ} {c : CPol} : ClFormula PS TS (n + 1) c → ClFormula PS TS n .pos

namespace ClFormula

/-- The embedding of classical formulas into the formulas of LU. -/
def toFormula : {n : ℕ} → {c : CPol} → ClFormula PS TS n c → Formula PS TS n
  | _, _, atom p ts => .atom p.1 ts
  | _, _, one => .one
  | _, _, zero => .zero
  | _, _, neg A => .neg A.toFormula
  | _, _, conj A B => .conj A.toFormula B.toFormula
  | _, _, disj A B => .disj A.toFormula B.toFormula
  | _, _, imp A B => .imp A.toFormula B.toFormula
  | _, _, call A => .call A.toFormula
  | _, _, cex A => .cex A.toFormula

omit [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-- **Polarity by construction**: the polarity of the embedded formula is the index. -/
@[simp] theorem pol_toFormula {n : ℕ} {c : CPol} (A : ClFormula PS TS n c) :
    A.toFormula.pol = c.toPol := by
  induction A with
  | atom p ts => exact p.2
  | _ => simp_all [toFormula, Formula.pol] <;> rfl

/-- The embedded formula is classical. -/
theorem isClassical_toFormula {n : ℕ} {c : CPol} (A : ClFormula PS TS n c) :
    A.toFormula.IsClassical := by
  induction A with
  | @atom _ c p ts =>
    show PS.predPol p.1 ≠ .neu
    rw [p.2]; cases c <;> simp [CPol.toPol]
  | _ => simp_all [toFormula, Formula.IsClassical]

/-- Every classical formula is the embedding of a classical formula, of some polarity. -/
theorem exists_of_isClassical {n : ℕ} (A : Formula PS TS n) (h : A.IsClassical) :
    ∃ (c : CPol) (B : ClFormula PS TS n c), B.toFormula = A := by
  induction A with
  | atom p ts =>
    have hp : PS.predPol p ≠ .neu := h
    rcases hq : PS.predPol p with _ | _ | _
    · exact ⟨.pos, atom ⟨p, hq⟩ ts, rfl⟩
    · exact absurd hq hp
    · exact ⟨.neg, atom ⟨p, hq⟩ ts, rfl⟩
  | one => exact ⟨_, one, rfl⟩
  | zero => exact ⟨_, zero, rfl⟩
  | neg A ih =>
    obtain ⟨c, B, rfl⟩ := ih h
    exact ⟨_, neg B, rfl⟩
  | conj A A' ih ih' =>
    obtain ⟨c, B, rfl⟩ := ih h.1
    obtain ⟨c', B', rfl⟩ := ih' h.2
    exact ⟨_, conj B B', rfl⟩
  | disj A A' ih ih' =>
    obtain ⟨c, B, rfl⟩ := ih h.1
    obtain ⟨c', B', rfl⟩ := ih' h.2
    exact ⟨_, disj B B', rfl⟩
  | imp A A' ih ih' =>
    obtain ⟨c, B, rfl⟩ := ih h.1
    obtain ⟨c', B', rfl⟩ := ih' h.2
    exact ⟨_, imp B B', rfl⟩
  | call A ih =>
    obtain ⟨c, B, rfl⟩ := ih h
    exact ⟨_, call B, rfl⟩
  | cex A ih =>
    obtain ⟨c, B, rfl⟩ := ih h
    exact ⟨_, cex B, rfl⟩
  | _ => exact h.elim

/-- The classical formulas are exactly the embeddings of `ClFormula`s. -/
theorem isClassical_iff {n : ℕ} (A : Formula PS TS n) :
    A.IsClassical ↔ ∃ (c : CPol) (B : ClFormula PS TS n c), B.toFormula = A :=
  ⟨exists_of_isClassical A, fun ⟨_, B, hB⟩ => hB ▸ isClassical_toFormula B⟩

/-- A classical formula of polarity `c` is the embedding of a `ClFormula` of index `c`. -/
theorem exists_of_isClassical_pol {n : ℕ} {c : CPol} (A : Formula PS TS n) (h : A.IsClassical)
    (hc : A.pol = c.toPol) : ∃ B : ClFormula PS TS n c, B.toFormula = A := by
  obtain ⟨c', B, rfl⟩ := exists_of_isClassical A h
  obtain rfl : c' = c := CPol.toPol_injective (by rw [← hc, pol_toFormula])
  exact ⟨B, rfl⟩

/-- Substitution in a classical formula; its type says that it preserves the polarity. -/
def subst : {n m : ℕ} → {c : CPol} → ClFormula PS TS n c → Subst TS n m → ClFormula PS TS m c
  | _, _, _, atom p ts, σ => atom p (ts.subst σ)
  | _, _, _, one, _ => one
  | _, _, _, zero, _ => zero
  | _, _, _, neg A, σ => neg (A.subst σ)
  | _, _, _, conj A B, σ => conj (A.subst σ) (B.subst σ)
  | _, _, _, disj A B, σ => disj (A.subst σ) (B.subst σ)
  | _, _, _, imp A B, σ => imp (A.subst σ) (B.subst σ)
  | _, _, _, call A, σ => call (A.subst (Subst.lift σ))
  | _, _, _, cex A, σ => cex (A.subst (Subst.lift σ))

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
/-- Substitution commutes with the embedding. -/
theorem toFormula_subst {n m : ℕ} {c : CPol} (A : ClFormula PS TS n c) (σ : Subst TS n m) :
    (A.subst σ).toFormula = A.toFormula.subst σ := by
  induction A generalizing m <;> simp_all [subst, toFormula, Formula.subst]

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
/-- The embedding is injective (the polarity index included). -/
theorem toFormula_injective {n : ℕ} {c d : CPol} (A : ClFormula PS TS n c)
    (B : ClFormula PS TS n d) (h : A.toFormula = B.toFormula) :
    (⟨c, A⟩ : Σ c, ClFormula PS TS n c) = ⟨d, B⟩ := by
  induction A generalizing d with
  | @atom _ c p ts =>
    cases B with
    | @atom _ d q us =>
      simp only [toFormula, Formula.atom.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨p, hp⟩ := p
      obtain ⟨q, hq⟩ := q
      subst h1
      obtain rfl : c = d := CPol.toPol_injective (hp.symm.trans hq)
      cases eq_of_heq h2
      rfl
    | _ => simp [toFormula] at h
  | one => cases B <;> simp_all [toFormula]
  | zero => cases B <;> simp_all [toFormula]
  | neg A ih =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.neg.injEq] at h
    obtain ⟨⟩ := ih _ h
    rfl
  | conj A A' ih ih' =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.conj.injEq] at h
    obtain ⟨⟩ := ih _ h.1
    obtain ⟨⟩ := ih' _ h.2
    rfl
  | disj A A' ih ih' =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.disj.injEq] at h
    obtain ⟨⟩ := ih _ h.1
    obtain ⟨⟩ := ih' _ h.2
    rfl
  | imp A A' ih ih' =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.imp.injEq] at h
    obtain ⟨⟩ := ih _ h.1
    obtain ⟨⟩ := ih' _ h.2
    rfl
  | call A ih =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.call.injEq] at h
    obtain ⟨⟩ := ih _ h
    rfl
  | cex A ih =>
    cases B <;> simp only [toFormula, reduceCtorEq, Formula.cex.injEq] at h
    obtain ⟨⟩ := ih _ h
    rfl

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
/-- Classical formulas are never neutral. -/
theorem pol_ne_neu_of_isClassical {n : ℕ} {A : Formula PS TS n} (h : A.IsClassical) :
    A.pol ≠ .neu := by
  obtain ⟨c, B, rfl⟩ := exists_of_isClassical A h
  cases c <;> simp [CPol.toPol]

end ClFormula

/-- Classical formulas of any polarity. -/
abbrev ClF (PS : PredSig) (TS : TermSig) (n : ℕ) : Type := Σ c : CPol, ClFormula PS TS n c

/-- The *stoup* of a classical sequent: room for at most one formula that is either negative
on the left or positive on the right (the formulas counted by `μ`). -/
inductive Stoup (PS : PredSig) (TS : TermSig) (n : ℕ) where
  /-- the stoup is empty -/
  | empty
  /-- a negative formula in the left linear zone -/
  | left (N : ClFormula PS TS n .neg)
  /-- a positive formula in the right linear zone -/
  | right (P : ClFormula PS TS n .pos)

/-- The contribution of the stoup to the left linear zone. -/
def Stoup.lhs {n : ℕ} : Stoup PS TS n → Multiset (Formula PS TS n)
  | .left N => {N.toFormula}
  | _ => 0

/-- The contribution of the stoup to the right linear zone. -/
def Stoup.rhs {n : ℕ} : Stoup PS TS n → Multiset (Formula PS TS n)
  | .right P => {P.toFormula}
  | _ => 0

/-- Classical sequents, correct by construction (stoup presentation): the left linear zone
holds positive classical formulas, the right linear zone negative ones, the central zones
arbitrary classical formulas, and the stoup at most one more formula. -/
structure ClSequent (PS : PredSig) (TS : TermSig) (n : ℕ) where
  /-- positive formulas of the left linear zone -/
  L : Multiset (ClFormula PS TS n .pos)
  /-- the left central zone -/
  CL : Finset (ClF PS TS n)
  /-- the right central zone -/
  CR : Finset (ClF PS TS n)
  /-- negative formulas of the right linear zone -/
  R : Multiset (ClFormula PS TS n .neg)
  /-- the stoup -/
  stoup : Stoup PS TS n

/-- The LU sequent of a classical sequent. -/
def ClSequent.toSequent {n : ℕ} (S : ClSequent PS TS n) : Sequent PS TS n :=
  ⟪S.L.map ClFormula.toFormula + S.stoup.lhs ; S.CL.image (fun A => A.2.toFormula) ⊢
    S.CR.image (fun A => A.2.toFormula) ; S.R.map ClFormula.toFormula + S.stoup.rhs⟫

omit [DecidableEq PS.Pred] [DecidableEq TS.Func] in
/-- In a multiset of formulas without neutral formulas, the positive and the negative
formulas make up everything. -/
theorem filter_pos_add_filter_neg {n : ℕ} (M : Multiset (Formula PS TS n))
    (h : ∀ A ∈ M, A.pol ≠ .neu) :
    M.filter (fun A => A.pol = .pos) + M.filter (fun A => A.pol = .neg) = M := by
  conv_rhs => rw [← Multiset.filter_add_not (fun A => A.pol = .pos) M]
  congr 1
  refine Multiset.filter_congr (fun A hA => ?_)
  have := h A hA
  revert this
  cases A.pol <;> simp

/-- The LU sequent of a `ClSequent` is a classical sequent. -/
theorem ClSequent.classicalSeq_toSequent {n : ℕ} (S : ClSequent PS TS n) :
    ClassicalSeq S.toSequent := by
  obtain ⟨L, CL, CR, R, st⟩ := S
  refine ⟨fun A hA => ?_, ?_⟩
  · simp only [toSequent, Sequent.formulas, Multiset.mem_add, Finset.mem_val,
      Finset.mem_image, Multiset.mem_map] at hA
    rcases hA with (((h | h) | h) | h) | h | h
    all_goals first
      | (obtain ⟨B, -, rfl⟩ := h; exact ClFormula.isClassical_toFormula _)
      | (cases st <;> simp_all [Stoup.lhs, Stoup.rhs, ClFormula.isClassical_toFormula])
  · have hL : (L.map ClFormula.toFormula).filter (fun A => A.pol = .neg) = 0 :=
      Multiset.filter_eq_nil.2 (by simp [CPol.toPol])
    have hR : (R.map ClFormula.toFormula).filter (fun A => A.pol = .pos) = 0 :=
      Multiset.filter_eq_nil.2 (by simp [CPol.toPol])
    simp only [mu, toSequent, Multiset.filter_add, hL, hR, zero_add]
    cases st <;> simp [Stoup.lhs, Stoup.rhs, Multiset.filter_singleton, CPol.toPol]

/-- Every classical sequent is the LU sequent of a `ClSequent`. -/
theorem ClSequent.exists_of_classicalSeq {n : ℕ} (S : Sequent PS TS n) (hS : ClassicalSeq S) :
    ∃ T : ClSequent PS TS n, T.toSequent = S := by
  obtain ⟨L, CL, CR, R⟩ := S
  obtain ⟨hall, hmu⟩ := hS
  simp only [AllIn, Sequent.formulas, Multiset.mem_add, Finset.mem_val] at hall
  have hLc : ∀ A ∈ L, A.IsClassical := fun A hA => hall A (by simp [hA])
  have hRc : ∀ A ∈ R, A.IsClassical := fun A hA => hall A (by simp [hA])
  -- lift the central zones
  obtain ⟨CL', hCL⟩ := finset_exists_image_eq (fun A : ClF PS TS n => A.2.toFormula) CL
    (fun A hA => by
      obtain ⟨c, B, hB⟩ := ClFormula.exists_of_isClassical A (hall A (by simp [hA]))
      exact ⟨⟨c, B⟩, hB⟩)
  obtain ⟨CR', hCR⟩ := finset_exists_image_eq (fun A : ClF PS TS n => A.2.toFormula) CR
    (fun A hA => by
      obtain ⟨c, B, hB⟩ := ClFormula.exists_of_isClassical A (hall A (by simp [hA]))
      exact ⟨⟨c, B⟩, hB⟩)
  -- lift the positive part of `L` and the negative part of `R`
  obtain ⟨L', hL'⟩ := multiset_exists_map_eq (ClFormula.toFormula (c := .pos))
    (L.filter (fun A => A.pol = .pos)) (fun A hA => by
      rw [Multiset.mem_filter] at hA
      exact ClFormula.exists_of_isClassical_pol A (hLc A hA.1) hA.2)
  obtain ⟨R', hR'⟩ := multiset_exists_map_eq (ClFormula.toFormula (c := .neg))
    (R.filter (fun A => A.pol = .neg)) (fun A hA => by
      rw [Multiset.mem_filter] at hA
      exact ClFormula.exists_of_isClassical_pol A (hRc A hA.1) hA.2)
  have hLsplit := filter_pos_add_filter_neg L
    (fun A hA => ClFormula.pol_ne_neu_of_isClassical (hLc A hA))
  have hRsplit := filter_pos_add_filter_neg R
    (fun A hA => ClFormula.pol_ne_neu_of_isClassical (hRc A hA))
  -- the stoup
  simp only [mu] at hmu
  set Ln := L.filter (fun A => A.pol = .neg) with hLn
  set Rp := R.filter (fun A => A.pol = .pos) with hRp
  have key : ∃ st : Stoup PS TS n, st.lhs = Ln ∧ st.rhs = Rp := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hmu with h0 | h1
    · refine ⟨.empty, ?_, ?_⟩ <;> simp [Stoup.lhs, Stoup.rhs] <;>
        [exact (Multiset.card_eq_zero.1 (by omega)).symm;
         exact (Multiset.card_eq_zero.1 (by omega)).symm]
    · rcases Nat.add_eq_one_iff.1 h1 with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · obtain ⟨N, hN⟩ := Multiset.card_eq_one.1 hr
        have hNm : N ∈ Rp := by simp [hN]
        rw [hRp, Multiset.mem_filter] at hNm
        obtain ⟨N', rfl⟩ := ClFormula.exists_of_isClassical_pol (c := .pos) N
          (hRc N hNm.1) hNm.2
        exact ⟨.right N', by simp [Stoup.lhs, Multiset.card_eq_zero.1 hl],
          by simp [Stoup.rhs, hN]⟩
      · obtain ⟨N, hN⟩ := Multiset.card_eq_one.1 hl
        have hNm : N ∈ Ln := by simp [hN]
        rw [hLn, Multiset.mem_filter] at hNm
        obtain ⟨N', rfl⟩ := ClFormula.exists_of_isClassical_pol (c := .neg) N
          (hLc N hNm.1) hNm.2
        exact ⟨.left N', by simp [Stoup.lhs, hN],
          by simp [Stoup.rhs, Multiset.card_eq_zero.1 hr]⟩
  obtain ⟨st, hst1, hst2⟩ := key
  refine ⟨⟨L', CL', CR', R', st⟩, ?_⟩
  simp only [ClSequent.toSequent, Sequent.mk_inj]
  refine ⟨?_, hCL, hCR, ?_⟩
  · rw [hL', hst1, hLsplit]
  · rw [hR', hst2, add_comm, hRsplit]

/-- **The classical sequents are exactly the `ClSequent`s.** -/
theorem ClSequent.range_toSequent {n : ℕ} (S : Sequent PS TS n) :
    ClassicalSeq S ↔ ∃ T : ClSequent PS TS n, T.toSequent = S :=
  ⟨exists_of_classicalSeq S, fun ⟨T, hT⟩ => hT ▸ T.classicalSeq_toSequent⟩

end LU
