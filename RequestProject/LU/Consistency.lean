module

public import RequestProject.LU.Calculus

/-!
# Soundness for classical truth and consistency of LU, for every choice of atom polarities

The polarity of an atomic predicate (`PS.predPol`) is a free parameter of LU: the rules
`outL`/`outR` and the rules of Fig. 3 consult it (through `Formula.pol`).  We show that no
choice of polarities makes LU inconsistent.

The argument is a classical (Tarskian) semantics that *forgets polarities and linearity*:
in a structure `M` (an arbitrary domain, possibly empty, with interpretations of the
function and predicate symbols), a formula is read classically with
`⊗, &, ∧ ↦ and`, `⅋, ⊕, ∨ ↦ or`, `⊸, ⇒, ⊃ ↦ implies`, `¬ ↦ not`, `!A, ?A ↦ A`,
`1, ⊤ ↦ true`, `0, ⊥ ↦ false`, `⋀, ∀ ↦ for all`, `⋁, ∃ ↦ exists`.
A sequent `Γ ; Γ' ⊢ Δ' ; Δ` is valid when, under every assignment of the free variables,
the conjunction of `Γ, Γ'` implies the disjunction of `Δ', Δ`.

* `Rule.sound`, `CutRule.sound`: every rule of LU, including the three cuts, preserves
  validity, *whatever the polarity side conditions say* (they are simply not used);
* `Provable.valid`: every provable sequent is valid in every structure;
* `not_provable_empty`, `not_provable_zero`, `not_provable_bot`, `not_provable_atom`,
  `not_provable_and_neg`: consistency;
* `consistent_for_every_polarity`: the same, stated explicitly for an arbitrary polarity
  assignment `pol : Pred → Pol` on a fixed set of predicate symbols.
-/

@[expose] public section

namespace LU

variable {PS : PredSig} {TS : TermSig}

/-- A classical first-order structure for the signatures `PS`, `TS`: a domain (possibly
empty), and interpretations of the function and predicate symbols.  Polarities play no
role. -/
structure Model (PS : PredSig) (TS : TermSig) where
  /-- the domain -/
  Dom : Type
  /-- interpretation of the function symbols -/
  fn : (f : TS.Func) → (Fin (TS.arity f) → Dom) → Dom
  /-- interpretation of the predicate symbols -/
  rel : (p : PS.Pred) → (Fin (PS.arity p) → Dom) → Prop

namespace Model

variable (M : Model PS TS)

mutual
/-- Value of a term under an assignment `ρ` of the free variables. -/
def evalTm {n : ℕ} (ρ : Fin n → M.Dom) : Tm TS n → M.Dom
  | .var i => ρ i
  | .func f ts => M.fn f (evalTms ρ ts)
/-- Value of a tuple of terms. -/
def evalTms {n : ℕ} (ρ : Fin n → M.Dom) : {k : ℕ} → Tms TS n k → Fin k → M.Dom
  | _, .nil => Fin.elim0
  | _, .cons t ts => Fin.cons (evalTm ρ t) (evalTms ρ ts)
end

mutual
theorem evalTm_subst {n m : ℕ} (σ : Subst TS n m) (ρ : Fin m → M.Dom) :
    (t : Tm TS n) → M.evalTm ρ (t.subst σ) = M.evalTm (fun i => M.evalTm ρ (σ i)) t
  | .var _ => rfl
  | .func f ts => by simp only [Tm.subst, evalTm, evalTms_subst σ ρ ts]
theorem evalTms_subst {n m : ℕ} (σ : Subst TS n m) (ρ : Fin m → M.Dom) :
    {k : ℕ} → (ts : Tms TS n k) →
      M.evalTms ρ (ts.subst σ) = M.evalTms (fun i => M.evalTm ρ (σ i)) ts
  | _, .nil => rfl
  | _, .cons t ts => by simp only [Tms.subst, evalTms, evalTm_subst σ ρ t, evalTms_subst σ ρ ts]
end

mutual
theorem evalTm_rename {n m : ℕ} (r : Fin n → Fin m) (ρ : Fin m → M.Dom) :
    (t : Tm TS n) → M.evalTm ρ (t.rename r) = M.evalTm (ρ ∘ r) t
  | .var _ => rfl
  | .func f ts => by simp only [Tm.rename, evalTm, evalTms_rename r ρ ts]
theorem evalTms_rename {n m : ℕ} (r : Fin n → Fin m) (ρ : Fin m → M.Dom) :
    {k : ℕ} → (ts : Tms TS n k) → M.evalTms ρ (ts.rename r) = M.evalTms (ρ ∘ r) ts
  | _, .nil => rfl
  | _, .cons t ts => by simp only [Tms.rename, evalTms, evalTm_rename r ρ t, evalTms_rename r ρ ts]
end

/-- Classical truth of a formula under an assignment `ρ` (polarities and linearity are
forgotten). -/
def eval : {n : ℕ} → Formula PS TS n → (Fin n → M.Dom) → Prop
  | _, .atom p ts, ρ => M.rel p (M.evalTms ρ ts)
  | _, .one, _ => True
  | _, .zero, _ => False
  | _, .bot, _ => False
  | _, .top, _ => True
  | _, .neg A, ρ => ¬ eval A ρ
  | _, .bang A, ρ => eval A ρ
  | _, .quest A, ρ => eval A ρ
  | _, .tensor A B, ρ => eval A ρ ∧ eval B ρ
  | _, .par A B, ρ => eval A ρ ∨ eval B ρ
  | _, .lolli A B, ρ => eval A ρ → eval B ρ
  | _, .with_ A B, ρ => eval A ρ ∧ eval B ρ
  | _, .plus A B, ρ => eval A ρ ∨ eval B ρ
  | _, .conj A B, ρ => eval A ρ ∧ eval B ρ
  | _, .disj A B, ρ => eval A ρ ∨ eval B ρ
  | _, .imp A B, ρ => eval A ρ → eval B ρ
  | _, .iimp A B, ρ => eval A ρ → eval B ρ
  | _, .lall A, ρ => ∀ x, eval A (Fin.cons x ρ)
  | _, .lex A, ρ => ∃ x, eval A (Fin.cons x ρ)
  | _, .call A, ρ => ∀ x, eval A (Fin.cons x ρ)
  | _, .cex A, ρ => ∃ x, eval A (Fin.cons x ρ)

theorem eval_lift {n m : ℕ} (σ : Subst TS n m) (ρ : Fin m → M.Dom) (x : M.Dom) :
    (fun i => M.evalTm (Fin.cons x ρ) (Subst.lift σ i)) =
      Fin.cons x (fun i => M.evalTm ρ (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Subst.lift_succ, Tm.shift, evalTm_rename, Fin.cons_succ]
  rfl

/-- The substitution lemma. -/
theorem eval_subst {n : ℕ} (A : Formula PS TS n) :
    ∀ {m : ℕ} (σ : Subst TS n m) (ρ : Fin m → M.Dom),
      M.eval (A.subst σ) ρ ↔ M.eval A (fun i => M.evalTm ρ (σ i)) := by
  induction A with
  | atom p ts => intro m σ ρ; simp only [Formula.subst, eval, evalTms_subst]
  | lall A ih | lex A ih | call A ih | cex A ih =>
    intro m σ ρ; simp only [Formula.subst, eval, ih, eval_lift]
  | _ => intro m σ ρ; simp_all [Formula.subst, eval]

theorem eval_shift {n : ℕ} (A : Formula PS TS n) (ρ : Fin (n + 1) → M.Dom) :
    M.eval A.shift ρ ↔ M.eval A (fun i => ρ i.succ) := by
  rw [Formula.shift, eval_subst]; rfl

theorem eval_inst {n : ℕ} (A : Formula PS TS (n + 1)) (t : Tm TS n) (ρ : Fin n → M.Dom) :
    M.eval (A.inst t) ρ ↔ M.eval A (Fin.cons (M.evalTm ρ t) ρ) := by
  rw [Formula.inst, eval_subst]
  congr! 1
  funext i
  refine Fin.cases rfl (fun j => rfl) i

/-- Classical validity of a sequent `Γ ; Γ' ⊢ Δ' ; Δ` in `M`: under every assignment, if all
formulas of `Γ, Γ'` are true then some formula of `Δ', Δ` is true. -/
def Valid {n : ℕ} (S : Sequent PS TS n) : Prop :=
  ∀ ρ : Fin n → M.Dom, (∀ A ∈ S.L, M.eval A ρ) → (∀ A ∈ S.CL, M.eval A ρ) →
    (∃ A ∈ S.CR, M.eval A ρ) ∨ (∃ A ∈ S.R, M.eval A ρ)

variable {M}

/-- All formulas of a multiset are true. -/
def AllT {n : ℕ} (Γ : Multiset (Formula PS TS n)) (ρ : Fin n → M.Dom) : Prop :=
  ∀ A ∈ Γ, M.eval A ρ
/-- Some formula of a multiset is true. -/
def ExT {n : ℕ} (Γ : Multiset (Formula PS TS n)) (ρ : Fin n → M.Dom) : Prop :=
  ∃ A ∈ Γ, M.eval A ρ

theorem allT_cons {n : ℕ} (A : Formula PS TS n) (Γ : Multiset (Formula PS TS n))
    (ρ : Fin n → M.Dom) : AllT (A ::ₘ Γ) ρ ↔ M.eval A ρ ∧ AllT Γ ρ := by
  simp [AllT]
theorem allT_add {n : ℕ} (Γ Λ : Multiset (Formula PS TS n)) (ρ : Fin n → M.Dom) :
    AllT (Γ + Λ) ρ ↔ AllT Γ ρ ∧ AllT Λ ρ := by
  simp only [AllT, Multiset.mem_add, or_imp, forall_and]
theorem allT_zero {n : ℕ} (ρ : Fin n → M.Dom) : AllT (M := M) (0 : Multiset (Formula PS TS n)) ρ := by
  simp [AllT]
theorem allT_singleton {n : ℕ} (A : Formula PS TS n) (ρ : Fin n → M.Dom) :
    AllT {A} ρ ↔ M.eval A ρ := by
  simp [AllT]
theorem exT_cons {n : ℕ} (A : Formula PS TS n) (Γ : Multiset (Formula PS TS n))
    (ρ : Fin n → M.Dom) : ExT (A ::ₘ Γ) ρ ↔ M.eval A ρ ∨ ExT Γ ρ := by
  simp [ExT]
theorem exT_add {n : ℕ} (Γ Λ : Multiset (Formula PS TS n)) (ρ : Fin n → M.Dom) :
    ExT (Γ + Λ) ρ ↔ ExT Γ ρ ∨ ExT Λ ρ := by
  simp only [ExT, Multiset.mem_add, or_and_right, exists_or]
theorem exT_zero {n : ℕ} (ρ : Fin n → M.Dom) : ¬ ExT (M := M) (0 : Multiset (Formula PS TS n)) ρ := by
  simp [ExT]
theorem exT_singleton {n : ℕ} (A : Formula PS TS n) (ρ : Fin n → M.Dom) :
    ExT {A} ρ ↔ M.eval A ρ := by
  simp [ExT]

theorem allT_sh {n : ℕ} (Γ : Multiset (Formula PS TS n)) (ρ : Fin (n + 1) → M.Dom) :
    AllT (sh Γ) ρ ↔ AllT Γ (fun i => ρ i.succ) := by
  simp [AllT, sh, eval_shift]
theorem exT_sh {n : ℕ} (Γ : Multiset (Formula PS TS n)) (ρ : Fin (n + 1) → M.Dom) :
    ExT (sh Γ) ρ ↔ ExT Γ (fun i => ρ i.succ) := by
  simp [ExT, sh, eval_shift]

theorem allT_val_empty {n : ℕ} (ρ : Fin n → M.Dom) :
    AllT (M := M) (∅ : Finset (Formula PS TS n)).val ρ := by
  simp [AllT]
theorem exT_val_empty {n : ℕ} (ρ : Fin n → M.Dom) :
    ¬ ExT (M := M) (∅ : Finset (Formula PS TS n)).val ρ := by
  simp [ExT]
/-- Validity, restated with `AllT` / `ExT`. -/
theorem valid_iff {n : ℕ} (S : Sequent PS TS n) :
    M.Valid S ↔ ∀ ρ : Fin n → M.Dom, AllT S.L ρ → AllT S.CL.val ρ → ExT S.CR.val ρ ∨ ExT S.R ρ := Iff.rfl

variable [DecidableEq PS.Pred] [DecidableEq TS.Func]

theorem allT_val_insert {n : ℕ} (A : Formula PS TS n) (Γ : Finset (Formula PS TS n))
    (ρ : Fin n → M.Dom) : AllT (insert A Γ).val ρ ↔ M.eval A ρ ∧ AllT Γ.val ρ := by
  simp [AllT]
theorem exT_val_insert {n : ℕ} (A : Formula PS TS n) (Γ : Finset (Formula PS TS n))
    (ρ : Fin n → M.Dom) : ExT (insert A Γ).val ρ ↔ M.eval A ρ ∨ ExT Γ.val ρ := by
  simp [ExT]
theorem allT_shc {n : ℕ} (Γ : Finset (Formula PS TS n)) (ρ : Fin (n + 1) → M.Dom) :
    AllT (shc Γ).val ρ ↔ AllT Γ.val (fun i => ρ i.succ) := by
  rw [shc_val, allT_sh]
theorem exT_shc {n : ℕ} (Γ : Finset (Formula PS TS n)) (ρ : Fin (n + 1) → M.Dom) :
    ExT (shc Γ).val ρ ↔ ExT Γ.val (fun i => ρ i.succ) := by
  rw [shc_val, exT_sh]

end Model

open Model

variable (M : Model PS TS) [DecidableEq PS.Pred] [DecidableEq TS.Func]

set_option maxHeartbeats 4000000 in
/-- Every rule of LU (Figures 1–3, cut excluded) preserves classical validity.  The polarity
side conditions of the rules are not used. -/
theorem Rule.sound {n : ℕ} {ps : List (Premise PS TS n)} {c : Sequent PS TS n}
    (h : Rule ps c) (hps : ∀ p ∈ ps, p.All (fun S => M.Valid S)) : M.Valid c := by
  cases h <;> simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Premise.All, valid_iff, IsEmpty.forall_iff, implies_true] at hps <;>
    rw [valid_iff] <;> intro ρ
  all_goals first
    | (try obtain ⟨h1, h2⟩ := hps
       try specialize h1 ρ
       try specialize h2 ρ
       try specialize hps ρ
       simp only [allT_cons, allT_add, allT_singleton, exT_cons, exT_add, exT_singleton,
         allT_val_insert, exT_val_insert, Model.eval, allT_zero, allT_val_empty,
         exT_zero, exT_val_empty, false_or, or_false, true_imp_iff,
         Multiset.insert_eq_cons] at *
       all_goals tauto)
    | skip
  all_goals
    simp only [allT_cons, exT_cons, allT_singleton, exT_singleton, allT_val_insert,
      exT_val_insert, allT_zero, exT_zero, Model.eval, eval_inst, true_imp_iff,
      or_false] at hps ⊢
  case lallR | callR_N =>
    intro hL hC
    by_contra hcon
    simp only [not_or, not_forall] at hcon
    obtain ⟨h1, ⟨x, hx⟩, h3⟩ := hcon
    have := hps (Fin.cons x ρ)
    simp only [allT_sh, allT_shc, exT_shc, exT_sh, Fin.cons_succ] at this
    tauto
  case callR_A =>
    intro hL hC
    by_contra hcon
    simp only [not_or, not_forall] at hcon
    obtain ⟨h1, ⟨x, hx⟩, h3⟩ := hcon
    have := hps (Fin.cons x ρ)
    simp only [allT_sh, allT_shc, exT_shc, exT_sh, Fin.cons_succ] at this
    tauto
  case lexL | cexL_P =>
    rintro ⟨⟨x, hx⟩, hL⟩ hC
    have := hps (Fin.cons x ρ)
    simp only [allT_sh, allT_shc, exT_shc, exT_sh, Fin.cons_succ] at this
    tauto
  case cexL_A =>
    rintro ⟨⟨x, hx⟩, hL⟩ hC
    have := hps (Fin.cons x ρ)
    simp only [allT_sh, allT_shc, exT_shc, exT_sh, Fin.cons_succ] at this
    tauto
  case lallL A t =>
    rintro ⟨hA, hL⟩ hC
    have := hps ρ ⟨hA (M.evalTm ρ t), hL⟩
    tauto
  case callL_A A t _ =>
    intro hA hC
    exact hps ρ (hA (M.evalTm ρ t)) hC
  case callL_N N t _ =>
    rintro ⟨hA, hL⟩ hC
    have := hps ρ ⟨hA (M.evalTm ρ t), hL⟩
    tauto
  case lexR A t | cexR_P A t _ =>
    intro hL hC
    have := hps ρ hL hC
    have key : M.eval A (Fin.cons (M.evalTm ρ t) ρ) → ∃ x, M.eval A (Fin.cons x ρ) :=
      fun h => ⟨_, h⟩
    tauto
  case cexR_A A t _ =>
    intro hC
    have := hps ρ hC
    have key : M.eval A (Fin.cons (M.evalTm ρ t) ρ) → ∃ x, M.eval A (Fin.cons x ρ) :=
      fun h => ⟨_, h⟩
    tauto

/-- The three cut rules of LU preserve classical validity. -/
theorem CutRule.sound {n : ℕ} {ps : List (Premise PS TS n)} {c : Sequent PS TS n}
    (h : CutRule ps c) (hps : ∀ p ∈ ps, p.All (fun S => M.Valid S)) : M.Valid c := by
  cases h <;> simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Premise.All, valid_iff] at hps <;>
    rw [valid_iff] <;> intro ρ <;> obtain ⟨h1, h2⟩ := hps <;> specialize h1 ρ <;>
    specialize h2 ρ <;>
    simp only [allT_cons, allT_add, allT_singleton, exT_cons, exT_add, exT_singleton,
      allT_val_insert, exT_val_insert, allT_zero, exT_zero, true_imp_iff, or_false] at * <;>
    tauto

/-- **Soundness.**  Every sequent provable in LU (with cuts) is classically valid in every
structure, for every assignment of polarities to the predicate symbols. -/
theorem Provable.valid {n : ℕ} {S : Sequent PS TS n} (h : Provable S) : M.Valid S := by
  induction h with
  | mk ps c hr _ _ _ ihs ihu =>
    have hps : ∀ p ∈ ps, p.All (fun S => M.Valid S) := by
      intro p hp
      cases p with
      | same s => exact ihs s hp
      | up s => exact ihu s hp
    rcases hr with hr | hr
    · exact Rule.sound M hr hps
    · exact CutRule.sound M hr hps

/-- The one-point structure in which every predicate is false. -/
def Model.trivial (PS : PredSig) (TS : TermSig) : Model PS TS where
  Dom := Unit
  fn := fun _ _ => ()
  rel := fun _ _ => False

/-- A formula provable on its own (`; ⊢ ; A`) is classically true in every structure under
every assignment. -/
theorem Provable.eval_of_provable {n : ℕ} {A : Formula PS TS n}
    (h : Provable ⟪0 ; ∅ ⊢ ∅ ; {A}⟫) (ρ : Fin n → M.Dom) : M.eval A ρ := by
  have := (h.valid M) ρ (allT_zero ρ) (allT_val_empty ρ)
  simpa [exT_singleton, exT_val_empty] using this

/-- **Consistency.**  The empty sequent `; ⊢ ;` is not provable in LU, whatever the
polarities of the atoms. -/
theorem not_provable_empty {n : ℕ} : ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; 0⟫ : Sequent PS TS n) := by
  intro h
  have := (h.valid (Model.trivial PS TS)) (fun _ => ()) (allT_zero _) (allT_val_empty _)
  simp at this

/-- **Consistency.**  `; ⊢ ; 0` is not provable in LU, whatever the polarities of the atoms. -/
theorem not_provable_zero {n : ℕ} : ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; {Formula.zero}⟫ : Sequent PS TS n) :=
  fun h => h.eval_of_provable (Model.trivial PS TS) (fun _ => ())

/-- **Consistency.**  `; ⊢ ; ⊥` is not provable in LU, whatever the polarities of the atoms. -/
theorem not_provable_bot {n : ℕ} : ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; {Formula.bot}⟫ : Sequent PS TS n) :=
  fun h => h.eval_of_provable (Model.trivial PS TS) (fun _ => ())

/-- No atomic formula `p(t₁, …, tₖ)` is provable in LU, whatever polarity `p` (or any other
predicate symbol) is given. -/
theorem not_provable_atom {n : ℕ} (p : PS.Pred) (ts : Tms TS n (PS.arity p)) :
    ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; {Formula.atom p ts}⟫ : Sequent PS TS n) :=
  fun h => h.eval_of_provable (Model.trivial PS TS) (fun _ => ())

/-- **Consistency.**  No formula `A` is provable together with its negation `¬A` (= `A⊥`),
whatever the polarities of the atoms. -/
theorem not_provable_and_neg {n : ℕ} (A : Formula PS TS n) :
    ¬ (Provable ⟪0 ; ∅ ⊢ ∅ ; {A}⟫ ∧ Provable ⟪0 ; ∅ ⊢ ∅ ; {Formula.neg A}⟫) := by
  rintro ⟨h, h'⟩
  exact h'.eval_of_provable (Model.trivial PS TS) (fun _ => ())
    (h.eval_of_provable (Model.trivial PS TS) (fun _ => ()))

/-- **The polarity of the predicate symbols cannot break LU.**  Fix predicate symbols `Pred`
with their arities, and choose *any* polarity `pol : Pred → Pol` for them (positive, negative
or neutral, arbitrarily).  Then, in LU over the resulting signature,
* every provable sequent is classically valid in every structure (the classical semantics does
  not mention `pol`);
* the empty sequent, `; ⊢ ; 0` and `; ⊢ ; ⊥` are not provable;
* no formula is provable together with its negation. -/
theorem consistent_for_every_polarity (Pred : Type) [DecidableEq Pred] (arity : Pred → ℕ)
    (pol : Pred → Pol) {n : ℕ} :
    let PS : PredSig := ⟨Pred, arity, pol⟩
    (∀ (M : Model PS TS) (S : Sequent PS TS n), Provable S → M.Valid S) ∧
    ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; 0⟫ : Sequent PS TS n) ∧
    ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; {Formula.zero}⟫ : Sequent PS TS n) ∧
    ¬ Provable (⟪0 ; ∅ ⊢ ∅ ; {Formula.bot}⟫ : Sequent PS TS n) ∧
    ∀ A : Formula PS TS n,
      ¬ (Provable ⟪0 ; ∅ ⊢ ∅ ; {A}⟫ ∧ Provable ⟪0 ; ∅ ⊢ ∅ ; {Formula.neg A}⟫) :=
  ⟨fun M _ h => h.valid M, not_provable_empty, not_provable_zero, not_provable_bot,
    not_provable_and_neg⟩

end LU
