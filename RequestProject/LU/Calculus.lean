module

public import RequestProject.LU.Syntax

/-!
# The sequent calculus LU

Sequents of LU have the shape `Γ ; Γ' ⊢ Δ' ; Δ` (§3): the formulas of `Γ` and `Δ` are
handled *linearly*, whereas the central zone `Γ'` / `Δ'` (between the two semicolons) has a
*classical maintenance* (weakening and contraction are allowed there).  The intended meaning
is the linear-logic sequent `Γ, !Γ' ⊢ ?Δ', Δ`.

The linear zones `Γ`, `Δ` are finite multisets of formulas and the central zones `Γ'`, `Δ'`
are finite *sets* of formulas: this builds in the exchange rule
`σ(Γ) ; σ'(Γ') ⊢ τ'(Δ') ; τ(Δ)` of Fig. 1, and also the two contraction rules of Fig. 1 (in a
finite set `A, A, Δ'` and `A, Δ'` are the same zone), which are therefore omitted; the two
weakening rules are kept.  In the rules, the principal formula of a linear zone is written at
the head (`A ::ₘ Γ` for "`Γ, A`" or "`A, Γ`"), and that of a central zone is inserted
(`insert A Γ'`).

* `Rule ps c` : `c` follows from the premises `ps` by one of the rules of Figures 1, 2, 3
  *other than cut*;
* `CutRule ps c` : `c` follows from `ps` by one of the three cut rules of Fig. 1;
* `Derivable R P S` : `S` has a derivation using rules from `R`, all of whose sequents
  satisfy `P`.

Remarks on the transcription.
* Sequents are well-scoped: `Sequent n` is the type of sequents whose formulas are in
  `Formula n` (`n` free variables in scope).  A premise of a rule is a `Premise n`: a sequent
  of the same scope `n`, or (for the eigenvariable rules) of scope `n + 1`.  The
  eigenvariable condition "`x` not free in `Γ;Γ' ⊢ Δ';Δ`" is then correct by construction:
  the premise lives in scope `n + 1`, the fresh variable is the index `0`, and the context of
  the premise is the weakening of the conclusion's context (`sh Γ = Γ.map Formula.shift`,
  `shc Γ' = Γ'.image Formula.shift`), which cannot mention the index `0`.
* **Departure from the printed Fig. 3.** In Fig. 3 (classical implication), Girard (1993,
  p. 213) prints the left rule for `N ⇒ P` with a *multiplicative* splitting of the contexts,
  `Γ;Γ' ⊢ Δ';Δ,N   Q,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ;Π`, which also contains typos
  (`Q` for `P`, `;` for `,`).  We deliberately use the *additive* rule instead:
  `Γ;Γ' ⊢ Δ';Δ,N   P,Γ;Γ' ⊢ Δ';Δ  /  N⇒P,Γ;Γ' ⊢ Δ';Δ` (`Rule.impL_NP`).
  This is the left rule of `N⊥ ⊕ P`, which is how Table 3 defines `N ⇒ P`, and it agrees
  with the paper's remark that these rules coincide with those of `¬(N ∧ ¬P) = N⊥ ⊕ P`.
  The multiplicative rule is not the left rule of `N⊥ ⊕ P`, and it breaks the induction on
  `μ` in the paper's proof of the Theorem for the classical fragment
  (see `LU.multiplicative_impL_NP_breaks_mu` in `MultiplicativeReading.lean`); the additive
  rule is needed to preserve the Theorem.
* As in the paper, the rules for the classical implication with neutral arguments are
  omitted ("this set of rules is incomplete").
-/

@[expose] public section

namespace LU

open Formula

/-- A sequent `Γ ; Γ' ⊢ Δ' ; Δ` of LU, in scope `n`: all formulas of the sequent are
well-scoped formulas of `Formula n` (a sequent of scope `0` is made of closed formulas). -/
structure Sequent (n : ℕ) where
  /-- `Γ`: left, linear zone -/
  L : Multiset (Formula n)
  /-- `Γ'`: left, central (classical) zone, a finite set (contraction is built in) -/
  CL : Finset (Formula n)
  /-- `Δ'`: right, central (classical) zone, a finite set (contraction is built in) -/
  CR : Finset (Formula n)
  /-- `Δ`: right, linear zone -/
  R : Multiset (Formula n)

@[inherit_doc] notation "⟪" Γ " ; " Γ' " ⊢ " Δ' " ; " Δ "⟫" => Sequent.mk Γ Γ' Δ' Δ

/-- Two sequents are equal iff their four zones are equal. -/
@[simp] theorem Sequent.mk_inj {n : ℕ} {Γ Δ Λ Θ : Multiset (Formula n)}
    {Γ' Δ' Λ' Θ' : Finset (Formula n)} :
    (⟪Γ ; Γ' ⊢ Δ' ; Δ⟫ = ⟪Λ ; Λ' ⊢ Θ' ; Θ⟫) ↔ Γ = Λ ∧ Γ' = Λ' ∧ Δ' = Θ' ∧ Δ = Θ := by
  simp

/-- A premise of a rule whose conclusion is in scope `n`: either a sequent of the same scope
`n` (`same`), or a sequent of scope `n + 1` (`up`), for the premise of an eigenvariable rule
(`⋀x` right, `⋁x` left, `∀x` right, `∃x` left), whose fresh variable is the index `0`. -/
inductive Premise (n : ℕ) where
  /-- a premise in the same scope as the conclusion -/
  | same : Sequent n → Premise n
  /-- a premise in the scope with one more (fresh) variable -/
  | up : Sequent (n + 1) → Premise n

/-- `p.All Q`: the sequent of the premise `p` satisfies `Q` (whatever its scope). -/
def Premise.All {n : ℕ} (Q : ∀ {m : ℕ}, Sequent m → Prop) : Premise n → Prop
  | .same s => Q s
  | .up s => Q s

@[simp] theorem Premise.all_same {n : ℕ} (Q : ∀ {m : ℕ}, Sequent m → Prop) (s : Sequent n) :
    (Premise.same s).All Q ↔ Q s := Iff.rfl

@[simp] theorem Premise.all_up {n : ℕ} (Q : ∀ {m : ℕ}, Sequent m → Prop) (s : Sequent (n + 1)) :
    (Premise.up s).All Q ↔ Q s := Iff.rfl

theorem Premise.All.imp {n : ℕ} {Q Q' : ∀ {m : ℕ}, Sequent m → Prop}
    (h : ∀ {m : ℕ} (s : Sequent m), Q s → Q' s) {p : Premise n} (hp : p.All Q) : p.All Q' := by
  cases p with
  | same s => exact h s hp
  | up s => exact h s hp

theorem Premise.All.and {n : ℕ} {Q Q' : ∀ {m : ℕ}, Sequent m → Prop} {p : Premise n}
    (h : p.All Q) (h' : p.All Q') : p.All (fun s => Q s ∧ Q' s) := by
  cases p with
  | same s => exact ⟨h, h'⟩
  | up s => exact ⟨h, h'⟩

theorem Premise.All.mp {n : ℕ} {Q Q' : ∀ {m : ℕ}, Sequent m → Prop} {p : Premise n}
    (h : p.All (fun s => Q s → Q' s)) (h' : p.All Q) : p.All Q' := by
  cases p with
  | same s => exact h h'
  | up s => exact h h'

/-- A property of all premises of a list, from its two instances. -/
theorem Premise.forall_all {n : ℕ} {ps : List (Premise n)} {Q : ∀ {m : ℕ}, Sequent m → Prop}
    (hs : ∀ s, Premise.same s ∈ ps → Q s) (hu : ∀ s, Premise.up s ∈ ps → Q s) :
    ∀ p ∈ ps, p.All Q := by
  intro p hp
  cases p with
  | same s => exact hs s hp
  | up s => exact hu s hp

/-- Weaken a context into the scope with one more variable (eigenvariable condition: the
fresh variable `0` does not occur in the context). -/
abbrev sh {n : ℕ} (Γ : Multiset (Formula n)) : Multiset (Formula (n + 1)) :=
  Γ.map Formula.shift

/-- Weaken a central zone into the scope with one more variable. -/
abbrev shc {n : ℕ} (Γ : Finset (Formula n)) : Finset (Formula (n + 1)) :=
  Γ.image Formula.shift

theorem shift_injective {n : ℕ} :
    Function.Injective (Formula.shift : Formula n → Formula (n + 1)) :=
  fun A B h => by simpa using congrArg (fun C => Formula.inst C default) h

/-- As a multiset, the weakening of a central zone is the weakening of its elements. -/
theorem shc_val {n : ℕ} (C : Finset (Formula n)) : (shc C).val = sh C.val :=
  Finset.image_val_of_injOn (shift_injective.injOn)

/-- The rules of LU other than cut (Figures 1, 2 and 3 of the paper).
`Rule ps c` means that the sequent `c` (in scope `n`) can be inferred from the list of
premises `ps`. -/
inductive Rule : {n : ℕ} → List (Premise n) → Sequent n → Prop where
  -- ### Fig. 1: identity and structure
  /-- identity `A ; ⊢ ; A` -/
  | ax {n : ℕ} (A : Formula n) : Rule [] ⟪{A} ; ∅ ⊢ ∅ ; {A}⟫
  /-- weakening in the central zone, right -/
  | weakR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫
  /-- weakening in the central zone, left -/
  | weakL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫
  /- Contraction in the central zone is built into the representation of the central zones
  as finite *sets*: `insert A (insert A Δ') = insert A Δ'`, so the premise and the conclusion
  of the two contraction rules of Fig. 1 are the same sequent, and the rules are omitted.
  | contrR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ insert A (insert A Δ') ; Δ⟫] ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫
  | contrL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A : Formula n) :
      Rule [.same ⟪Γ ; insert A (insert A Γ') ⊢ Δ' ; Δ⟫] ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫
  -/
  /-- permeability: any formula may enter the central zone (right) -/
  | inR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫
  /-- permeability: any formula may enter the central zone (left) -/
  | inL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫
  /-- permeability: a negative formula may exit the central zone (right) -/
  | outR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (N : Formula n) (hN : N.pol = .neg) :
      Rule [.same ⟪Γ ; Γ' ⊢ insert N Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫
  /-- permeability: a positive formula may exit the central zone (left) -/
  | outL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (P : Formula n) (hP : P.pol = .pos) :
      Rule [.same ⟪Γ ; insert P Γ' ⊢ Δ' ; Δ⟫] ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 2: linear connectives
  | oneR {n : ℕ} : Rule [] ⟪0 ; ∅ ⊢ ∅ ; {(one : Formula n)}⟫
  | botL {n : ℕ} : Rule [] ⟪{(bot : Formula n)} ; ∅ ⊢ ∅ ; 0⟫
  | tensorR {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, .same ⟪Λ ; Γ' ⊢ Δ' ; B ::ₘ Θ⟫]
        ⟪Γ + Λ ; Γ' ⊢ Δ' ; tensor A B ::ₘ (Δ + Θ)⟫
  | tensorL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪A ::ₘ B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪tensor A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | parR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A B : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; par A B ::ₘ Δ⟫
  | parL {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪par A B ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  | lolliR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; lolli A B ::ₘ Δ⟫
  | lolliL {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, .same ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪lolli A B ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  | topR {n : ℕ} (Γ Δ : Multiset (Formula n)) : Rule [] ⟪Γ ; ∅ ⊢ ∅ ; top ::ₘ Δ⟫
  | zeroL {n : ℕ} (Γ Δ : Multiset (Formula n)) : Rule [] ⟪zero ::ₘ Γ ; ∅ ⊢ ∅ ; Δ⟫
  | withR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A B : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, .same ⟪Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫]
        ⟪Γ ; Γ' ⊢ Δ' ; with_ A B ::ₘ Δ⟫
  | withL₁ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪with_ A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | withL₂ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪with_ A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | plusR₁ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; plus A B ::ₘ Δ⟫
  | plusR₂ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; plus A B ::ₘ Δ⟫
  | plusL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A B : Formula n) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫]
        ⟪plus A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | negL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫] ⟪neg A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | negR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; neg A ::ₘ Δ⟫
  | bangR {n : ℕ} (Γ' Δ' : Finset (Formula n)) (A : Formula n) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {A}⟫] ⟪0 ; Γ' ⊢ Δ' ; {bang A}⟫
  | bangL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      Rule [.same ⟪Γ ; insert A Γ' ⊢ Δ' ; Δ⟫] ⟪bang A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | questR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A : Formula n) :
      Rule [.same ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; quest A ::ₘ Δ⟫
  | questL {n : ℕ} (Γ' Δ' : Finset (Formula n)) (A : Formula n) :
      Rule [.same ⟪{A} ; Γ' ⊢ Δ' ; 0⟫] ⟪{quest A} ; Γ' ⊢ Δ' ; 0⟫
  | lallR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula (n + 1)) :
      Rule [.up ⟪sh Γ ; shc Γ' ⊢ shc Δ' ; A ::ₘ sh Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; lall A ::ₘ Δ⟫
  | lallL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula (n + 1)) (t : Term n) :
      Rule [.same ⟪A.inst t ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪lall A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | lexR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula (n + 1)) (t : Term n) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A.inst t ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; lex A ::ₘ Δ⟫
  | lexL {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula (n + 1)) :
      Rule [.up ⟪A ::ₘ sh Γ ; shc Γ' ⊢ shc Δ' ; sh Δ⟫] ⟪lex A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 3: conjunction (`P, Q` positive; `A, B` not positive)
  | conjR_PQ {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, .same ⟪Λ ; Γ' ⊢ Δ' ; Q ::ₘ Θ⟫]
        ⟪Γ + Λ ; Γ' ⊢ Δ' ; conj P Q ::ₘ (Δ + Θ)⟫
  | conjL_PQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪P ::ₘ Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪conj P Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjR_AQ {n : ℕ} (Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (A Q : Formula n)
      (hA : A.pol ≠ .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {A}⟫, .same ⟪Λ ; Γ' ⊢ Δ' ; Q ::ₘ Θ⟫] ⟪Λ ; Γ' ⊢ Δ' ; conj A Q ::ₘ Θ⟫
  | conjL_AQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A Q : Formula n)
      (hA : A.pol ≠ .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Q ::ₘ Γ ; insert A Γ' ⊢ Δ' ; Δ⟫] ⟪conj A Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjR_PB {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P B : Formula n)
      (hP : P.pol = .pos) (hB : B.pol ≠ .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, .same ⟪0 ; Γ' ⊢ Δ' ; {B}⟫] ⟪Γ ; Γ' ⊢ Δ' ; conj P B ::ₘ Δ⟫
  | conjL_PB {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P B : Formula n)
      (hP : P.pol = .pos) (hB : B.pol ≠ .pos) :
      Rule [.same ⟪P ::ₘ Γ ; insert B Γ' ⊢ Δ' ; Δ⟫] ⟪conj P B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjR_AB {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n)
      (hA : A.pol ≠ .pos) (hB : B.pol ≠ .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, .same ⟪Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫]
        ⟪Γ ; Γ' ⊢ Δ' ; conj A B ::ₘ Δ⟫
  | conjL_AB₁ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n)
      (hA : A.pol ≠ .pos) (hB : B.pol ≠ .pos) :
      Rule [.same ⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪conj A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjL_AB₂ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n)
      (hA : A.pol ≠ .pos) (hB : B.pol ≠ .pos) :
      Rule [.same ⟪B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪conj A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 3: intuitionistic implication (`P` positive; `A` not positive; `B` arbitrary)
  | iimpR_P {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P B : Formula n) (hP : P.pol = .pos) :
      Rule [.same ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; iimp P B ::ₘ Δ⟫
  | iimpL_P {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (P B : Formula n) (hP : P.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, .same ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪iimp P B ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  | iimpR_A {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A B : Formula n) (hA : A.pol ≠ .pos) :
      Rule [.same ⟪Γ ; insert A Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; iimp A B ::ₘ Δ⟫
  | iimpL_A {n : ℕ} (Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (A B : Formula n) (hA : A.pol ≠ .pos) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {A}⟫, .same ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪iimp A B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  -- ### Fig. 3: `∀` (`A` not negative; `N` negative)
  | callR_A {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (A : Formula (n + 1)) (hA : A.pol ≠ .neg) :
      Rule [.up ⟪sh Γ ; shc Γ' ⊢ insert A (shc Δ') ; sh Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; call A ::ₘ Δ⟫
  | callL_A {n : ℕ} (Γ' Δ' : Finset (Formula n)) (A : Formula (n + 1)) (t : Term n)
      (hA : A.pol ≠ .neg) :
      Rule [.same ⟪{A.inst t} ; Γ' ⊢ Δ' ; 0⟫] ⟪{call A} ; Γ' ⊢ Δ' ; 0⟫
  | callR_N {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (N : Formula (n + 1)) (hN : N.pol = .neg) :
      Rule [.up ⟪sh Γ ; shc Γ' ⊢ shc Δ' ; N ::ₘ sh Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; call N ::ₘ Δ⟫
  | callL_N {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (N : Formula (n + 1)) (t : Term n) (hN : N.pol = .neg) :
      Rule [.same ⟪N.inst t ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪call N ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 3: disjunction (`P, Q` positive; `M, N` negative; `S, T` neutral)
  | disjR₁_PQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P Q ::ₘ Δ⟫
  | disjR₂_PQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; Q ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P Q ::ₘ Δ⟫
  | disjL_PQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫]
        ⟪disj P Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_SQ {n : ℕ} (Γ' Δ' : Finset (Formula n)) (S Q : Formula n)
      (hS : S.pol = .neu) (hQ : Q.pol = .pos) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {S}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S Q}⟫
  | disjR₂_SQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (S Q : Formula n)
      (hS : S.pol = .neu) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; Q ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj S Q ::ₘ Δ⟫
  | disjL_SQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (S Q : Formula n)
      (hS : S.pol = .neu) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; insert S Γ' ⊢ Δ' ; Δ⟫, .same ⟪Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫]
        ⟪disj S Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR_MQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (M Q : Formula n)
      (hM : M.pol = .neg) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ insert Q Δ' ; M ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj M Q ::ₘ Δ⟫
  | disjL_MQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (M Q : Formula n)
      (hM : M.pol = .neg) (hQ : Q.pol = .pos) :
      Rule [.same ⟪M ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪0 ; insert Q Γ' ⊢ Δ' ; 0⟫]
        ⟪disj M Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_PT {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P T : Formula n)
      (hP : P.pol = .pos) (hT : T.pol = .neu) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P T ::ₘ Δ⟫
  | disjR₂_PT {n : ℕ} (Γ' Δ' : Finset (Formula n)) (P T : Formula n)
      (hP : P.pol = .pos) (hT : T.pol = .neu) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {T}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj P T}⟫
  | disjL_PT {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P T : Formula n)
      (hP : P.pol = .pos) (hT : T.pol = .neu) :
      Rule [.same ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪Γ ; insert T Γ' ⊢ Δ' ; Δ⟫]
        ⟪disj P T ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_ST {n : ℕ} (Γ' Δ' : Finset (Formula n)) (S T : Formula n)
      (hS : S.pol = .neu) (hT : T.pol = .neu) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {S}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S T}⟫
  | disjR₂_ST {n : ℕ} (Γ' Δ' : Finset (Formula n)) (S T : Formula n)
      (hS : S.pol = .neu) (hT : T.pol = .neu) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {T}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S T}⟫
  | disjL_ST {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (S T : Formula n)
      (hS : S.pol = .neu) (hT : T.pol = .neu) :
      Rule [.same ⟪Γ ; insert S Γ' ⊢ Δ' ; Δ⟫, .same ⟪Γ ; insert T Γ' ⊢ Δ' ; Δ⟫]
        ⟪disj S T ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_MT {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (M T : Formula n)
      (hM : M.pol = .neg) (hT : T.pol = .neu) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; M ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj M T ::ₘ Δ⟫
  | disjR₂_MT {n : ℕ} (Γ' Δ' : Finset (Formula n)) (M T : Formula n)
      (hM : M.pol = .neg) (hT : T.pol = .neu) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {M, T}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj M T}⟫
  | disjL_MT {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (M T : Formula n)
      (hM : M.pol = .neg) (hT : T.pol = .neu) :
      Rule [.same ⟪M ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪0 ; insert T Γ' ⊢ Δ' ; 0⟫]
        ⟪disj M T ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR_PN {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P N : Formula n)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [.same ⟪Γ ; Γ' ⊢ insert P Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P N ::ₘ Δ⟫
  | disjL_PN {n : ℕ} (Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (P N : Formula n)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [.same ⟪{P} ; Γ' ⊢ Δ' ; 0⟫, .same ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪disj P N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  | disjR₁_SN {n : ℕ} (Γ' Δ' : Finset (Formula n)) (S N : Formula n)
      (hS : S.pol = .neu) (hN : N.pol = .neg) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {S, N}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S N}⟫
  | disjR₂_SN {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (S N : Formula n)
      (hS : S.pol = .neu) (hN : N.pol = .neg) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj S N ::ₘ Δ⟫
  | disjL_SN {n : ℕ} (Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (S N : Formula n)
      (hS : S.pol = .neu) (hN : N.pol = .neg) :
      Rule [.same ⟪0 ; insert S Γ' ⊢ Δ' ; 0⟫, .same ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪disj S N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  | disjR_MN {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (M N : Formula n)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; M ::ₘ N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj M N ::ₘ Δ⟫
  | disjL_MN {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (M N : Formula n)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [.same ⟪M ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, .same ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪disj M N ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  -- ### Fig. 3: `∃` (`P` positive; `A` not positive)
  | cexR_P {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P : Formula (n + 1)) (t : Term n) (hP : P.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P.inst t ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; cex P ::ₘ Δ⟫
  | cexL_P {n : ℕ} (Λ : Multiset (Formula n)) (Λ' Θ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (P : Formula (n + 1)) (hP : P.pol = .pos) :
      Rule [.up ⟪P ::ₘ sh Λ ; shc Λ' ⊢ shc Θ' ; sh Θ⟫] ⟪cex P ::ₘ Λ ; Λ' ⊢ Θ' ; Θ⟫
  | cexR_A {n : ℕ} (Γ' Δ' : Finset (Formula n)) (A : Formula (n + 1)) (t : Term n)
      (hA : A.pol ≠ .pos) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {A.inst t}⟫] ⟪0 ; Γ' ⊢ Δ' ; {cex A}⟫
  | cexL_A {n : ℕ} (Λ : Multiset (Formula n)) (Λ' Θ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (A : Formula (n + 1)) (hA : A.pol ≠ .pos) :
      Rule [.up ⟪sh Λ ; insert A (shc Λ') ⊢ shc Θ' ; sh Θ⟫] ⟪cex A ::ₘ Λ ; Λ' ⊢ Θ' ; Θ⟫
  -- ### Fig. 3: classical implication (`P, Q` positive; `M, N` negative)
  | impR₁_NP {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (N P : Formula n)
      (hN : N.pol = .neg) (hP : P.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp N P ::ₘ Δ⟫
  | impR₂_NP {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (N P : Formula n)
      (hN : N.pol = .neg) (hP : P.pol = .pos) :
      Rule [.same ⟪N ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp N P ::ₘ Δ⟫
  /-- Left rule for `N ⇒ P`, **additive** version (the left rule of `N⊥ ⊕ P`, Table 3).
  This departs from the multiplicative rule (with typos) printed in Fig. 3 of Girard (1993);
  the multiplicative version breaks the Theorem's proof for the classical fragment. -/
  | impL_NP {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (N P : Formula n)
      (hN : N.pol = .neg) (hP : P.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫, .same ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫]
        ⟪imp N P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | impR_PQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪P ::ₘ Γ ; Γ' ⊢ insert Q Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp P Q ::ₘ Δ⟫
  | impL_PQ {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P Q : Formula n)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, .same ⟪{Q} ; Γ' ⊢ Δ' ; 0⟫] ⟪imp P Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | impR_MN {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (M N : Formula n)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [.same ⟪Γ ; insert M Γ' ⊢ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp M N ::ₘ Δ⟫
  | impL_MN {n : ℕ} (Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Θ : Multiset (Formula n)) (M N : Formula n)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [.same ⟪0 ; Γ' ⊢ Δ' ; {M}⟫, .same ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪imp M N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  | impR_PN {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ : Multiset (Formula n)) (P N : Formula n)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [.same ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp P N ::ₘ Δ⟫
  | impL_PN {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (P N : Formula n)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [.same ⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, .same ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪imp P N ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫

/-- The three cut rules of LU (Fig. 1). -/
inductive CutRule : {n : ℕ} → List (Premise n) → Sequent n → Prop where
  /-- cut between two linear occurrences of `A` -/
  | cut {n : ℕ} (Γ Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n))
      (Δ Θ : Multiset (Formula n)) (A : Formula n) :
      CutRule [.same ⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, .same ⟪A ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪Γ + Λ ; Γ' ⊢ Δ' ; Δ + Θ⟫
  /-- cut between a central occurrence of `A` (right) and a linear one (left) -/
  | cutR {n : ℕ} (Γ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Δ : Multiset (Formula n))
      (A : Formula n) :
      CutRule [.same ⟪Γ ; Γ' ⊢ insert A Δ' ; Δ⟫, .same ⟪{A} ; Γ' ⊢ Δ' ; 0⟫] ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫
  /-- cut between a linear occurrence of `A` (right) and a central one (left) -/
  | cutL {n : ℕ} (Λ : Multiset (Formula n)) (Γ' Δ' : Finset (Formula n)) (Θ : Multiset (Formula n))
      (A : Formula n) :
      CutRule [.same ⟪0 ; Γ' ⊢ Δ' ; {A}⟫, .same ⟪Λ ; insert A Γ' ⊢ Δ' ; Θ⟫] ⟪Λ ; Γ' ⊢ Δ' ; Θ⟫

/-- `Derivable R P S`: the sequent `S` has a derivation built from rule instances in `R`,
in which *every* sequent satisfies `P`.  The premises of a rule are derivable, whether they
are in the same scope as the conclusion (`Premise.same`) or in the scope with one more
variable (`Premise.up`). -/
inductive Derivable (R : ∀ {n : ℕ}, List (Premise n) → Sequent n → Prop)
    (P : ∀ {n : ℕ}, Sequent n → Prop) : ∀ {n : ℕ}, Sequent n → Prop where
  | mk {n : ℕ} (ps : List (Premise n)) (c : Sequent n) :
      R ps c → P c → (∀ s, Premise.same s ∈ ps → Derivable R P s) →
      (∀ s, Premise.up s ∈ ps → Derivable R P s) → Derivable R P c

/-- All rules of LU, including cut. -/
def LURule {n : ℕ} (ps : List (Premise n)) (c : Sequent n) : Prop := Rule ps c ∨ CutRule ps c

/-- Provability in LU (cut allowed). -/
def Provable {n : ℕ} (S : Sequent n) : Prop := Derivable LURule (fun _ => True) S

/-- Cut-free provability in LU. -/
def CutFreeProvable {n : ℕ} (S : Sequent n) : Prop := Derivable Rule (fun _ => True) S

/-- The (multiset of all) formulas occurring in a sequent. -/
def Sequent.formulas {n : ℕ} (S : Sequent n) : Multiset (Formula n) :=
  S.L + S.CL.val + S.CR.val + S.R

section Derivable

variable {R R' : ∀ {n : ℕ}, List (Premise n) → Sequent n → Prop}
  {P P' : ∀ {n : ℕ}, Sequent n → Prop}

/-- Build a derivation from a rule instance whose premises are all derivable. -/
theorem Derivable.mk' {n : ℕ} (ps : List (Premise n)) (c : Sequent n) (hr : R ps c) (hc : P c)
    (h : ∀ p ∈ ps, p.All (Derivable R P)) : Derivable R P c :=
  .mk ps c hr hc (fun _ hs => h _ hs) (fun _ hs => h _ hs)

/-- Inversion: the last rule of a derivation. -/
theorem Derivable.cases' {n : ℕ} {S : Sequent n} (h : Derivable R P S) :
    ∃ ps, R ps S ∧ P S ∧ ∀ p ∈ ps, p.All (Derivable R P) := by
  cases h with
  | mk ps c hr hc hs hu =>
    refine ⟨ps, hr, hc, fun p hp => ?_⟩
    cases p with
    | same s => exact hs s hp
    | up s => exact hu s hp

theorem Derivable.mono
    (hR : ∀ {n : ℕ} (ps : List (Premise n)) (c : Sequent n), R ps c → R' ps c)
    (hP : ∀ {n : ℕ} (S : Sequent n), P S → P' S) {n : ℕ} {S : Sequent n}
    (h : Derivable R P S) : Derivable R' P' S := by
  induction h with
  | mk ps c hr hc _ _ ihs ihu => exact .mk' ps c (hR _ _ hr) (hP _ hc) (Premise.forall_all ihs ihu)

end Derivable

/-- Cut-free provability implies provability. -/
theorem CutFreeProvable.provable {n : ℕ} {S : Sequent n} (h : CutFreeProvable S) :
    Provable S :=
  Derivable.mono (fun _ _ h => Or.inl h) (fun _ h => h) h

end LU
