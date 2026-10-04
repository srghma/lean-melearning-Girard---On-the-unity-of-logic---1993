module

public import RequestProject.LU.Syntax

/-!
# The sequent calculus LU

Sequents of LU have the shape `Γ ; Γ' ⊢ Δ' ; Δ` (§3): the formulas of `Γ` and `Δ` are
handled *linearly*, whereas the central zone `Γ'` / `Δ'` (between the two semicolons) has a
*classical maintenance* (weakening and contraction are allowed there).  The intended meaning
is the linear-logic sequent `Γ, !Γ' ⊢ ?Δ', Δ`.

Each of the four zones is a finite multiset of formulas: this builds in the exchange rule
`σ(Γ) ; σ'(Γ') ⊢ τ'(Δ') ; τ(Δ)` of Fig. 1.  In the rules, the principal formula of a zone is
written at the head (`A ::ₘ Γ` for "`Γ, A`" or "`A, Γ`").

* `Rule ps c` : `c` follows from the premises `ps` by one of the rules of Figures 1, 2, 3
  *other than cut*;
* `CutRule ps c` : `c` follows from `ps` by one of the three cut rules of Fig. 1;
* `Derivable R P S` : `S` has a derivation using rules from `R`, all of whose sequents
  satisfy `P`.

Remarks on the transcription.
* The eigenvariable condition "`x` not free in `Γ;Γ' ⊢ Δ';Δ`" is expressed with de Bruijn
  indices: the context of the premise is shifted (`sh Γ = Γ.map Formula.shift`).
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

/-- A sequent `Γ ; Γ' ⊢ Δ' ; Δ` of LU. -/
structure Sequent where
  /-- `Γ`: left, linear zone -/
  L : Multiset Formula
  /-- `Γ'`: left, central (classical) zone -/
  CL : Multiset Formula
  /-- `Δ'`: right, central (classical) zone -/
  CR : Multiset Formula
  /-- `Δ`: right, linear zone -/
  R : Multiset Formula

@[inherit_doc] notation "⟪" Γ " ; " Γ' " ⊢ " Δ' " ; " Δ "⟫" => Sequent.mk Γ Γ' Δ' Δ

/-- Shift all free variables of a context (eigenvariable condition). -/
abbrev sh (Γ : Multiset Formula) : Multiset Formula := Γ.map Formula.shift

/-- The rules of LU other than cut (Figures 1, 2 and 3 of the paper).
`Rule ps c` means that `c` can be inferred from the list of premises `ps`. -/
inductive Rule : List Sequent → Sequent → Prop where
  -- ### Fig. 1: identity and structure
  /-- identity `A ; ⊢ ; A` -/
  | ax (A : Formula) : Rule [] ⟪{A} ; 0 ⊢ 0 ; {A}⟫
  /-- weakening in the central zone, right -/
  | weakR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫
  /-- weakening in the central zone, left -/
  | weakL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫
  /-- contraction in the central zone, right -/
  | contrR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; Γ' ⊢ A ::ₘ A ::ₘ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫
  /-- contraction in the central zone, left -/
  | contrL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; A ::ₘ A ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫
  /-- permeability: any formula may enter the central zone (right) -/
  | inR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫
  /-- permeability: any formula may enter the central zone (left) -/
  | inL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫
  /-- permeability: a negative formula may exit the central zone (right) -/
  | outR (Γ Γ' Δ' Δ : Multiset Formula) (N : Formula) (hN : N.pol = .neg) :
      Rule [⟪Γ ; Γ' ⊢ N ::ₘ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫
  /-- permeability: a positive formula may exit the central zone (left) -/
  | outL (Γ Γ' Δ' Δ : Multiset Formula) (P : Formula) (hP : P.pol = .pos) :
      Rule [⟪Γ ; P ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 2: linear connectives
  | oneR : Rule [] ⟪0 ; 0 ⊢ 0 ; {one}⟫
  | botL : Rule [] ⟪{bot} ; 0 ⊢ 0 ; 0⟫
  | tensorR (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (A B : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, ⟪Λ ; Γ' ⊢ Δ' ; B ::ₘ Θ⟫]
        ⟪Γ + Λ ; Γ' ⊢ Δ' ; tensor A B ::ₘ (Δ + Θ)⟫
  | tensorL (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪A ::ₘ B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪tensor A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | parR (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; par A B ::ₘ Δ⟫
  | parL (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (A B : Formula) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪par A B ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  | lolliR (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; lolli A B ::ₘ Δ⟫
  | lolliL (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (A B : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪lolli A B ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  | topR (Γ Δ : Multiset Formula) : Rule [] ⟪Γ ; 0 ⊢ 0 ; top ::ₘ Δ⟫
  | zeroL (Γ Δ : Multiset Formula) : Rule [] ⟪zero ::ₘ Γ ; 0 ⊢ 0 ; Δ⟫
  | withR (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, ⟪Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; with_ A B ::ₘ Δ⟫
  | withL₁ (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪with_ A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | withL₂ (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪with_ A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | plusR₁ (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; plus A B ::ₘ Δ⟫
  | plusR₂ (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; plus A B ::ₘ Δ⟫
  | plusL (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪plus A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | negL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫] ⟪neg A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | negR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; neg A ::ₘ Δ⟫
  | bangR (Γ' Δ' : Multiset Formula) (A : Formula) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {A}⟫] ⟪0 ; Γ' ⊢ Δ' ; {bang A}⟫
  | bangL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪bang A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | questR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; quest A ::ₘ Δ⟫
  | questL (Γ' Δ' : Multiset Formula) (A : Formula) :
      Rule [⟪{A} ; Γ' ⊢ Δ' ; 0⟫] ⟪{quest A} ; Γ' ⊢ Δ' ; 0⟫
  | lallR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪sh Γ ; sh Γ' ⊢ sh Δ' ; A ::ₘ sh Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; lall A ::ₘ Δ⟫
  | lallL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) (t : Term) :
      Rule [⟪A.inst t ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪lall A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | lexR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) (t : Term) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A.inst t ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; lex A ::ₘ Δ⟫
  | lexL (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      Rule [⟪A ::ₘ sh Γ ; sh Γ' ⊢ sh Δ' ; sh Δ⟫] ⟪lex A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 3: conjunction (`P, Q` positive; `A, B` not positive)
  | conjR_PQ (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, ⟪Λ ; Γ' ⊢ Δ' ; Q ::ₘ Θ⟫]
        ⟪Γ + Λ ; Γ' ⊢ Δ' ; conj P Q ::ₘ (Δ + Θ)⟫
  | conjL_PQ (Γ Γ' Δ' Δ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪P ::ₘ Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪conj P Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjR_AQ (Λ Γ' Δ' Θ : Multiset Formula) (A Q : Formula)
      (hA : A.pol ≠ .pos) (hQ : Q.pol = .pos) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {A}⟫, ⟪Λ ; Γ' ⊢ Δ' ; Q ::ₘ Θ⟫] ⟪Λ ; Γ' ⊢ Δ' ; conj A Q ::ₘ Θ⟫
  | conjL_AQ (Γ Γ' Δ' Δ : Multiset Formula) (A Q : Formula)
      (hA : A.pol ≠ .pos) (hQ : Q.pol = .pos) :
      Rule [⟪Q ::ₘ Γ ; A ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪conj A Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjR_PB (Γ Γ' Δ' Δ : Multiset Formula) (P B : Formula)
      (hP : P.pol = .pos) (hB : B.pol ≠ .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, ⟪0 ; Γ' ⊢ Δ' ; {B}⟫] ⟪Γ ; Γ' ⊢ Δ' ; conj P B ::ₘ Δ⟫
  | conjL_PB (Γ Γ' Δ' Δ : Multiset Formula) (P B : Formula)
      (hP : P.pol = .pos) (hB : B.pol ≠ .pos) :
      Rule [⟪P ::ₘ Γ ; B ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪conj P B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjR_AB (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula)
      (hA : A.pol ≠ .pos) (hB : B.pol ≠ .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, ⟪Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; conj A B ::ₘ Δ⟫
  | conjL_AB₁ (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula)
      (hA : A.pol ≠ .pos) (hB : B.pol ≠ .pos) :
      Rule [⟪A ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪conj A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | conjL_AB₂ (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula)
      (hA : A.pol ≠ .pos) (hB : B.pol ≠ .pos) :
      Rule [⟪B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪conj A B ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 3: intuitionistic implication (`P` positive; `A` not positive; `B` arbitrary)
  | iimpR_P (Γ Γ' Δ' Δ : Multiset Formula) (P B : Formula) (hP : P.pol = .pos) :
      Rule [⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; iimp P B ::ₘ Δ⟫
  | iimpL_P (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (P B : Formula) (hP : P.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪iimp P B ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  | iimpR_A (Γ Γ' Δ' Δ : Multiset Formula) (A B : Formula) (hA : A.pol ≠ .pos) :
      Rule [⟪Γ ; A ::ₘ Γ' ⊢ Δ' ; B ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; iimp A B ::ₘ Δ⟫
  | iimpL_A (Λ Γ' Δ' Θ : Multiset Formula) (A B : Formula) (hA : A.pol ≠ .pos) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {A}⟫, ⟪B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪iimp A B ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  -- ### Fig. 3: `∀` (`A` not negative; `N` negative)
  | callR_A (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) (hA : A.pol ≠ .neg) :
      Rule [⟪sh Γ ; sh Γ' ⊢ A ::ₘ sh Δ' ; sh Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; call A ::ₘ Δ⟫
  | callL_A (Γ' Δ' : Multiset Formula) (A : Formula) (t : Term) (hA : A.pol ≠ .neg) :
      Rule [⟪{A.inst t} ; Γ' ⊢ Δ' ; 0⟫] ⟪{call A} ; Γ' ⊢ Δ' ; 0⟫
  | callR_N (Γ Γ' Δ' Δ : Multiset Formula) (N : Formula) (hN : N.pol = .neg) :
      Rule [⟪sh Γ ; sh Γ' ⊢ sh Δ' ; N ::ₘ sh Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; call N ::ₘ Δ⟫
  | callL_N (Γ Γ' Δ' Δ : Multiset Formula) (N : Formula) (t : Term) (hN : N.pol = .neg) :
      Rule [⟪N.inst t ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪call N ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  -- ### Fig. 3: disjunction (`P, Q` positive; `M, N` negative; `S, T` neutral)
  | disjR₁_PQ (Γ Γ' Δ' Δ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P Q ::ₘ Δ⟫
  | disjR₂_PQ (Γ Γ' Δ' Δ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; Q ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P Q ::ₘ Δ⟫
  | disjL_PQ (Γ Γ' Δ' Δ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪disj P Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_SQ (Γ' Δ' : Multiset Formula) (S Q : Formula)
      (hS : S.pol = .neu) (hQ : Q.pol = .pos) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {S}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S Q}⟫
  | disjR₂_SQ (Γ Γ' Δ' Δ : Multiset Formula) (S Q : Formula)
      (hS : S.pol = .neu) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; Q ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj S Q ::ₘ Δ⟫
  | disjL_SQ (Γ Γ' Δ' Δ : Multiset Formula) (S Q : Formula)
      (hS : S.pol = .neu) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; S ::ₘ Γ' ⊢ Δ' ; Δ⟫, ⟪Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪disj S Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR_MQ (Γ Γ' Δ' Δ : Multiset Formula) (M Q : Formula)
      (hM : M.pol = .neg) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Q ::ₘ Δ' ; M ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj M Q ::ₘ Δ⟫
  | disjL_MQ (Γ Γ' Δ' Δ : Multiset Formula) (M Q : Formula)
      (hM : M.pol = .neg) (hQ : Q.pol = .pos) :
      Rule [⟪M ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪0 ; Q ::ₘ Γ' ⊢ Δ' ; 0⟫] ⟪disj M Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_PT (Γ Γ' Δ' Δ : Multiset Formula) (P T : Formula)
      (hP : P.pol = .pos) (hT : T.pol = .neu) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P T ::ₘ Δ⟫
  | disjR₂_PT (Γ' Δ' : Multiset Formula) (P T : Formula)
      (hP : P.pol = .pos) (hT : T.pol = .neu) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {T}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj P T}⟫
  | disjL_PT (Γ Γ' Δ' Δ : Multiset Formula) (P T : Formula)
      (hP : P.pol = .pos) (hT : T.pol = .neu) :
      Rule [⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪Γ ; T ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪disj P T ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_ST (Γ' Δ' : Multiset Formula) (S T : Formula)
      (hS : S.pol = .neu) (hT : T.pol = .neu) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {S}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S T}⟫
  | disjR₂_ST (Γ' Δ' : Multiset Formula) (S T : Formula)
      (hS : S.pol = .neu) (hT : T.pol = .neu) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {T}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S T}⟫
  | disjL_ST (Γ Γ' Δ' Δ : Multiset Formula) (S T : Formula)
      (hS : S.pol = .neu) (hT : T.pol = .neu) :
      Rule [⟪Γ ; S ::ₘ Γ' ⊢ Δ' ; Δ⟫, ⟪Γ ; T ::ₘ Γ' ⊢ Δ' ; Δ⟫] ⟪disj S T ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR₁_MT (Γ Γ' Δ' Δ : Multiset Formula) (M T : Formula)
      (hM : M.pol = .neg) (hT : T.pol = .neu) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; M ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj M T ::ₘ Δ⟫
  | disjR₂_MT (Γ' Δ' : Multiset Formula) (M T : Formula)
      (hM : M.pol = .neg) (hT : T.pol = .neu) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {M, T}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj M T}⟫
  | disjL_MT (Γ Γ' Δ' Δ : Multiset Formula) (M T : Formula)
      (hM : M.pol = .neg) (hT : T.pol = .neu) :
      Rule [⟪M ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪0 ; T ::ₘ Γ' ⊢ Δ' ; 0⟫] ⟪disj M T ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | disjR_PN (Γ Γ' Δ' Δ : Multiset Formula) (P N : Formula)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [⟪Γ ; Γ' ⊢ P ::ₘ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj P N ::ₘ Δ⟫
  | disjL_PN (Λ Γ' Δ' Θ : Multiset Formula) (P N : Formula)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [⟪{P} ; Γ' ⊢ Δ' ; 0⟫, ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪disj P N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  | disjR₁_SN (Γ' Δ' : Multiset Formula) (S N : Formula)
      (hS : S.pol = .neu) (hN : N.pol = .neg) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {S, N}⟫] ⟪0 ; Γ' ⊢ Δ' ; {disj S N}⟫
  | disjR₂_SN (Γ Γ' Δ' Δ : Multiset Formula) (S N : Formula)
      (hS : S.pol = .neu) (hN : N.pol = .neg) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj S N ::ₘ Δ⟫
  | disjL_SN (Λ Γ' Δ' Θ : Multiset Formula) (S N : Formula)
      (hS : S.pol = .neu) (hN : N.pol = .neg) :
      Rule [⟪0 ; S ::ₘ Γ' ⊢ Δ' ; 0⟫, ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪disj S N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  | disjR_MN (Γ Γ' Δ' Δ : Multiset Formula) (M N : Formula)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; M ::ₘ N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; disj M N ::ₘ Δ⟫
  | disjL_MN (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (M N : Formula)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [⟪M ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫, ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪disj M N ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫
  -- ### Fig. 3: `∃` (`P` positive; `A` not positive)
  | cexR_P (Γ Γ' Δ' Δ : Multiset Formula) (P : Formula) (t : Term) (hP : P.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P.inst t ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; cex P ::ₘ Δ⟫
  | cexL_P (Λ Λ' Θ' Θ : Multiset Formula) (P : Formula) (hP : P.pol = .pos) :
      Rule [⟪P ::ₘ sh Λ ; sh Λ' ⊢ sh Θ' ; sh Θ⟫] ⟪cex P ::ₘ Λ ; Λ' ⊢ Θ' ; Θ⟫
  | cexR_A (Γ' Δ' : Multiset Formula) (A : Formula) (t : Term) (hA : A.pol ≠ .pos) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {A.inst t}⟫] ⟪0 ; Γ' ⊢ Δ' ; {cex A}⟫
  | cexL_A (Λ Λ' Θ' Θ : Multiset Formula) (A : Formula) (hA : A.pol ≠ .pos) :
      Rule [⟪sh Λ ; A ::ₘ sh Λ' ⊢ sh Θ' ; sh Θ⟫] ⟪cex A ::ₘ Λ ; Λ' ⊢ Θ' ; Θ⟫
  -- ### Fig. 3: classical implication (`P, Q` positive; `M, N` negative)
  | impR₁_NP (Γ Γ' Δ' Δ : Multiset Formula) (N P : Formula)
      (hN : N.pol = .neg) (hP : P.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp N P ::ₘ Δ⟫
  | impR₂_NP (Γ Γ' Δ' Δ : Multiset Formula) (N P : Formula)
      (hN : N.pol = .neg) (hP : P.pol = .pos) :
      Rule [⟪N ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp N P ::ₘ Δ⟫
  /-- Left rule for `N ⇒ P`, **additive** version (the left rule of `N⊥ ⊕ P`, Table 3).
  This departs from the multiplicative rule (with typos) printed in Fig. 3 of Girard (1993);
  the multiplicative version breaks the Theorem's proof for the classical fragment. -/
  | impL_NP (Γ Γ' Δ' Δ : Multiset Formula) (N P : Formula)
      (hN : N.pol = .neg) (hP : P.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫, ⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫] ⟪imp N P ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | impR_PQ (Γ Γ' Δ' Δ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪P ::ₘ Γ ; Γ' ⊢ Q ::ₘ Δ' ; Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp P Q ::ₘ Δ⟫
  | impL_PQ (Γ Γ' Δ' Δ : Multiset Formula) (P Q : Formula)
      (hP : P.pol = .pos) (hQ : Q.pol = .pos) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, ⟪{Q} ; Γ' ⊢ Δ' ; 0⟫] ⟪imp P Q ::ₘ Γ ; Γ' ⊢ Δ' ; Δ⟫
  | impR_MN (Γ Γ' Δ' Δ : Multiset Formula) (M N : Formula)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [⟪Γ ; M ::ₘ Γ' ⊢ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp M N ::ₘ Δ⟫
  | impL_MN (Λ Γ' Δ' Θ : Multiset Formula) (M N : Formula)
      (hM : M.pol = .neg) (hN : N.pol = .neg) :
      Rule [⟪0 ; Γ' ⊢ Δ' ; {M}⟫, ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪imp M N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫
  | impR_PN (Γ Γ' Δ' Δ : Multiset Formula) (P N : Formula)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [⟪P ::ₘ Γ ; Γ' ⊢ Δ' ; N ::ₘ Δ⟫] ⟪Γ ; Γ' ⊢ Δ' ; imp P N ::ₘ Δ⟫
  | impL_PN (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (P N : Formula)
      (hP : P.pol = .pos) (hN : N.pol = .neg) :
      Rule [⟪Γ ; Γ' ⊢ Δ' ; P ::ₘ Δ⟫, ⟪N ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫]
        ⟪imp P N ::ₘ (Γ + Λ) ; Γ' ⊢ Δ' ; Δ + Θ⟫

/-- The three cut rules of LU (Fig. 1). -/
inductive CutRule : List Sequent → Sequent → Prop where
  /-- cut between two linear occurrences of `A` -/
  | cut (Γ Λ Γ' Δ' Δ Θ : Multiset Formula) (A : Formula) :
      CutRule [⟪Γ ; Γ' ⊢ Δ' ; A ::ₘ Δ⟫, ⟪A ::ₘ Λ ; Γ' ⊢ Δ' ; Θ⟫] ⟪Γ + Λ ; Γ' ⊢ Δ' ; Δ + Θ⟫
  /-- cut between a central occurrence of `A` (right) and a linear one (left) -/
  | cutR (Γ Γ' Δ' Δ : Multiset Formula) (A : Formula) :
      CutRule [⟪Γ ; Γ' ⊢ A ::ₘ Δ' ; Δ⟫, ⟪{A} ; Γ' ⊢ Δ' ; 0⟫] ⟪Γ ; Γ' ⊢ Δ' ; Δ⟫
  /-- cut between a linear occurrence of `A` (right) and a central one (left) -/
  | cutL (Λ Γ' Δ' Θ : Multiset Formula) (A : Formula) :
      CutRule [⟪0 ; Γ' ⊢ Δ' ; {A}⟫, ⟪Λ ; A ::ₘ Γ' ⊢ Δ' ; Θ⟫] ⟪Λ ; Γ' ⊢ Δ' ; Θ⟫

/-- `Derivable R P S`: the sequent `S` has a derivation built from rule instances in `R`,
in which *every* sequent satisfies `P`. -/
inductive Derivable (R : List Sequent → Sequent → Prop) (P : Sequent → Prop) :
    Sequent → Prop where
  | mk (ps : List Sequent) (c : Sequent) :
      R ps c → P c → (∀ p ∈ ps, Derivable R P p) → Derivable R P c

/-- All rules of LU, including cut. -/
def LURule (ps : List Sequent) (c : Sequent) : Prop := Rule ps c ∨ CutRule ps c

/-- Provability in LU (cut allowed). -/
def Provable (S : Sequent) : Prop := Derivable LURule (fun _ => True) S

/-- Cut-free provability in LU. -/
def CutFreeProvable (S : Sequent) : Prop := Derivable Rule (fun _ => True) S

/-- The (multiset of all) formulas occurring in a sequent. -/
def Sequent.formulas (S : Sequent) : Multiset Formula := S.L + S.CL + S.CR + S.R

theorem Derivable.mono {R R' : List Sequent → Sequent → Prop} {P P' : Sequent → Prop}
    (hR : ∀ ps c, R ps c → R' ps c) (hP : ∀ S, P S → P' S) {S : Sequent}
    (h : Derivable R P S) : Derivable R' P' S := by
  induction h with
  | mk ps c hr hc _ ih => exact .mk ps c (hR _ _ hr) (hP _ hc) ih

/-- Cut-free provability implies provability. -/
theorem CutFreeProvable.provable {S : Sequent} (h : CutFreeProvable S) : Provable S :=
  Derivable.mono (fun _ _ h => Or.inl h) (fun _ h => h) h

end LU
