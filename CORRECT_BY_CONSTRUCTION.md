# Correctness by construction for `Tm`, `Formula`, `Rule`, `Premise` and `Sequent`

This note answers two questions. What else can be made correct by construction in
`Syntax.lean` and `Calculus.lean`? And can predicate polarities be fixed, for example "the
left linear zone only contains …"?

Section 1 summarizes what the types already guarantee. Section 2 answers the polarity
question and describes what is now implemented (sorry-free) in
`RequestProject/LU/FragmentSyntax.lean`, `FragmentSyntaxInt.lean` and
`FragmentSyntaxTheorem.lean`. Section 3 lists further options with their costs. Sections 2–3
make no change to `Syntax.lean` or `Calculus.lean`: the new files are additive, and the rest
of the development is untouched.

## 1. What is already guaranteed by the types

| Invariant | How |
|---|---|
| Free variables in scope | `Tm TS n`, `Formula PS TS n`: de Bruijn indices `Fin n` |
| Arity of function/predicate symbols | `func f : Tms TS n (TS.arity f) → …`, `atom p : Tms TS n (PS.arity p) → …` |
| Unique representation of atoms | `Tm` / `Tms` are separate mutual types (a tuple is never a term) |
| Quantifier bodies bind exactly one variable | body in `Formula PS TS (n+1)` |
| Eigenvariable condition | `Premise.up` lives in scope `n+1`; context is `sh Γ` / `shc Γ'` |
| Exchange, central contraction | `Multiset` linear zones, `Finset` central zones |
| Context splitting of multiplicative rules | conclusion is literally `Γ + Λ`, `Δ + Θ` |

## 2. Fixing polarities: where it is true, and what is implemented

### 2.1 In full LU no zone has a fixed polarity

Restricting a zone of an LU sequent to one polarity is **not** sound for LU as a whole:

* the identity `A ; ⊢ ; A` puts an *arbitrary* formula into both linear zones;
* the rules `inL` / `inR` move *any* formula into the central zones;
* only the exit rules have polarity conditions: `outL` (only positive formulas leave the
  left central zone) and `outR` (only negative ones leave the right central zone). These are
  conditions on *moves*, not invariants of zones.

LU also needs atoms of all three polarities in one signature. Neutral atoms are needed for
the intuitionistic and linear readings, and positive/negative ones for the classical
reading. So `PredSig` itself must keep a free `predPol`.

Polarity invariants **do** hold for the four *fragments* of §6. Those are exactly the places
where a by-construction type pays off.

### 2.2 Polarity-sliced signatures (`FragmentSyntax.lean`)

* `PS.PredOf q := {p : PS.Pred // PS.predPol p = q}` — the predicate symbols of polarity `q`.
  An atom of a fragment takes its symbol from an allowed slice, so a neutral atom *cannot be
  written* in a classical formula.
* `PS.restrict ok` — the sub-signature of the symbols whose polarity satisfies `ok`
  (`restrict_predPol` gives the guarantee).
* `PolPredSig` — a signature *presented by polarity*, `Pred : Pol → Type`. Setting
  `Pred .neu := Empty` gives a signature with no neutral predicate (`PolPredSig.predPol_ne`).
  `toPredSig` turns it into an ordinary `PredSig`.

### 2.3 Polarity in the type of formulas

The facts "classical formulas are never neutral", "intuitionistic formulas are never
negative" and "neutral intuitionistic formulas are neutral" were previously separate lemmas.
They now become typing facts:

| Fragment | Type | Index | Atoms from |
|---|---|---|---|
| classical | `ClFormula PS TS n c` | `c : CPol` (`pos`/`neg`) | `PredOf c.toPol` |
| intuitionistic | `IntFormula PS TS n c` | `c : IPol` (`pos`/`neu`) | `PredOf c.toPol` |
| neutral intuitionistic | `NFormula PS TS n` | none (always `neu`) | `PredOf .neu` |
| linear | `LinFormula PS TS n q` | `q : Pol` | all symbols |

The constructors compute the index by Tables 1–2 (e.g.
`ClFormula.conj : ClFormula n c → ClFormula n d → ClFormula n (CPol.conj c d)`). For each
fragment we prove:

* `pol_toFormula` — the polarity of the embedded formula equals the index;
* `is…_toFormula` and `exists_of_is…` / `is…_iff` — the image of the embedding is *exactly*
  the predicate `IsClassical`, `IsIntuitionistic`, `IsNeutralInt` or `IsLinear` of
  `Fragments.lean`;
* `ClFormula.toFormula_injective`, `NFormula.toFormula_injective` — the embedding is
  injective (so the intrinsic types are isomorphic to the subtypes);
* `ClFormula.subst`, `LinFormula.subst` with `toFormula_subst` — substitution has a type that
  *says* it preserves polarity.

### 2.4 Sequents of the fragments by construction — the "zone" restrictions

* **Classical (`ClSequent`, stoup presentation).** The left linear zone is a
  `Multiset (ClFormula n .pos)`: only positive formulas. The right linear zone is a
  `Multiset (ClFormula n .neg)`: only negative ones. A separate `Stoup`
  (`empty | left N | right P`) holds the one formula allowed to break this rule. So the
  condition `μ ≤ 1` (at most one negative formula on the left or positive formula on the
  right) holds by construction. This is the kind of statement you suggested: "all formulas
  in the L zone are positive, except the stoup". The central zones hold classical formulas of
  any polarity.
* **Intuitionistic (`IntSequent`).** `Γ;Γ' ⊢ ;A` with fields `L`, `CL` and a single `goal`.
  There is no right central zone, and the right linear zone is a single formula.
* **Neutral intuitionistic (`NIntSequent`).** `L : Option (NFormula n)`, so there is at most
  one linear left formula.
* **Linear (`LinSequent`).** All four zones hold `LinFormula`s.

Main theorems (`range_toSequent`): for every LU sequent `S`,

```
ClassicalSeq S  ↔ ∃ T : ClSequent  PS TS n, T.toSequent = S
IntSeq S        ↔ ∃ T : IntSequent PS TS n, T.toSequent = S
NeutralIntSeq S ↔ ∃ T : NIntSequent PS TS n, T.toSequent = S
LinearSeq S     ↔ ∃ T : LinSequent PS TS n, T.toSequent = S
```

and (`FragmentSyntaxTheorem.lean`, `*.cutFree_within`): a cut-free LU proof of
`T.toSequent` can be replaced by a cut-free proof in which **every** sequent is the image of
an intrinsic sequent of the same fragment. This is §6's theorem restated with the
intrinsic types. It uses only the standard axioms, and not the unproved `cut_elimination`.

## 3. Further options (not implemented), with costs

1. **Polarity-indexed `Formula` for the whole of LU.** Extend `LinFormula` with the
   constructors of Table 2 (`conj : Formula n p → Formula n q → Formula n (Pol.conj p q)`,
   …). Rule side conditions such as `(P : Formula n) (hP : P.pol = .pos)` then become argument
   types `(P : Formula n .pos)`, and `Formula.pol` disappears as a function. Zones become
   multisets of `Σ q, Formula n q`. `LinFormula` is a working prototype of this. Cost: every
   file of the development changes. Pattern matching on formulas with computed indices
   (`Pol.conj p q`) needs care: `cases` fails on non-variable indices, which is why
   `toFormula_injective` is stated on `Σ`-pairs.
   *Cheap variant:* `abbrev PFormula n q := {A : Formula n // A.pol = q}`, used only in rule
   parameters. This is mostly cosmetic.
2. **Rules with a fixed number of premises.** `Rule : List (Premise n) → Sequent n → Prop`
   allows any list length in principle. Indexing by arity (`Fin k → Premise n`, or
   `Rule₀`/`Rule₁`/`Rule₂`) records in the type that LU rules have 0, 1 or 2 premises.
   Low cost, low gain.
3. **Derivations as data.** Replace the `Prop`-valued `Derivable` with a `Type`-valued
   `Proof R P S` (trees whose nodes are rule instances). This gives height and size measures,
   structural recursion on proofs, and executable proof transformations. It is the natural
   basis for the still-missing `cut_elimination`. Medium cost; `Derivable` becomes
   `Nonempty (Proof …)`.
4. **Intrinsic calculi for the fragments.** Define `ClRule : List ClSequent → ClSequent →
   Prop` directly (an LC-style calculus on stoup sequents), and similarly for the other
   fragments. Then prove that it is equivalent to LU restricted to the fragment. This would
   be the full correct-by-construction version of §6's theorem; `cutFree_within` is its
   first half. High cost: Fig. 3 has many polarity-split rules.
5. **Rules whose linear context must be empty** (`bangR`, `questL`, `conjR_AQ` premise
   `⟪0 ; Γ' ⊢ Δ' ; {A}⟫`, …). A dedicated constructor `Sequent.central Γ' Δ' A` for
   "`; Γ' ⊢ Δ' ; A`" would name this shape. This is cosmetic.
6. **Many-sorted terms.** A `TermSig` with sorts would make ill-sorted terms impossible.
   This is not needed for Girard's paper.
