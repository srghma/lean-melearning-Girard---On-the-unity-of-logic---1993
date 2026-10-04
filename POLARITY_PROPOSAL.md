# Proposal: deriving polarity instead of postulating it

**Status:** design proposal only. No Lean code has been changed. Statements marked
**(in project)** are existing, sorry-free theorems. Everything else is a target, a conjecture,
or an informal argument and is labelled that way.

## 0. Where we are today, and the question "derive from *what*?"

The formalization currently treats polarity as **primitive data**:

| Ingredient | Today | File |
|---|---|---|
| Atom polarity | field `Pred.pol`, chosen freely | `Syntax.lean` |
| Constants, `!`, `?`, `¬`, `∀`, `∃` | fixed clauses in `Formula.pol` | `Syntax.lean` |
| Linear connectives (Table 1) | lookup functions `Pol.tensor`, `Pol.par`, … | `Syntax.lean` |
| Chimeric connectives (Table 2) | lookup functions `Pol.conj`, `Pol.disj`, `Pol.imp`, `Pol.iimp` | `Syntax.lean` |

So "deriving polarity" can mean deriving any of these four layers from something more
basic. The paper itself suggests several candidate sources:

* **(S1) Linear decomposition.** Table 3 rewrites `∧, ∨, ⇒, ⊃, ∀, ∃` in linear logic.
* **(S2) A generated class.** §1 item 3 says the formulas that can cross the left
  semicolon both ways *"are closed under ⊗, ⊕ and ⋁x"*.
* **(S3) Structural behaviour / provability.** A positive formula has left structural
  rules (it behaves like `!A`), and a negative one has right structural rules (like `?A`).
  In LU this is the permeability rule. In LL it is `P ⊢ !P` and `?N ⊢ N` (§4, "easy inductive
  argument").
* **(S4) Substitution.** An atom's polarity says which formulas may be substituted for it
  (§6, substitution property).
* **(S5) Denotational semantics.** §2 says a positive formula denotes a positive correlation
  space and a negative one a negative correlation space.
* **(S6) Focusing / reversibility.** This is not in the paper, but it is the modern meaning
  of "polarity" (Andreoli, and Girard's later work). §6 below compares it.

The recommendation (§7) is a layered plan:

* Table 2 from S1: cheap, and essentially already proved.
* Table 1 from S2: cheap.
* Atom polarity from S4 together with the `!p₀`/`?p₀` reading: already proved.
* A soundness and optimality theorem tying all of this to S3: the substantive new work.
* S5 left as a remark.
* S6 as a documented contrast.

---

## 1. Layer A: Table 2 derived from Table 1 via Table 3 (source S1)

**Idea.** Remove the four Table 2 functions as primitive definitions and *define*

```lean
def Formula.polDerived (A : Formula n) : Pol := A.toLinear.pol   -- uses Table 1 only
```

Then make Table 2 a theorem.

**What already exists (in project).** `Formula.pol_toLinear : A.toLinear.pol = A.pol`
(`Translation.lean`). This *is* the statement that Table 2 is determined by Table 1 and
Table 3. The definitions just need to be inverted.

**Subtlety: circularity.** `toLinear` itself pattern-matches on `A.pol` and `B.pol` to choose
the micro-connective (`conjLin a b`, …), so `polDerived` cannot be defined naively. Two clean
fixes:

1. Define `toLinear` and `polDerived` by **mutual recursion**, returning a pair
   `(linear formula, its polarity)`. The pair's second component is the derived polarity, and
   Table 2 becomes the lemma `polDerived (conj A B) = Pol.conj A.polDerived B.polDerived`,
   proved by `cases` on the nine cases.
2. Keep `Formula.pol` restricted to the *linear* constructors (Table 1), and define
   `chimeric` formulas as a separate syntax that elaborates into linear formulas. This is
   heavier and changes all the calculus files, so it is not recommended.

**Cost:** low (about 50–100 lines). It touches only `Syntax.lean` and `Translation.lean`,
because downstream files use `pol` through its simp lemmas.

**Gain:** the nine-entry tables `Pol.conj`, `Pol.disj` and `Pol.imp` stop being something a
reader has to trust. This is exactly how §5 of the paper motivates them ("chimeras").

---

## 2. Layer B: Table 1 derived from generators and closure (source S2)

**Idea.** Follow §1 item 3 literally: positivity is the *least* class of formulas
containing the obviously duplicable ones and closed under the operations that preserve
duplicability. Negativity is the dual class.

```lean
inductive IsPos : Formula n → Prop
  | atom  : p.pol = .pos → IsPos (atom p ts)
  | one   : IsPos one
  | zero  : IsPos zero
  | bang  : IsPos (bang A)
  | tensor : IsPos A → IsPos B → IsPos (tensor A B)
  | plus   : IsPos A → IsPos B → IsPos (plus A B)
  | lex    : IsPos A → IsPos (lex A)
  | neg    : IsNeg A → IsPos (neg A)
-- IsNeg: generators ⊥, ⊤, ?A, negative atoms; closed under ⅋, &, ⋀x, and ¬ of IsPos
--   plus a constructor `lolli : IsPos A → IsNeg B → IsNeg (lolli A B)`, since `⊸` is a
--   primitive constructor of `Formula` (it is A⊥ ⅋ B)
```

The two predicates are mutually inductive. Then *define*
`pol A := if IsPos A then .pos else if IsNeg A then .neg else .neu`
(both predicates are decidable by structural recursion), and prove:

* **Target B1 (Table 1 recovered).** For every linear connective, `pol` computed this way
  equals the current `Pol.tensor`, `Pol.par`, and so on. This is a finite case check.
* **Target B2 (no overlap).** `¬ (IsPos A ∧ IsNeg A)`. The paper's "polarity 0 is not
  shared" decision in §2 becomes a lemma rather than a convention. Proof: induction, using
  the fact that the generators are disjoint.

**Cost:** low to medium. **Gain:** Table 1 becomes "the closure of the generators under the
operations that preserve the structure", which is the paper's own explanation. Combined with
Layer A, the only primitive polarity data left are atom polarities and the generators.

---

## 3. Layer C: atom polarity derived from neutral atoms (sources S4 and S3)

The paper says atoms "are given with their polarity". The project already shows that this
datum can be eliminated in two ways.

* **Through `!`/`?` (in project).** `Table3Soundness.lean` reads a positive atom `p` as
  `!p₀` and a negative one as `?p₀`, where `p₀` is the same symbol declared neutral
  (`Formula.atomLL`). `pol_atomLL` shows that this reading has the declared polarity, and
  `LL.of_provable_table3` shows that every LU rule is sound under it. So a polarized
  atom is *derivable* as an exponential applied to a neutral atom, and the soundness of the
  whole calculus survives.
* **Through substitution (in project).** `Substitution.lean` (`pol_substPred`,
  `ProvableWithin.substPred`, …) shows that an atom of polarity `π` can be replaced by any
  formula of polarity `π`. Read backwards, this says *the polarity of an atom is the
  declaration of the class of formulas it ranges over*. That is a type for the atom, not a
  property of it.

**Proposal.** Document these two theorems together as "atom polarity is derived". An optional
refactor would make `Pred` polarity-free and add `!`/`?` wrappers in the syntax. That is not
recommended: it would break the fragment definitions (the classical fragment needs
polarized atoms) for no gain in content.

---

## 4. Layer D: polarity characterized by structural behaviour (source S3), the substantive part

This is the real "derivation from meaning": polarity should be *whatever lets a formula
undergo structural rules*. Define the semantic classes, for linear formulas with neutral
atoms:

```lean
def SemPos (A : Formula n) : Prop := LL true {A} {bang A}    -- A has left weakening + contraction
def SemNeg (A : Formula n) : Prop := LL true {quest A} {A}
```

(Equivalently: `A ⊢ 1` and `A ⊢ A ⊗ A` are provable. Proving the equivalence would be a small
target in its own right.)

### D1. Soundness: syntactic ⇒ semantic **(in project)**
`Formula.IsNeutralLinear.bang_quest` (`LinearEquiv.lean`):
`A.pol = .pos → LL true {A} {bang A}` and `A.pol = .neg → LL true {quest A} {A}`.
`pos_toLL` and `neg_toLL` extend this to all LU formulas through Table 3.

### D2. Completeness fails: semantic ⇏ syntactic (informal, not yet formalized)
Polarity is *syntactic* and is not invariant under provable equivalence. The paper says
so itself (§2: `(A ⊗ 1) ⅋ ⊥` "changes the polarity to 0"). Candidate witness:

* `A := (1 ⊗ 1) ⅋ ⊥`. Table 1 gives `par pos neg = neu`.
* But `A ⊣⊢ 1` in LL, hence `A ⊢ !A` (from `⊢ A`, promotion gives `⊢ !A`; then `A ⊢ 1` and
  `1 ⊢ !A`, followed by a cut).

Formalizing this witness is easy: it only needs *provability*, which we have, so the
negation of `SemPos A → A.pol = .pos` is a short Lean proof. **Proposed target D2.**

So polarity **cannot** be defined as `SemPos`. That would make it undecidable (first-order LL)
and not compositional, and the LU rules depend on polarity being checkable on the syntax.

### D3. Optimality: Table 1 is the *best compositional* approximation (conjecture)
The right statement is that Table 1 is forced:

> **Conjecture D3.** Among functions `f : Pol → Pol → Pol` (one per connective) such that
> "`A.pol = π`, `B.pol = ρ`, `f π ρ = pos` ⇒ `SemPos (A ∘ B)`" (and dually for `neg`) holds
> for *all* formulas, Table 1 is pointwise maximal: every entry `neu` in Table 1 has a
> witness pair `(A, B)` with `A ∘ B` neither `SemPos` nor `SemNeg`.

Candidate witnesses (unchecked):

* `tensor pos neu`: `1 ⊗ p` with `p` a neutral atom, since `1 ⊗ p ⊣⊢ p` and `p ⊬ !p`.
* `tensor neg neg`: `?p ⊗ ?q`.
* Similar witnesses for `⊕`, `⅋`, `&` and `⋁`.

**Difficulty:** each witness needs an **unprovability** proof in LL. We cannot get it from
cut-free search, because LL cut elimination is not proved in this project (it is the
hypothesis `LLCutElimination`). The options are:

* (a) prove LL cut elimination first, which is large;
* (b) build a small **phase-semantics countermodel**: soundness of LL in phase spaces
  is a few hundred lines, and each witness then needs one finite monoid;
* (c) state D3 *assuming* `LLCutElimination` and use the cut-free proof search.

Recommendation: (b), because it is self-contained and reusable.

D1 + D2 + D3 together give the precise sense in which polarity is derived from structural
behaviour. It is the decidable, compositional under-approximation of "having structural
rules", and it is the best such approximation.

### D4. The LU-internal version (optional)
Inside LU itself, S3 is the permeability rules of `Calculus.lean`: a positive formula may
leave the central zone on the left, and a negative one on the right. An LU analogue of
`SemPos` would be "the left-exit rule for `A` is admissible". The analogue of D1 is immediate
(the rule is primitive for positive `A`), and D2 and D3 transfer through `provable_iff_LL`
for neutral-atom linear sequents.

---

## 5. Source S5: denotational semantics (out of scope, remark only)

§2: a positive formula denotes a coherent space *with a canonical positive correlation
structure* (it generalizes `!X`), and dually for negative formulas. Table 1 then reads
as "the construction on coherent spaces lifts canonically to correlation spaces". This is the
semantic counterpart of Layer B and D3. Formalizing it would need coherence spaces, the
correlation spaces of Girard's *A new constructive logic: classical logic*, and the
interpretation of LL. That is far larger than the rest of the project, so it is not proposed
here.

---

## 6. Contrast with focusing polarity (source S6)

The modern notion, from Andreoli's focusing, assigns polarity to the **head connective
only**: `⊗, ⊕, 1, 0, ∃, !` are positive (their right rules are irreversible) and
`⅋, &, ⊥, ⊤, ∀, ?` are negative (their right rules are reversible).

| | LU polarity (this paper) | Focusing polarity |
|---|---|---|
| Determined by | the whole formula (hereditary) | the head connective |
| `p ⊗ q`, `p` neutral | neutral | positive |
| Meaning | structural rules allowed | rule reversibility |
| Number of values | three (with neutral) | two |

The two notions agree on the generators (`!` and `1` positive, `?` and `⊥` negative) but are
**not** derivable from each other: roughly, LU positivity is a *hereditary* version of
focusing positivity, which stops at atoms and at `!`-subformulas. A useful small theorem to
record would be:

> **Target S6.** If `A.pol = .pos` and `A` contains no `¬` or `⊸`, then every connective on
> the path from the root of `A` to an atom or a `!`-subformula is focusing-positive
> (and dually for negative formulas).

This would pin down the relation precisely. It follows directly from Layer B.

---

## 7. Recommended plan

| Step | Content | New Lean | Risk |
|---|---|---|---|
| 1 | Layer A: `polDerived` by mutual recursion with `toLinear`; Table 2 as a lemma | ~100 lines | low |
| 2 | Layer B: `IsPos`/`IsNeg` inductive; Table 1 and the no-overlap lemma as theorems | ~150 lines | low |
| 3 | Layer C: documentation only (already proved) | 0 | none |
| 4 | D2: the `(1 ⊗ 1) ⅋ ⊥` witness (semantic ⇏ syntactic) | ~50 lines | low |
| 5 | Phase-semantics soundness for LL | ~400 lines | medium |
| 6 | D3: optimality witnesses for every `neu` entry of Table 1 | ~200 lines | medium (finding the witnesses) |
| 7 | Target S6: relation to focusing polarity | ~80 lines | low |

Steps 1–4 are independent of the open `cut_elimination` and could be delivered together.
Steps 5–6 give the conceptual payoff: they show that Girard's tables are not arbitrary,
because no compositional assignment can be more generous. Remark (ii) and correlation
spaces (S5) stay out of scope.

**Answer to "derive polarity from what?"** The connective tables can be derived: Table 2 from
Table 1 via Table 3, and Table 1 from the generators `1, 0, !` and `⊥, ⊤, ?` via closure.
Atom polarity reduces to neutral atoms plus `!`/`?`. The *justification* of the whole scheme
is structural behaviour (`P ⊢ !P`, `?N ⊢ N`). Polarity is sound for it (proved), not complete
for it (easy to show), and, conjecturally, its optimal compositional approximation.
