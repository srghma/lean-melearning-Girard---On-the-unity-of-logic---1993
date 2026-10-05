# Summary of changes for run 14b89ece-1774-462c-adc8-4eaed4ef30bd
**Short answer to your polarity question:** in full LU no zone can be limited to a fixed polarity. Such limits only hold inside the four fragments of §6, and I've now built those limits into the types there.
- In full LU, the identity rule `A ; ⊢ ; A` puts any formula into both linear zones, and `inL`/`inR` let any formula into the middle zones. The only polarity conditions (`outL` for positive, `outR` for negative) restrict which formulas may leave a zone; they don't say what a zone contains.
- LU also needs atoms of all three polarities in one signature, so `PredSig` has to keep a free `predPol`.

All new code builds with no `sorry` and uses only the standard axioms. It is in three new files; `Syntax.lean`, `Calculus.lean` and the rest of the development are unchanged.

**Atoms of a fixed polarity** (`RequestProject/LU/FragmentSyntax.lean`)
- `PS.PredOf q` is the type of predicate symbols of polarity `q`.
- `PS.restrict ok` is the sub-signature of symbols whose polarity satisfies `ok`.
- `PolPredSig` gives a signature by polarity (`Pred : Pol → Type`); setting `Pred .neu := Empty` gives a signature with no neutral predicates.

**Polarity built into each fragment's formula type.** Each constructor computes the polarity from Tables 1–2, and atoms can only come from the allowed polarities, so for example a neutral atom cannot be written in a classical formula:
- `ClFormula PS TS n c`: classical formulas, with `c` either positive or negative (classical formulas are never neutral).
- `IntFormula`: intuitionistic formulas, positive or neutral (never negative).
- `NFormula`: neutral intuitionistic formulas, always neutral.
- `LinFormula PS TS n q`: linear formulas, any polarity. This is a working model of what a polarity-indexed `Formula` for all of LU would look like.

For each of these I proved:
- `pol_toFormula`: the LU polarity of the embedded formula equals the type's polarity index.
- `*_iff`: the embedding produces exactly the formulas accepted by `IsClassical`, `IsIntuitionistic`, `IsNeutralInt` and `IsLinear`.
- Injectivity of the classical and neutral embeddings, and substitution that by its type preserves polarity (classical and linear).

**Zone limits by construction — the kind of rule you suggested**
- **`ClSequent`:** the left linear zone holds only positive formulas and the right linear zone only negative ones. A separate `Stoup` slot (`empty | left N | right P`) holds the one formula allowed to break this, so the condition `μ ≤ 1` holds by construction.
- **`IntSequent`:** the shape `Γ;Γ' ⊢ ;A`, with no right middle zone and a single formula on the right.
- **`NIntSequent`:** the left linear zone is an `Option`, so it holds at most one formula.
- **`LinSequent`:** all four zones hold linear formulas.

Two results tie these types back to the existing development:
- **`range_toSequent`** (four versions, in `FragmentSyntax.lean` and `FragmentSyntaxInt.lean`): for example, `ClassicalSeq S ↔ ∃ T : ClSequent PS TS n, T.toSequent = S`. The new sequent types give exactly the fragment sequents defined in `Fragments.lean`, no more and no less.
- **`*.cutFree_within`** (`FragmentSyntaxTheorem.lean`): the §6 theorem restated with the new types. A cut-free proof of a fragment sequent can be replaced by one in which every sequent comes from that fragment's new sequent type. This does not depend on the unproved `cut_elimination`.

**What else could be done:** `CORRECT_BY_CONSTRUCTION.md` explains the above and lists further options, none of which I implemented, with their costs:
- a polarity-indexed `Formula` for all of LU, so rule side conditions like `hP : P.pol = .pos` become argument types (expensive: every file changes);
- rules with a fixed number of premises (0, 1 or 2);
- proofs as data rather than a `Prop`, which is the natural basis for cut elimination;
- separate calculi for each fragment that work directly on the new sequent types;
- a named shape for sequents with an empty linear context;
- many-sorted terms (not needed for the paper).

`LU_FORMALIZATION.md` has a new row pointing to these files.

# Summary of changes for run 73e141c1-5d94-47a5-89ce-1b1c7aab605b
**Short answer: yes. Whatever polarity you give the predicate symbols, LU cannot derive falsity.** This is now proved in Lean, in the new file `RequestProject/LU/Consistency.lean`. It builds with no `sorry`, uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and does not depend on the unproved `cut_elimination`.

**Cut elimination is still open.** It was the only remaining `sorry`, and it is still unproved. Of the earlier results, only `fragment_theorem` (the §6 theorem for proofs with cuts) depends on it. Girard also only claims it ("more or less obvious, but perhaps a bit too long to write down"). I did not attempt it in this session, because a proof for this calculus is very long. The calculus has about 90 rules, and a positive formula on the right can meet a copy of itself in the left middle (classical) zone while the surrounding linear formulas cannot be copied. Handling that needs, for each positive connective and mirrored for each negative one, a separate result about splitting formulas in the middle zones. On top of that come cut-permutation steps against every rule and a substitution lemma for proofs. This is a separate, much larger project.

**How the polarity result is proved**
- **Polarity-free meaning:** formulas get an ordinary true/false reading in any structure (any domain, including an empty one), ignoring polarity and linearity:
  - ⊗, &, ∧ mean "and"; ⅋, ⊕, ∨ mean "or";
  - ⊸, ⇒, ⊃ mean "implies"; ¬ means "not";
  - !A and ?A both mean A; 1 and ⊤ are true, 0 and ⊥ are false;
  - ⋀ and ∀ mean "for all"; ⋁ and ∃ mean "there exists".
- **Valid sequents:** \(\Gamma ; \Gamma' \vdash \Delta' ; \Delta\) is valid if, for every value of the variables, everything in \(\Gamma, \Gamma'\) being true makes something in \(\Delta', \Delta\) true.
- **Every rule is sound:** `Rule.sound` checks every rule of Figures 1–3, and `CutRule.sound` checks the three cut rules. None of these proofs uses a polarity side condition. This is the key point: the polarity of an atom only decides which rules may be applied, and every rule is sound regardless.
- **Every provable sequent is valid** (`Provable.valid`), in every structure, with cuts allowed.

**What follows from it**

Each of these holds for every signature, so for every choice of `predPol`:
- `not_provable_empty`: the empty sequent `; ⊢ ;` is not provable.
- `not_provable_zero` and `not_provable_bot`: `; ⊢ ; 0` and `; ⊢ ; ⊥` are not provable.
- `not_provable_atom`: no atom \(p(t_1,\dots,t_k)\) is provable, whatever polarity \(p\) has.
- `not_provable_and_neg`: no formula is provable together with its negation.
- `consistent_for_every_polarity` puts these together for fixed predicate symbols with an arbitrary polarity function `pol : Pred → Pol`.

This complements the existing `LL.of_provable_table3`, which shows that any polarity assignment is also sound for the Table 3 reading in linear logic.

The full project builds, `LU_FORMALIZATION.md` has the new entries, and the Properties table now lists the semantics, the soundness theorem and the consistency theorem (both proved). Everything is committed.

# Summary of changes for run 8aa19667-53b5-4f9e-9dd5-f773b04dad50
I implemented `SIGNATURE_ASSESSMENT.md` with the mutual `Tm`/`Tms` pair, and the whole development now works over any signature. After a clean rebuild the project compiles. The only `sorry` is still `cut_elimination`, which the paper also only claims. The main theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); `fragment_theorem` still depends on the `sorry`.

**New syntax (`RequestProject/LU/Syntax.lean`)**
- **Signatures:** `TermSig` has fields `Func` and `arity`. `PredSig` has fields `Pred`, `arity` and `predPol`, so an atom's polarity is `PS.predPol p`.
- **Terms and tuples:** the mutual pair is `Tm TS n` (terms: `var`, `func f (ts : Tms TS n (TS.arity f))`) and `Tms TS n k` (`k`-tuples: `nil`, `cons`). Since a tuple is never a term, atoms `atom p (ts : Tms TS n (PS.arity p))` have one representation each.
- **Term operations:** renaming, substitution, the component accessor `Tms.get` and all composition lemmas are defined and proved by mutual structural recursion. Decidable equality of terms needs `[DecidableEq TS.Func]`.
- **Formulas:** `Formula PS TS n` has decidable equality (`Formula.decEq`) given `[DecidableEq PS.Pred]` and `[DecidableEq TS.Func]`. One limitation: this equality cannot be evaluated by `decide`, so concrete formula comparisons have to be proved another way.
- **No default term:** there is no fixed default term any more. `Formula.shift_injective` is now proved from injectivity of renaming, so a signature without constants is fine.

**Rest of the development**
- Every file takes `{PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]` as section variables. `Sequent PS TS n` and `Premise PS TS n` are indexed by the signatures.
- `CutElimination PS TS` and `LLCutElimination PS TS` take the signatures explicitly.
- Theorems that don't need decidable equality leave those instance arguments out (via `omit`), so they don't carry unused assumptions.
- **Substitution for an atom (`Substitution.lean`):** now stated for `a : PS.Pred`, with `A : Formula PS TS (n + PS.arity a)`.
- **The example in `MultiplicativeReading.lean`:** now uses a concrete signature, `multPS` (two nullary positive predicates) and `multTS` (no function symbols).
- **Table 3 soundness (`Table3Soundness.lean`):** the old code built "`p` declared neutral" as a new symbol, which an arbitrary signature doesn't provide. Instead, a positive atom `p` is now read as `!p` and a negative one as `?p`. This is sound because the linear logic rules never look at atom polarities. To support it, `LinearEquiv.lean` gains `Formula.IsGuardedLinear`: linear formulas whose atoms are neutral except under `!`/`?`. The paper's "easy inductive argument" is now proved for this wider class (`IsGuardedLinear.bang_quest`), and the old `IsNeutralLinear.bang_quest` follows from it. As a result, `LL.of_provable_table3`, `provable_iff_LL` and `cutFreeProvable_of_LLCutElimination` need no extra condition on the signature.

**Unchanged:** the statements about rules, fragments, the §6 theorem, LJ, LK and the §4 equivalence are the same, apart from the added signature parameters.

**Documentation:** `LU_FORMALIZATION.md` is updated, and `SIGNATURE_ASSESSMENT.md` has a "Status: implemented" note at the top. `RequestProject/SignatureAssessment.lean` is kept unchanged as the record of the assessment.

**Properties table:** I updated the rows I could reach: the term, formula, sequent and polarity definitions, plus `fragment_theorem_cutFree`, `fragment_theorem`, `cut_elimination`, `provable_iff_LL`, `LL.of_provable_table3` and `neutral_headVariable`. Other older rows (for example the substitution, LJ/LK and multiplicative-reading results) could not all be reached in this session. Their statement snippets may still show the old `Formula n` / `Term n` syntax, even though the proofs build. Everything is committed.

# Summary of changes for run 83044bfd-c794-4b10-b631-1fb5b9ffb9e0
Both changes are done and the whole project builds. The only `sorry` is still `cut_elimination` in `MainTheorem.lean`.

**On your signature proposal: taking `Func` and `Pred` from an external signature is correct, but the `Term` family as you wrote it is not.** The index `1` is meant to mean "a term", but `cons t nil : Term TS n 1` is also a 1-tuple, so:
- **An atom has two forms.** For a unary predicate `p`, `atom p (var 0)` and `atom p (cons (var 0) nil)` are two different formulas that both read `p(x)`. This breaks formula equality, the identity rule and the finite-set central zones.
- **Junk terms exist.** For example `cons (cons (var 0) nil) nil` is accepted as a term.
- **Matching has to handle it.** Any function on terms must deal with `cons` against `var`/`func`; Lean's coverage check rejects those cases as missing.

Two corrected versions both compile:
- **(A)** keep the current shape, parameterised by the signature: `func (f : TS.Func) : (Fin (TS.arity f) → Term TS n) → Term TS n`, and atoms take `Fin (PS.arity p) → Term TS n`.
- **(B)** keep tuples but separate them from terms, e.g. with an `Option ℕ` index (`none` = term, `some k` = `k`-tuple) or a mutual `Tm`/`Tms` pair.

Switching to either would also need:
- `[DecidableEq TS.Func]` and `[DecidableEq PS.Pred]` instance arguments, because the central zones are finite sets.
- Dropping the fixed default term: a signature may have no constants, so the one place that uses it (`shift_injective`) needs a renaming-injectivity proof, which I checked works.
- Restating the concrete atoms in `MultiplicativeReading.lean` and the predicate substitution in `Substitution.lean` over a signature.

The checks are in `RequestProject/SignatureAssessment.lean`: `Proposed.atom_two_representations`, `Proposed.Term.rename_injective`, `FixedA`, `FixedB`, `FixedB.unary_tuple`. It builds without `sorry` and is not imported by the main development. The full write-up is in `SIGNATURE_ASSESSMENT.md`. I haven't changed `Syntax.lean`.

**1. Central zones `CL`, `CR` are now `Finset`s.**
- **Rules:** a central formula is added with `insert`, empty zones are `∅`, and eigenvariable premises use `shc Γ' = Γ'.image Formula.shift`. `weakR`/`weakL` are kept. `contrR`/`contrL` are commented out in `Calculus.lean` with a note: in a finite set, `insert A (insert A Δ')` is `insert A Δ'`, so contraction is built in.
- **Statements that changed:**
  - The LK and LJ translations and the Table 3 soundness theorem now use `S.CL.val` / `S.CR.val`.
  - `LJ.provable` now concludes `Provable ⟪0 ; Γ.toFinset ⊢ ∅ ; {C}⟫`.
  - Linear-only sequents are written `⟪Γ ; ∅ ⊢ ∅ ; Δ⟫`.
- **Proofs:** LK, LJ and the linear-logic side now do the contraction or weakening themselves when a formula enters or leaves a central zone. `shc_val` (with `shift_injective`) moved into `Calculus.lean` so the LJ and LK files can use it.

**2. `Sequent` is indexed by its scope**, as `structure Sequent (n : ℕ)`. Rule premises are `Premise n` (`.same` for scope `n`, `.up` for scope `n + 1` in eigenvariable rules). `Rule`, `CutRule` and `Derivable` follow design (b), with `P : ∀ {n}, Sequent n → Prop`.

I also updated the header of `Calculus.lean` and `LU_FORMALIZATION.md`, removed six unused simp arguments, and updated the Properties table to the new statements; the previously proved results there use only the standard axioms. `ARISTOTLE_SUMMARY.md` is untouched and everything is committed.

## Suggested follow-up

If you like, I can move the whole development to external signatures using the corrected term representation (A) or (B) from `SIGNATURE_ASSESSMENT.md`, and add the decidable-equality instance arguments that the finite-set central zones need.

# Summary of changes for run 22dfe6ee-b07a-465f-8592-5e7605b89f0e
I wrote `POLARITY_PROPOSAL.md`, a design proposal for deriving polarity instead of taking it as given. I didn't change any Lean code, and I added nothing new to Lean, so the proposal's new claims are not machine-checked.

Your question ended in "…WHAT", so I read it as "what could polarity be derived from?". The file answers that in layers:

- **Table 2 from Table 1 via Table 3.** The project already proves `pol_toLinear`. The proposal is to define polarity from the linear decomposition, computing the formula and its polarity together so the definition isn't circular. Table 2 then becomes a lemma.
- **Table 1 from a generated class.** Section 1 of the paper describes the positive formulas as a closure: start from positive atoms, `1`, `0` and `!A`, and close under `⊗`, `⊕`, `⋁x` and `¬` of negative formulas (negative formulas are the dual). Using two inductive predicates for these classes, Table 1 and the paper's "no shared polarity" choice both become theorems.
- **Atom polarity from neutral atoms.** No new proof is needed. Two existing results already do this:
  - reading a positive atom as `!p₀` and a negative one as `?p₀` (`atomLL`, `pol_atomLL`), with every LU rule sound under that reading (`LL.of_provable_table3`);
  - the substitution theorems, which make an atom's polarity say which formulas may be substituted for it.
- **Justification from structural behaviour:** "positive" means the formula has structural rules on the left (it behaves like `!A`), "negative" the same on the right (like `?A`). There are three parts:
  - **Soundness (already proved):** a positive formula proves its own `!`-version and a negative one is proved by its `?`-version (`IsNeutralLinear.bang_quest`).
  - **Completeness fails (not yet in Lean):** `(1⊗1)⅋⊥` is neutral by Table 1 but equivalent to `1`, so it still has the structural behaviour. Polarity therefore can't be *defined* by provability; it is deliberately syntactic and decidable.
  - **Optimality (conjecture):** no compositional table can be more generous than Table 1. I give candidate witnesses, but checking them needs proofs that certain sequents are unprovable, so I suggest a small phase-semantics countermodel.
- **Remark and contrast:** the paper's semantic explanation (correlation spaces) is noted as out of scope. The modern focusing notion of polarity, which depends only on the head connective, is compared with LU's hereditary polarity, with a small proposed theorem relating the two.

The file ends with a seven-step plan with rough sizes. Steps 1–4 don't depend on the open `cut_elimination` proof. The file is committed.

# Summary of changes for run eced67a5-8751-45ef-81b9-f4a89871abea
I made no changes, as you asked. These answers are based on the current `RequestProject/LU/Calculus.lean` and `Syntax.lean`.

## 1. Making the central zones `CL` and `CR` Finsets

**Yes, contraction comes for free, but weakening does not.** In a Finset, `insert A (insert A Γ') = insert A Γ'`. So once `::ₘ` becomes `insert` in the central zones, the premise and conclusion of `contrR` and `contrL` are the same sequent. The rules become `Rule [S] S`: harmless, so you could simply delete them. Keep `L` and `R` as multisets, because the linear zones must not contract (`A ⊗ A` is not `A`). Weakening stays a real rule: `ax`, `topR`, `zeroL`, `oneR` and `botL` require an empty central zone (`0`), so `weakL`/`weakR` are still needed. You could drop them only if you also allowed an arbitrary central context in the zero-premise rules, which departs further from the paper's Fig. 1.

**Provability is unchanged.** Weakening and contraction are both available in the central zone, so a sequent is provable with Finsets exactly when it is provable with multisets. Two points work in your favour: central contexts are always shared between premises, never split, so the Finset version never needs a "split a set" operation; and a set-valued unbounded zone is a standard design (Andreoli's focused sequents use one).

**Costs:**
- **Decidable equality:** Finset needs `DecidableEq (Formula n)`. `Term` and `Formula` don't derive it today, because `Term.func` and `atom` take `Fin k → Term n`. You can write the instance by hand (the domain is finite) or use classical decidability.
- **Harder case analysis on rules:** this is the main cost. With multisets, `A ::ₘ Γ' = X` determines `Γ' = X.erase A`. With sets, `insert A Γ' = X` allows `Γ'` either to contain `A` or not, so every proof that does case analysis on a rule instance gets extra cases. That affects the invariants in `Intuitionistic.lean` and `Classical.lean`, the absorption lemmas, and the `LJ`/`LK`/`LL` translations.
- **Other rewrites:** `sh` becomes `Finset.image shift`, which is fine since `shift` is injective. `Sequent.formulas` and the `!Γ'`/`?Δ'` translations go through `.val`.
- **Hidden contractions:** rules like `inL`, `outR`, `bangL` and `cutL` silently contract when the formula is already in the set, so the multiset-to-set correspondence of derivations is not one-to-one.

**When it pays off:** mainly for the one open proof, `cut_elimination`. Built-in contraction, ideally together with an arbitrary central context in the zero-premise rules, removes the usual contraction-versus-cut problem. For the results already proved, it is mostly rework with no gain.

## 2. Indexing `Sequent` by scope instead of storing it as a field

**`structure Sequent (n : ℕ)` itself makes sense.** It matches `Formula n`. It removes the `S.scope` projections (about 25 uses), for example `A : Formula (S.scope + a.arity)` becomes `A : Formula (n + a.arity)`. It also makes `Sequent.subst : Subst n m → Sequent n → Sequent m` and `sh : Sequent n → Sequent (n+1)` typed operations. Finally, equalities between sequents become ordinary rather than dependent: today, equating two `Sequent.mk n …` values can produce dependent-type (`HEq`) side conditions.

**But `Rule : List (Sequent n) → Sequent n → Prop` does not work as stated.** Four rules have their premise one scope up: `lallR`, `lexL`, `callR_A` and `callR_N` take a premise in `Sequent (n+1)` and conclude a `Sequent n`. A homogeneous list cannot express them. That is why the previous design made the scope a field: the current `Sequent` is the same thing as `Σ n, Sequent n`. Ways to do it:
- **(a) Heterogeneous premises:** `Rule : {n : ℕ} → List (Σ m, Sequent m) → Sequent n → Prop`. This is the smallest change, but it is close to the current design.
- **(b) A precise premise type:** `inductive Premise (n) | same : Sequent n → Premise n | up : Sequent (n+1) → Premise n`, with `Rule n : List (Premise n) → Sequent n → Prop`. The types then say exactly that a premise is in scope `n` or `n+1`. `Derivable R P : {n : ℕ} → Sequent n → Prop` gets two hypotheses, `∀ s, .same s ∈ ps → Derivable s` and `∀ s, .up s ∈ ps → Derivable s`. Keep them as two hypotheses rather than one `match` on the premise, so the inductive type stays strictly positive.
- **(c) One constructor per rule:** `inductive Proves : {n : ℕ} → Sequent n → Prop` with each LU rule as a constructor. This is the most idiomatic option for well-scoped syntax, but you lose the generic `Derivable R P` framework. That framework is what `ProvableWithin` relies on: it requires every sequent in the derivation to satisfy a fragment predicate. You would have to thread `P : ∀ {n}, Sequent n → Prop` through every constructor.

**Recommendation:** index `Sequent` by `n`, and use (b) for `Rule`/`Derivable`, with `P : ∀ {n}, Sequent n → Prop`. The fragment predicates are already uniform in the scope, so this fits easily. The proof changes would be mostly mechanical. The gain is cleaner statements, not new results.

# Summary of changes for run b39f6d29-736c-4cd0-bce3-9044cf747a09
Yes, the syntax should be indexed by scope. I changed it, and every file that uses it now builds with the new types. Nothing changed in what is proved: the only `sorry` is still `cut_elimination`, which the paper only claims too. The key theorems (`fragment_theorem_cutFree`, `ProvableWithin.substPred`, `provable_iff_LL`, `LL.of_provable_table3`, `multiplicative_impL_NP_breaks_mu`) use only the standard axioms.

**Terms** (`Syntax.lean`)
```lean
structure Func where name : ℕ; arity : ℕ
inductive Term (n : ℕ) where
  | var : Fin n → Term n
  | func (f : Func) : (Fin f.arity → Term n) → Term n
```
`Term 0` is the type of closed terms. One change from your sketch: function symbols are not `Fin n`. The scope `n` counts variables, not symbols. Instead each symbol carries its arity, and its arguments are a tuple of exactly `f.arity` terms, so the wrong number of arguments can't be written.

**Predicates and formulas**
- An atom has exactly as many arguments as its predicate's arity: `atom (p : Pred) (ts : Fin p.arity → Term n) : Formula n`.
- `Formula : ℕ → Type` is indexed by scope, and the body of a quantifier is a `Formula (n + 1)`.
- `Formula 0` (abbreviation `ClosedFormula`) is the type of closed formulas.
- `Pred` keeps its name, arity and polarity but has no scope index, because a predicate symbol mentions no variables.
- There is one simultaneous substitution, `Formula.subst` (with `Subst n m := Fin n → Term m`), which avoids capture by construction. Weakening (`shift`) and instantiation (`inst`, i.e. `A[t/x]`) are special cases of it, and its composition laws are proved.

**Other constructs**
- **Sequents:** a `Sequent` has a field `scope`, and its four zones are multisets of `Formula scope`, so every formula in a sequent lives in the same context; scope 0 means a closed sequent. The scope is a field rather than a type index because the premise of an eigenvariable rule lives in scope `n + 1`, and a derivation still has to be a tree of sequents.
- **Eigenvariable condition:** it now holds by construction. The premise is in scope `n + 1` and its context is the weakened context, which cannot mention the fresh variable. The same holds in the linear-logic, LJ and LK calculi (`LL`, `LJ`, `LK`), which are now indexed by scope.
- **Substitution of a formula for an atom** (§6): `substPred a (A : Formula (n + a.arity)) (B : Formula n)`. The types force `A` to have exactly as many distinguished variables as the atom's arity, and its parameters are weakened under binders so they are never captured. The provability theorems take `A : Formula (S.scope + a.arity)`.
- **Example:** the counterexample in `MultiplicativeReading.lean` now uses closed atoms (`Formula 0`).

**Proof changes forced by the new types**
- The invariants of the intuitionistic and classical proofs quantified over arbitrary target sequents. They now quantify over the four zones at the same scope, which is equivalent.
- The absorption lemmas in `Classical.lean` now name the premise by its zones.
- The old shift and index-substitution lemmas were replaced by single lemmas about `subst`, e.g. `toLL_subst` and `isClassical_subst`.

`LU_FORMALIZATION.md` and the Properties table are updated. The table has new entries for `Term`, `Formula` and `Sequent`, and the changed statements are back to proved after the rebuild. The whole project builds and everything is committed.

# Summary of changes for run e0698a9a-a9f4-424b-b383-cb72c12d6c24
I fixed every open item except cut elimination for LU. That is still the project's only `sorry` (`cut_elimination` in `MainTheorem.lean`), and the paper only claims it too (Remark (i)). The whole project builds, and every new theorem uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**1. Left rule for `N ⇒ P`.** `Rule.impL_NP` keeps the additive rule. Its docstring and the file header of `Calculus.lean` now say that this deliberately departs from the misprinted multiplicative rule in Fig. 3. Your patch to the typ file is applied, so the typ file and the Lean code agree.

**2. Substitution property (§6)**, in `Substitution.lean`:
- The four fragments are closed under substituting a formula for an atom (`Fragment.mem_substPred`).
- If the formula has the atom's polarity, polarity is preserved and sequents of a fragment stay in that fragment.
- Provability is preserved with cuts, without cuts, and within a fragment (`Provable.substPred`, `CutFreeProvable.substPred`, `ProvableWithin.substPred`).

**3. §4, LU is equivalent to linear logic.**
- `LinearLogic.lean` defines two-sided first-order linear logic `LL` and translates its proofs into LU, so that \(\Gamma \vdash \Delta\) becomes `Γ; ⊢ ;Δ`. Cut-free proofs map to cut-free proofs, and promotion is simulated through the central zone as the paper describes (`LL.provable`, `LL.cutFreeProvable`).
- `LinearEquiv.lean` proves the paper's "easy inductive argument": with neutral atoms, \(P \vdash\, !P\) for positive \(P\) and \(?N \vdash N\) for negative \(N\). From this it derives the strengthened `!` rule (`LL.bangR_strong`). It also translates any LU derivation of `Γ;Γ' ⊢ Δ';Δ` made of linear formulas with neutral atoms into an LL proof of \(\Gamma, !\Gamma' \vdash ?\Delta', \Delta\) (`LL.of_derivable_neutralLinear`). One difference: the paper leaves positive central formulas without `!`, while I put `!` on all of them; the lemma above makes the two readings equivalent.
- `provable_iff_LL`: for linear formulas with neutral atoms, `Γ; ⊢ ;Δ` is provable in LU (cuts allowed) if and only if \(\Gamma \vdash \Delta\) is provable in LL. This needs no cut-elimination hypothesis.

**4. Soundness for Table 3**, in `Table3Soundness.lean`. `LL.of_provable_table3` shows that every LU rule, including the cuts and all Fig. 3 cases, is sound for the reading \(\Gamma^*, !\Gamma'^* \vdash ?\Delta'^*, \Delta^*\), where \(A^*\) is the Table 3 decomposition. The theorem covers all atom polarities: a positive atom \(p\) is read as \(!p_0\) and a negative one as \(?p_0\), where \(p_0\) is the neutral atom with the same name and arity. With only neutral atoms, the reading is exactly `toLinear` (`LL.of_provable_toLinear`). This also confirms that the additive `N ⇒ P` rule is sound for \(N^\perp \oplus P\).

**5. Comparison with LJ and LK** (end of §6):
- `LJ.lean`: provability within the intuitionistic fragments translates to Gentzen's LJ, and LJ proofs of intuitionistic sequents are LU-provable, using cuts.
- `LK.lean`: cut-free classical LU proofs translate to LK. The paper's LC is not formalized, so this is LK rather than LC.

**Still open:**
- **Cut elimination for LU** is not proved, so `fragment_theorem` (the §6 theorem with cuts) remains in progress. The cut-free version and the version that assumes cut elimination are proved. For linear sequents `Γ; ⊢ ;Δ` with neutral atoms, `cutFreeProvable_of_LLCutElimination` shows that LU cut elimination would follow from cut elimination for linear logic, which is also not proved; it is a hypothesis of that theorem.
- **Remark (ii)** and the other denotational claims (coherence and correlation spaces) are outside this formalization.

`COMPLETENESS_AUDIT.md`, `LU_FORMALIZATION.md` and the Properties table are updated to match.

# Summary of changes for run 64c3f34e-dc42-4e7f-b817-09bfc683878a
**No, the formalization is not complete.** I compared your typ file with the Lean code section by section. The core of the paper is formalized and matches it, but three things are missing or differ. The project builds, and it has exactly one `sorry`. The full comparison is in `COMPLETENESS_AUDIT.md`.

**What is formalized and checked against the typ:**
- **Tables 1 and 2:** transcribed and checked entry by entry.
- **Table 3:** proved to agree with Tables 1–2 on polarities.
- **Figs. 1–3:** all rules checked one by one, with one exception (the `N ⇒ P` rule below).
- **The four fragments and their kinds of sequent:** match the typ.
- **The Theorem of §6 for cut-free proofs:** fully proved for all four fragments. It uses only Lean's standard axioms. The head-variable remark is also proved.

**What is incomplete:**
1. **Cut elimination is not proved.** `cut_elimination` is the one `sorry`. So the Theorem with cuts (`fragment_theorem`) holds only assuming cut elimination. The paper doesn't prove it either: Remark (i) calls it "more or less obvious" and points to a forthcoming paper by J. Vauzeilles.
2. **Several of the paper's claims are not formalized at all:**
   - §4: LU is equivalent to ordinary linear logic.
   - LU's rules are sound with respect to the Table 3 translation (only the polarity agreement is proved).
   - The substitution property of the fragments.
   - Remark (ii) on denotational semantics.
   - The comparison with LJ and LC at the end of §6.
   - The informal claims about isomorphisms and the associativity of disjunction.
3. **One rule reads differently from your typ file.** For the left rule of `N ⇒ P` (classical implication, Fig. 3):
   - The scanned PDF has misprints.
   - Your typ file corrects them to a **multiplicative** rule (contexts `Γ, Λ` and `Δ, Π`).
   - The Lean code uses the **additive** rule, which is the left rule of `N⊥ ⊕ P`, the decomposition Table 3 gives for `N ⇒ P`.

**Why the additive rule:** the paper's proof for the classical fragment needs that every rule whose conclusion has \(\mu > 1\) has a premise with \(\mu\) at least as large. The multiplicative rule breaks this. I added `RequestProject/LU/MultiplicativeReading.lean` with a proof (no `sorry`) of a concrete instance: two cut-free provable classical premises, each with \(\mu = 1\), whose multiplicative conclusion has \(\mu = 2\). As a test I swapped the multiplicative rule into the calculus: only the classical case of the proof failed, and I reverted it. Whether the Theorem itself still holds under the multiplicative reading is open.

Files changed: `COMPLETENESS_AUDIT.md` (new), `RequestProject/LU/MultiplicativeReading.lean` (new), and a new row in `LU_FORMALIZATION.md`. Everything is committed.

## Suggested follow-up

Your typ file writes the left rule for `N ⇒ P` (Fig. 3) as a multiplicative rule. The formalization uses the additive rule of `N⊥ ⊕ P` from Table 3, because the multiplicative version breaks the step of Girard's proof for the classical fragment. If you meant the multiplicative rule, I can switch the calculus to it and try to rework the classical-fragment proof, or look for a counterexample to the Theorem under that reading. I can also try to formalize one of the missing parts, such as the substitution property or the translation to LJ.

# Summary of changes for run 3c81b62b-3b1d-43ee-bafc-af43e424a227
I formalized Girard's *On the unity of logic* in Lean, in about 2,850 lines under `RequestProject/LU/`. The theorem of §6 is fully proved for cut-free proofs. The version with cuts depends on cut elimination for LU, which I did not prove: it is the one `sorry` in the project (`cut_elimination` in `MainTheorem.lean`). The paper also only claims it ("more or less obvious, but perhaps a bit too long to write down explicitly"). `LU_FORMALIZATION.md` maps each part of the paper to its Lean file.

**What is formalized:**
- **Language and polarities (§2, Tables 1–2):** `Syntax.lean`. Formulas use de Bruijn indices for bound variables.
- **Table 3:** `Translation.lean` gives the decomposition into linear logic. `pol_toLinear` proves Tables 1–3 agree on polarities, and `isLinearConn_toLinear` proves the decomposition only uses linear connectives.
- **The calculus LU (Figs. 1–3):** `Calculus.lean` has sequents `Γ;Γ' ⊢ Δ';Δ` as four multisets, about 90 cut-free rules, the three cut rules, and provability with and without cut.
- **The four fragments of §6:** `Fragments.lean` defines classical, intuitionistic, neutral intuitionistic and linear formulas, μ, each fragment's notion of sequent, and "provable within the fragment".
- **Subformula property:** `Subformula.lean`.

**Proved results (no `sorry`, standard axioms only):**
- `fragment_theorem_cutFree`: a sequent of any of the four fragments with a cut-free LU proof is provable within that fragment. Each fragment has its own result, following the paper's proof:
  - linear: from the subformula property;
  - neutral intuitionistic: by counting formulas in Γ; `neutral_headVariable` proves Γ has at most one formula;
  - intuitionistic (`IntMain.lean`): uses the paper's invariant for ν ≠ 1, under which formulas may be added and positive or atomic ones removed; this is how the "bad" ⊃-left rule is replaced by the "good" one;
  - classical (`ClMain.lean`): uses the paper's invariant for μ ≥ 2, removing formulas that contribute to μ; this is how the "bad" permeability rules are replaced by weakening.
- `fragment_theorem_of_cutElimination`: the theorem for proofs with cuts, assuming cut elimination.
- `fragment_theorem` is the paper's statement with cuts; it depends on the unproved `cut_elimination`.

**Transcription choices you should know about:**
- The left rule printed for `N ⇒ P` in Fig. 3 has evident misprints (`Q` for `P`, `;` for `,`). I used the additive left rule of `N⊥ ⊕ P`, which is what Table 3 decomposes `N ⇒ P` into.
- As in the paper, the classical-implication rules with neutral arguments are omitted.
- The paper's side remark that the fragments are closed under substitution for atoms is not formalized.

The Properties table lists these results with their status; `cut_elimination` and `fragment_theorem` are marked in progress.