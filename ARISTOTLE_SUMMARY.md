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