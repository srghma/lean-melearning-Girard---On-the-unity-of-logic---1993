# Girard, *On the unity of logic* (1993) — Lean formalization

All files are under `RequestProject/LU/`.

| Paper | Lean |
|---|---|
| §2, §6: language (over signatures), polarities, Tables 1–2 | `Syntax.lean` (`Pol`, `TermSig`, `PredSig`, `Tm`, `Tms`, `Formula`, `Formula.pol`) |
| Table 3 (decomposition into linear logic) | `Translation.lean` (`Formula.toLinear`, `pol_toLinear`, `isLinearConn_toLinear`) |
| §3–§5, Figs. 1–3: the sequent calculus LU | `Calculus.lean` (`Sequent`, `Rule`, `CutRule`, `Provable`, `CutFreeProvable`) |
| §6: the four fragments and their sequents | `Fragments.lean` (`IsClassical`, `IsIntuitionistic`, `IsNeutralInt`, `IsLinear`, `mu`, `Fragment.Seq`, `ProvableWithin`) |
| Subformula property of cut-free rules | `Subformula.lean` (`Rule.allIn_premises`, `Derivable.allIn`) |
| Theorem §6: linear and neutral intuitionistic fragments, head variable | `NeutralInt.lean` |
| Theorem §6: intuitionistic fragment | `Intuitionistic.lean`, `IntMain.lean` (`intuitionistic_within`) |
| Theorem §6: classical fragment | `Classical.lean`, `ClMain.lean` (`classical_within`) |
| Theorem §6 (all fragments) | `MainTheorem.lean` |
| Left rule for `N ⇒ P`: the multiplicative reading breaks the classical invariant | `MultiplicativeReading.lean` |
| §6: the substitution property | `Substitution.lean` (`Formula.substPred`, `Fragment.mem_substPred`, `Fragment.seq_substPred`, `CutFreeProvable.substPred`, `Provable.substPred`, `ProvableWithin.substPred`) |
| End of §6: comparison of the intuitionistic fragments with LJ | `LJ.lean` (`LJ`, `LJ.of_provableWithin_intuitionistic`, `LJ.of_provableWithin_neutralInt`, `LJ.provable`) |
| End of §6: the classical fragment and LK | `LK.lean` (`LK`, `LK.of_cutFreeProvable_classical`, `LK.of_provableWithin_classical`) |
| §4: usual linear logic and its translation into LU | `LinearLogic.lean` (`LL`, `LL.provable`, `LL.cutFreeProvable`) |
| §4: the strengthened `!` rule and the translation of LU (neutral atoms) into LL | `LinearEquiv.lean` (`Formula.IsNeutralLinear.bang_quest`, `Formula.IsGuardedLinear.bang_quest`, `LL.bangR_strong`, `LL.of_derivable_neutralLinear`, `LL.of_cutFreeProvable_neutralLinear`) |
| §5: soundness of every LU rule for the Table 3 reading; §4 equivalence | `Table3Soundness.lean` (`Formula.toLL`, `LL.of_provable_table3`, `LL.of_provable_toLinear`, `provable_iff_LL`, `cutFreeProvable_of_LLCutElimination`) |
| Consistency of LU for every choice of atom polarities (classical soundness) | `Consistency.lean` (`Model`, `Model.eval`, `Model.Valid`, `Rule.sound`, `CutRule.sound`, `Provable.valid`, `not_provable_empty`, `not_provable_zero`, `not_provable_bot`, `not_provable_atom`, `not_provable_and_neg`, `consistent_for_every_polarity`) |

Status:
* `fragment_theorem_cutFree` (the theorem for cut-free proofs, all four fragments) is fully
  proved, as is `fragment_theorem_of_cutElimination` (the theorem for proofs with cuts,
  assuming cut elimination).
* §4 (equivalence of LU with neutral atoms and linear logic, both directions, including the
  strengthened `!` rule), soundness of LU for the Table 3 reading, the substitution property
  and the comparisons with LJ and LK are fully proved.
* Consistency, for an arbitrary polarity assignment to the predicate symbols: every rule of
  LU (including the three cuts) is sound for the classical reading that forgets polarities and
  linearity, so provable sequents are classically valid, the empty sequent, `; ⊢ ; 0` and
  `; ⊢ ; ⊥` are unprovable, and no formula is provable together with its negation. This is
  fully proved and does not depend on `cut_elimination`.
* `cut_elimination` (Remark (i): "more or less obvious (but perhaps a bit too long to write
  down explicitly)") is **not** proved; it is the only `sorry` in the development, and
  `fragment_theorem` (the statement with cuts) depends on it.

Transcription choices: the language is a parameter — function symbols come from a signature
`TS : TermSig` (`Func`, `arity`) and predicate symbols, with their arity and polarity, from a
signature `PS : PredSig` (`Pred`, `arity`, `predPol`); every development is stated for
arbitrary signatures with `[DecidableEq PS.Pred]` and `[DecidableEq TS.Func]` (needed for the
finite-set central zones). Terms `Tm TS n` and `k`-tuples of terms `Tms TS n k` are a mutual
pair of inductive types, so a tuple is never a term and atoms `atom p (ts : Tms TS n
(PS.arity p))` have a unique representation. Syntax is well-scoped by construction —
`Tm TS n` and `Formula PS TS n` have their free variables in `Fin n` (de Bruijn indices;
`Formula PS TS 0` = closed formulas), function and predicate symbols always receive exactly
`arity` arguments, and quantifier bodies live in `Formula PS TS (n + 1)`; sequents are
indexed by their scope (`Sequent PS TS n`), the linear zones are multisets and the central
zones finite sets of formulas (exchange built in, and central contraction built in, so the two contraction
rules of Fig. 1 are omitted while weakening is kept); a rule premise is a `Premise PS TS n`, i.e.
a sequent of scope `n` or (eigenvariable rules) `n + 1`, and eigenvariable conditions hold by
construction (the premise lives in scope `n + 1`, its context is the weakened context); the
misprinted left rule for `N ⇒ P` (Fig. 3) is taken to be the additive left rule of `N⊥ ⊕ P`
(Table 3); as in the paper, classical-implication rules with neutral arguments are omitted.
In the Table 3 soundness theorem a positive atom `p` is read as `!p` and a negative one as
`?p` (the paper's `!p₀`, `?p₀` with `p₀` neutral): linear logic ignores the polarity of atoms,
so no extra neutral copy of `p` is needed in the signature.
