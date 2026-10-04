# Girard, *On the unity of logic* (1993) — Lean formalization

All files are under `RequestProject/LU/`.

| Paper | Lean |
|---|---|
| §2, §6: language, polarities, Tables 1–2 | `Syntax.lean` (`Pol`, `Formula`, `Formula.pol`) |
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
| §4: the strengthened `!` rule and the translation of LU (neutral atoms) into LL | `LinearEquiv.lean` (`Formula.IsNeutralLinear.bang_quest`, `LL.bangR_strong`, `LL.of_derivable_neutralLinear`, `LL.of_cutFreeProvable_neutralLinear`) |
| §5: soundness of every LU rule for the Table 3 reading; §4 equivalence | `Table3Soundness.lean` (`Formula.toLL`, `LL.of_provable_table3`, `LL.of_provable_toLinear`, `provable_iff_LL`, `cutFreeProvable_of_LLCutElimination`) |

Status:
* `fragment_theorem_cutFree` (the theorem for cut-free proofs, all four fragments) is fully
  proved, as is `fragment_theorem_of_cutElimination` (the theorem for proofs with cuts,
  assuming cut elimination).
* §4 (equivalence of LU with neutral atoms and linear logic, both directions, including the
  strengthened `!` rule), soundness of LU for the Table 3 reading, the substitution property
  and the comparisons with LJ and LK are fully proved.
* `cut_elimination` (Remark (i): "more or less obvious (but perhaps a bit too long to write
  down explicitly)") is **not** proved; it is the only `sorry` in the development, and
  `fragment_theorem` (the statement with cuts) depends on it.

Transcription choices: sequents are quadruples of multisets (exchange built in); bound
variables use de Bruijn indices (eigenvariable conditions = shifting the context); the
misprinted left rule for `N ⇒ P` (Fig. 3) is taken to be the additive left rule of `N⊥ ⊕ P`
(Table 3); as in the paper, classical-implication rules with neutral arguments are omitted.
