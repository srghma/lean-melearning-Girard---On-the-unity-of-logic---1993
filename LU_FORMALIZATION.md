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

Status:
* `fragment_theorem_cutFree` (the theorem for cut-free proofs, all four fragments) is fully
  proved, as is `fragment_theorem_of_cutElimination` (the theorem for proofs with cuts,
  assuming cut elimination).
* `cut_elimination` (Remark (i): "more or less obvious (but perhaps a bit too long to write
  down explicitly)") is **not** proved; it is the only `sorry` in the development, and
  `fragment_theorem` (the statement with cuts) depends on it.

Transcription choices: sequents are quadruples of multisets (exchange built in); bound
variables use de Bruijn indices (eigenvariable conditions = shifting the context); the
misprinted left rule for `N ⇒ P` (Fig. 3) is taken to be the additive left rule of `N⊥ ⊕ P`
(Table 3); as in the paper, classical-implication rules with neutral arguments are omitted.
