# Is the formalization of Girard, *On the unity of logic*, complete?

This file compares `Girard - On the unity of logic - 1993.typ`, section by section, with the
Lean development in `RequestProject/LU/`. The full project builds. It has exactly one
`sorry`: `cut_elimination` in `MainTheorem.lean`.

**Short answer: almost.** The language, the polarity tables, the calculus LU, the
fragments, the Theorem of §6 for cut-free proofs, the substitution property, the §4
equivalence with linear logic, soundness for the Table 3 reading and the comparisons with
LJ/LK are formalized and proved. What remains:

1. The Theorem of §6 *with cuts* (`fragment_theorem`) depends on cut elimination for LU,
   which is not proved. The paper does not prove it either (Remark (i)).
2. The denotational claims (Remark (ii), §1, §5, Conclusion) and the comparison with
   Girard's LC are not formalized (list below).
3. The left rule for `N ⇒ P` is the additive one, a deliberate departure from the
   (misprinted) multiplicative rule of Fig. 3; see the last section. The typ file has been
   patched to match.

## What is formalized and matches the typ file

| Paper (typ) | Lean | Status |
|---|---|---|
| §2 Table 1 (linear polarities) | `Syntax.lean`: `Pol.tensor`, `Pol.par`, … | Checked entry by entry; matches |
| §5 Table 2 (classical/intuitionistic polarities) | `Syntax.lean`: `Pol.conj`, `Pol.disj`, `Pol.imp`, `Pol.iimp`; `∀` negative, `∃` positive | Checked entry by entry; matches |
| §5 Table 3 (decomposition into LL) | `Translation.lean`: `toLinear`, `pol_toLinear` | Proved: Tables 1–3 agree on polarities |
| §6 language | `Syntax.lean`: `Formula` | Matches (also has `⊥, ⊤, ?` from Fig. 2) |
| Fig. 1 (identity, structure, 3 cuts) | `Calculus.lean`: `Rule`, `CutRule` | Matches; exchange is built in via multisets |
| Fig. 2 (linear rules) | `Calculus.lean` | Matches the typ rule by rule (including `⊤`/`0` axioms with empty central zone) |
| Fig. 3: conjunction, `⊃`, `∀`, the nine disjunction cases, `∃` | `Calculus.lean` | Checked rule by rule; matches |
| Fig. 3: classical implication | `Calculus.lean` | Matches, except the left rule for `N ⇒ P` (see below); neutral cases omitted, as in the paper |
| §6 fragments (1)–(4) and sequents (i)–(iii) | `Fragments.lean` | Matches |
| §6 Theorem, cut-free proofs | `fragment_theorem_cutFree` | **Proved** (standard axioms only) |
| §6 head-variable remark | `neutral_headVariable` | **Proved** |
| §6 Theorem, with cuts | `fragment_theorem` | Depends on unproved `cut_elimination` |
| Remark (i): cut elimination | `cut_elimination` | **`sorry`** |
| §6 substitution property | `Substitution.lean`: `Fragment.mem_substPred`, `Fragment.seq_substPred`, `Provable.substPred`, `CutFreeProvable.substPred`, `ProvableWithin.substPred` | **Proved** |
| §4: LL translates into LU (`Γ ⊢ Δ` ↦ `Γ; ⊢ ;Δ`), cut-free to cut-free | `LinearLogic.lean`: `LL.provable`, `LL.cutFreeProvable` | **Proved** |
| §4: strengthened `!` rule (`P ⊢ !P` for positive, `?N ⊢ N` for negative, neutral atoms) | `LinearEquiv.lean`: `Formula.IsNeutralLinear.bang_quest`, `LL.bangR_strong` | **Proved** |
| §4: LU with neutral atoms translates into LL | `LinearEquiv.lean`: `LL.of_derivable_neutralLinear`, `LL.of_cutFreeProvable_neutralLinear` | **Proved** |
| §4: equivalence (neutral linear `Γ; ⊢ ;Δ` provable in LU iff `Γ ⊢ Δ` in LL) | `Table3Soundness.lean`: `provable_iff_LL` | **Proved** (no cut-elimination hypothesis) |
| Soundness of all LU rules (with cuts) for the Table 3 reading `Γ*, !Γ'* ⊢ ?Δ'*, Δ*` | `Table3Soundness.lean`: `LL.of_provable_table3`, `LL.of_provable_toLinear` | **Proved** |
| End of §6: intuitionistic fragments vs LJ | `LJ.lean`: `LJ.of_provableWithin_intuitionistic`, `LJ.of_provableWithin_neutralInt`, `LJ.provable` | **Proved** (LU-with-cuts → LJ uses a cut-elimination hypothesis) |
| End of §6: classical fragment vs LK | `LK.lean`: `LK.of_cutFreeProvable_classical`, `LK.of_provableWithin_classical` | **Proved** (LK, not LC) |

## Not formalized

* **Cut elimination** (Remark (i)): not proved. `cutFreeProvable_of_LLCutElimination` shows
  that, for linear sequents `Γ; ⊢ ;Δ` with neutral atoms, it would follow from cut
  elimination for linear logic (taken as a hypothesis).
* **Remark (ii):** the denotational content (coherent and correlation spaces, proofs being
  denotationally equal). This needs a semantics that is not formalized.
* **End of §6, LC:** Girard's calculus LC is not formalized; the classical fragment is
  compared with Gentzen's LK instead (soundness direction only).
* **Table 3 with positive/negative atoms:** the Table 3 reading treats a positive atom `p`
  as `!p₀` and a negative atom as `?p₀` (`Formula.toLL`); for neutral atoms it is exactly
  `toLinear`.
* **§1, §5 and the Conclusion:** the informal claims about isomorphisms and associativity
  of disjunction (these are denotational).

## The left rule for `N ⇒ P` (Fig. 3, classical implication)

* The scanned PDF prints
  `Γ;Γ' ⊢ Δ';Δ,N   Q,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ;Π`, which contains misprints.
* The typ file originally corrected this to the **multiplicative** rule
  `Γ;Γ' ⊢ Δ';Δ,N   P,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ,Π`; it has since been patched
  to the additive rule below, so the typ file and the Lean code now agree.
* The Lean code (`Rule.impL_NP`) uses the **additive** rule
  `Γ;Γ' ⊢ Δ';Δ,N   P,Γ;Γ' ⊢ Δ';Δ  /  N⇒P,Γ;Γ' ⊢ Δ';Δ`.
  This is the left rule of `N⊥ ⊕ P`, which is what Table 3 gives for `N ⇒ P`. It also
  agrees with the paper's remark that these rules "would have been the same if implication
  had been defined from conjunction", since `¬(N ∧ ¬P) = (N & P⊥)⊥ = N⊥ ⊕ P`.

The additive reading is also the one under which the paper's proof works. The proof for
the classical fragment says that for every rule whose conclusion `S` has `μ(S) > 1`, some
premise `S'` has `μ(S') ≥ μ(S)`, and the `F` axiom is the only exception. The
multiplicative reading violates this. `RequestProject/LU/MultiplicativeReading.lean` proves
(`multiplicative_impL_NP_breaks_mu`, no `sorry`) that the instance

  `; ⊢ ; ¬q, q     q', ¬q'; ⊢ ;  /  ¬q⇒q', ¬q'; ⊢ ; q`   (`q, q'` positive atoms)

has two cut-free provable premises made of classical formulas, each with `μ = 1`. Its
conclusion has `μ = 2`.

When I swapped the multiplicative rule into the calculus as a test, the subformula property
and the linear, neutral-intuitionistic and intuitionistic cases still built. Only the
classical case failed, which is exactly where this invariant is used. The
test was then reverted. Whether the Theorem itself still holds under the multiplicative
reading has not been determined.
