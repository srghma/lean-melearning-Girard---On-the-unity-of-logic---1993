# Is the formalization of Girard, *On the unity of logic*, complete?

This file compares `Girard - On the unity of logic - 1993.typ`, section by section, with the
Lean development in `RequestProject/LU/`. The full project builds. It has exactly one
`sorry`: `cut_elimination` in `MainTheorem.lean`.

**Short answer: no.** The paper's technical core is formalized and faithful: the language,
the polarity tables, the calculus LU, the fragments and the Theorem of §6 for cut-free
proofs. It is not complete in three ways:

1. The Theorem of §6 *with cuts* (`fragment_theorem`) depends on cut elimination for LU,
   which is not proved. The paper does not prove it either (Remark (i)).
2. Several secondary claims of the paper are not formalized at all (list below).
3. The typ file and the Lean code read one rule of Fig. 3 differently. This is the left
   rule for `N ⇒ P`; see the last section.

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

## Not formalized

* **§4:** the claim that LU (with neutral atoms) is equivalent to ordinary linear logic,
  in both directions. That includes the strengthened `!` rule for positive/negative contexts.
* **Soundness of LU with respect to Table 3:** only the polarity agreement is proved.
  There is no theorem that LU rules are derivable in linear logic via `toLinear`.
* **§6, the substitution property:** fragments are closed under substituting formulas of the
  same polarity for atoms.
* **Remark (ii):** the denotational content (coherent and correlation spaces, proofs being
  denotationally equal). This needs a semantics that is not formalized.
* **End of §6:** the comparison of the fragments with LJ (`Γ;Γ' ⊢ ;A` ↦ `Γ,Γ' ⊢ A`) and
  with LC.
* **§1, §5 and the Conclusion:** the informal claims about isomorphisms and associativity
  of disjunction (these are denotational).

## The left rule for `N ⇒ P` (Fig. 3, classical implication)

* The scanned PDF prints
  `Γ;Γ' ⊢ Δ';Δ,N   Q,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ;Π`, which contains misprints.
* The typ file corrects this to the **multiplicative** rule
  `Γ;Γ' ⊢ Δ';Δ,N   P,Λ;Γ' ⊢ Δ';Π  /  N⇒P,Γ,Λ;Γ' ⊢ Δ';Δ,Π`.
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
