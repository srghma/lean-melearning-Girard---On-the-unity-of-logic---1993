# Assessment: taking the function and predicate symbols from a signature

Proposed design:

```lean
structure TermSig where
  Func  : Type
  arity : Func → ℕ

structure PredSig where
  Pred    : Type
  arity   : Pred → ℕ
  predPol : Pred → Pol

inductive Term (TS : TermSig) (n : ℕ) : ℕ → Type where
  | var  : Fin n → Term TS n 1
  | func (f : TS.Func) : Term TS n (TS.arity f) → Term TS n 1
  | nil  : Term TS n 0
  | cons : Term TS n 1 → Term TS n k → Term TS n (k + 1)

inductive Formula (PS : PredSig) (TS : TermSig) : ℕ → Type where
  | atom {n} (p : PS.Pred) (t : Term TS n (PS.arity p)) : Formula PS TS n
  | one {n} : Formula PS TS n
  | ...
```

## The signature part is right

The paper does not fix a language. It only says that atomic predicates come with a
polarity. Making the symbols a parameter is therefore more faithful than the current
`Syntax.lean`, which fixes `Func := {name : ℕ, arity : ℕ}` and
`Pred := {name, arity, pol}`. Putting `predPol` in `PredSig` is the right place for
the polarity of atoms (§2). `TermSig` / `PredSig` as structures with a `Type` field and an
arity function is the standard presentation of a first-order signature (Mathlib's
`FirstOrder.Language` is similar).

## The `Term` family as written is **not** correct

The index `k` is used for two different things. `Term TS n 1` is meant to be the type of
terms, but `cons (t : Term TS n 1) nil` also has type `Term TS n (0 + 1) = Term TS n 1`.
So the "terms" include 1-tuples, and tuples of tuples, and so on. These were checked in
Lean, in `RequestProject/SignatureAssessment.lean`, which builds without `sorry`:

* **The same atom has two different representations.** For a unary predicate `p`,
  `atom p (var 0)` and `atom p (cons (var 0) nil)` both have type `Formula PS TS 1` and are
  different. (`Proposed.atom_two_representations` proves them unequal.) Both read as `p(x)`. Formula equality
  is now finer than syntactic identity. This breaks the identity axiom `A ⊢ A` up to
  representation, the central zones as `Finset`s (deduplication), and substitution
  lemmas.
* **Junk terms.** `cons (cons (var 0) nil) nil : Term TS 1 1` is a "term" that is not a
  first-order term. It can be passed to a function symbol or substituted for a variable.
* **Pattern matching sees the junk.** A `DecidableEq` (or any function) on `Term TS n 1`
  must handle `cons` against `var` and `func`, because Lean's coverage checker reports
  those cases as missing. They are real inhabitants and cannot be dismissed as impossible.

A smaller point: `cons` uses an auto-bound `k`. Write `{k : ℕ}` explicitly in case the
project ever switches `autoImplicit` off.

## Correct alternatives (`FixedA`, `FixedB` in the same file; both compile, with `rename` defined structurally)

**(A) Keep the current representation, parameterised by the signature (simplest,
closest to the existing code):**

```lean
inductive Term (TS : TermSig) (n : ℕ) : Type where
  | var  : Fin n → Term TS n
  | func (f : TS.Func) : (Fin (TS.arity f) → Term TS n) → Term TS n

inductive Formula (PS : PredSig) (TS : TermSig) : ℕ → Type where
  | atom {n} (p : PS.Pred) (ts : Fin (PS.arity p) → Term TS n) : Formula PS TS n
  | ...
```

**(B) Keep first-order tuples, but separate terms from tuples in the index.** Either use an
`Option ℕ` index (`none` = a term, `some k` = a `k`-tuple):

```lean
inductive Term (TS : TermSig) (n : ℕ) : Option ℕ → Type where
  | var  : Fin n → Term TS n none
  | func (f : TS.Func) : Term TS n (some (TS.arity f)) → Term TS n none
  | nil  : Term TS n (some 0)
  | cons {k : ℕ} : Term TS n none → Term TS n (some k) → Term TS n (some (k + 1))
```

or a mutual pair `Tm` (terms) / `Tms` (`k`-tuples). In both versions a tuple cannot be used
where a term is expected, so atoms and terms have unique representations again
(`FixedB.unary_tuple`: every argument of a unary predicate is `cons u nil`).

## Consequences for the rest of the development (with either A or B)

* **Decidable equality.** The central zones are now `Finset`s, so formulas need
  `DecidableEq`. With external symbols this needs `[DecidableEq TS.Func]` and
  `[DecidableEq PS.Pred]` as instance arguments, carried as `variable`s through the files.
* **No closed terms in general.** A signature may have no constants, so `Term TS 0` can be
  empty. The current `Inhabited (Term n)` instance, which uses a fixed constant, must go.
  Its one use, the proof of `shift_injective` in `Calculus.lean`, must be replaced by an
  injectivity-of-renaming argument. That argument was checked to work for the proposed
  family (`Proposed.Term.rename_injective`).
* **Concrete examples** such as `atQ`, `atQ'` in `MultiplicativeReading.lean`, and the
  predicate-substitution file `Substitution.lean`, which uses `p.arity` and `p.pol`, must
  be restated over a signature. For example, the examples can use a concrete signature with
  two nullary positive predicates.
* The proofs about rules, fragments and the main theorem do not depend on the
  representation of terms, so they should carry over essentially unchanged, apart from the
  extra parameters.

**Summary:** taking `Func`/`Pred` from outside is correct and recommended. The
proposed `Term` family must be changed, to (A) or (B), because index `1` mixes up terms
with 1-tuples.
