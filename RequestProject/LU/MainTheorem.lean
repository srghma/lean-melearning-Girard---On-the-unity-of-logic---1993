module

public import RequestProject.LU.ClMain

/-!
# The theorem of §6

> **Theorem.** If a sequent of one of the fragments considered is provable, it is provable
> within the fragment.

Girard's proof restricts attention to cut-free proofs, using "a cut-elimination theorem for
LU that is more or less obvious (but perhaps a bit too long to write down explicitly)"
(Remark (i)).  Accordingly:

* `fragment_theorem_cutFree` is the theorem for cut-free provability; it is fully proved,
  following the proof of the paper fragment by fragment;
* `CutElimination` is the statement of the cut-elimination theorem for LU;
* `fragment_theorem_of_cutElimination` derives the theorem for provability with cuts from
  cut elimination;
* `cut_elimination` states cut elimination for LU; it is **not proved** here (it is left as
  `sorry`), exactly as in the paper, where it is only claimed;
* `fragment_theorem` is the statement of the paper, which depends on `cut_elimination`.
-/

@[expose] public section

namespace LU

variable {PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]

variable {n : ℕ}

/-- A proof within a fragment is in particular a cut-free proof. -/
theorem ProvableWithin.cutFreeProvable {F : Fragment} {S : Sequent PS TS n}
    (h : ProvableWithin F S) : CutFreeProvable S :=
  h.mono (fun _ _ h => h) (fun _ _ => trivial)

/-- **Theorem of §6, for cut-free proofs.**  If a sequent of one of the four fragments has a
cut-free proof in LU, then it has a (cut-free) proof all of whose sequents are sequents of
the fragment. -/
theorem fragment_theorem_cutFree (F : Fragment) {S : Sequent PS TS n} (hS : F.Seq S)
    (h : CutFreeProvable S) : ProvableWithin F S := by
  cases F with
  | classical => exact classical_within h hS
  | intuitionistic => exact intuitionistic_within h hS
  | neutralIntuitionistic => exact neutralInt_within h hS
  | linear => exact linear_within h hS

/-- Cut elimination for LU: every provable sequent has a cut-free proof. -/
def CutElimination (PS : PredSig) (TS : TermSig) [DecidableEq PS.Pred] [DecidableEq TS.Func] :
    Prop := ∀ {n : ℕ} (S : Sequent PS TS n), Provable S → CutFreeProvable S

/-- The theorem of §6 for provability with cuts, assuming cut elimination. -/
theorem fragment_theorem_of_cutElimination (hce : CutElimination PS TS) (F : Fragment)
    {S : Sequent PS TS n} (hS : F.Seq S) (h : Provable S) : ProvableWithin F S :=
  fragment_theorem_cutFree F hS (hce S h)

/-- Cut elimination for LU (Remark (i) of §6: "more or less obvious (but perhaps a bit too
long to write down explicitly)").  Not proved in this development. -/
theorem cut_elimination : CutElimination PS TS := by
  sorry

/-- **Theorem of §6.**  If a sequent of one of the fragments is provable in LU, it is
provable within the fragment.  (Depends on the unproved `cut_elimination`.) -/
theorem fragment_theorem (F : Fragment) {S : Sequent PS TS n} (hS : F.Seq S) (h : Provable S) :
    ProvableWithin F S :=
  fragment_theorem_of_cutElimination cut_elimination F hS h

end LU
