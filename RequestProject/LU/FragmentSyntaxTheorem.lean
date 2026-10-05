module

public import RequestProject.LU.MainTheorem
public import RequestProject.LU.FragmentSyntaxInt

/-!
# The theorem of §6 for the intrinsic fragment sequents

With the intrinsic sequent types of `FragmentSyntax.lean` and `FragmentSyntaxInt.lean`, the
cut-free theorem of §6 says: a cut-free LU proof of a sequent of a fragment can be replaced by
a proof in which *every* sequent is (the image of) an intrinsic sequent of that fragment.
These are direct consequences of `fragment_theorem_cutFree` and of the `range_toSequent`
characterizations.
-/

@[expose] public section

namespace LU

variable {PS : PredSig} {TS : TermSig} [DecidableEq PS.Pred] [DecidableEq TS.Func]

/-- Classical fragment: every sequent of the proof is a stoup sequent `ClSequent`. -/
theorem ClSequent.cutFree_within {n : ℕ} (T : ClSequent PS TS n)
    (h : CutFreeProvable T.toSequent) :
    Derivable Rule (fun {m} S => ∃ T' : ClSequent PS TS m, T'.toSequent = S) T.toSequent :=
  (fragment_theorem_cutFree .classical ((ClSequent.range_toSequent _).2 ⟨T, rfl⟩) h).mono
    (fun _ _ h => h) (fun S hS => (ClSequent.range_toSequent S).1 hS)

/-- Intuitionistic fragment: every sequent of the proof is an `IntSequent`. -/
theorem IntSequent.cutFree_within {n : ℕ} (T : IntSequent PS TS n)
    (h : CutFreeProvable T.toSequent) :
    Derivable Rule (fun {m} S => ∃ T' : IntSequent PS TS m, T'.toSequent = S) T.toSequent :=
  (fragment_theorem_cutFree .intuitionistic ((IntSequent.range_toSequent _).2 ⟨T, rfl⟩) h).mono
    (fun _ _ h => h) (fun S hS => (IntSequent.range_toSequent S).1 hS)

/-- Neutral intuitionistic fragment: every sequent of the proof is an `NIntSequent`. -/
theorem NIntSequent.cutFree_within {n : ℕ} (T : NIntSequent PS TS n)
    (h : CutFreeProvable T.toSequent) :
    Derivable Rule (fun {m} S => ∃ T' : NIntSequent PS TS m, T'.toSequent = S) T.toSequent :=
  (fragment_theorem_cutFree .neutralIntuitionistic
      ((NIntSequent.range_toSequent _).2 ⟨T, rfl⟩) h).mono
    (fun _ _ h => h) (fun S hS => (NIntSequent.range_toSequent S).1 hS)

/-- Linear fragment: every sequent of the proof is a `LinSequent`. -/
theorem LinSequent.cutFree_within {n : ℕ} (T : LinSequent PS TS n)
    (h : CutFreeProvable T.toSequent) :
    Derivable Rule (fun {m} S => ∃ T' : LinSequent PS TS m, T'.toSequent = S) T.toSequent :=
  (fragment_theorem_cutFree .linear ((LinSequent.range_toSequent _).2 ⟨T, rfl⟩) h).mono
    (fun _ _ h => h) (fun S hS => (LinSequent.range_toSequent S).1 hS)

end LU
