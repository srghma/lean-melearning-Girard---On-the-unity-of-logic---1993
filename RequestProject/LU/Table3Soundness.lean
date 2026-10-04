module

public import RequestProject.LU.LinearEquiv
public import RequestProject.LU.Translation

/-!
# Soundness of LU with respect to Table 3

Table 3 (§5) defines the chimeric connectives `∧, ∨, ⇒, ⊃, ∀, ∃` in terms of linear logic,
depending on the polarities of their arguments (`Formula.toLinear`, `Translation.lean`).  The
intended meaning of an LU sequent `Γ;Γ' ⊢ Δ';Δ` is the linear sequent `Γ, !Γ' ⊢ ?Δ', Δ` (§3).
We prove that **every rule of LU is sound for this reading**: if `Γ;Γ' ⊢ Δ';Δ` is provable in
LU (with cuts), then `Γ*, !Γ'* ⊢ ?Δ'*, Δ*` is provable in linear logic (with cut), where
`A*` is the Table 3 decomposition of `A` (`LL.of_provable_table3`).

Atoms.  A positive atom `p` of LU behaves like a formula `!p` of linear logic (it may be
contracted and weakened on the left), and dually a negative atom behaves like `?p`.  So the
translation `Formula.toLL` is `toLinear` (Table 3) in which, in addition, a positive atom
`p` is read as `!p₀` and a negative atom as `?p₀`, where `p₀` is the neutral atom with the
same name and arity; neutral atoms are unchanged.  For formulas whose atoms are all neutral,
`toLL` *is* `toLinear` (`Formula.toLL_eq_toLinear`).
-/

@[expose] public section

namespace LU

open Formula

namespace Formula

/-- Reading of an atom in linear logic: `p ↦ !p₀` if `p` is positive, `p ↦ ?p₀` if `p` is
negative (`p₀` is `p` declared neutral), and neutral atoms are unchanged. -/
def atomLL (p : Pred) (ts : List Term) : Formula :=
  match p.pol with
  | .pos => bang (atom { p with pol := .neu } ts)
  | .neg => quest (atom { p with pol := .neu } ts)
  | .neu => atom p ts

/-- The translation of LU formulas into linear logic: Table 3 (as `toLinear`), with positive
atoms read as `!p₀` and negative atoms as `?p₀`. -/
def toLL : Formula → Formula
  | atom p ts => atomLL p ts
  | one => one
  | zero => zero
  | bot => bot
  | top => top
  | neg A => neg A.toLL
  | bang A => bang A.toLL
  | quest A => quest A.toLL
  | tensor A B => tensor A.toLL B.toLL
  | par A B => par A.toLL B.toLL
  | lolli A B => lolli A.toLL B.toLL
  | with_ A B => with_ A.toLL B.toLL
  | plus A B => plus A.toLL B.toLL
  | conj A B => conjLin A.pol B.pol A.toLL B.toLL
  | disj A B => disjLin A.pol B.pol A.toLL B.toLL
  | imp A B => impLin A.pol B.pol A.toLL B.toLL
  | iimp A B => iimpLin A.pol A.toLL B.toLL
  | lall A => lall A.toLL
  | lex A => lex A.toLL
  | call A => callLin A.pol A.toLL
  | cex A => cexLin A.pol A.toLL

/-- Formulas all of whose atoms are neutral. -/
def AtomsNeutral : Formula → Prop
  | atom p _ => p.pol = .neu
  | one | zero | bot | top => True
  | neg A | bang A | quest A | lall A | lex A | call A | cex A => A.AtomsNeutral
  | tensor A B | par A B | lolli A B | with_ A B | plus A B | conj A B | disj A B | imp A B
  | iimp A B => A.AtomsNeutral ∧ B.AtomsNeutral

/-- With neutral atoms, the translation is exactly the Table 3 decomposition `toLinear`. -/
theorem toLL_eq_toLinear {A : Formula} (h : A.AtomsNeutral) : A.toLL = A.toLinear := by
  induction A <;> simp_all [AtomsNeutral, toLL, toLinear, atomLL]

theorem pol_atomLL (p : Pred) (ts : List Term) : (atomLL p ts).pol = p.pol := by
  unfold atomLL; split <;> simp_all [pol]

@[simp] theorem pol_toLL (A : Formula) : A.toLL.pol = A.pol := by
  induction A with
  | atom p ts => exact pol_atomLL p ts
  | conj A B ihA ihB =>
    simp only [toLL, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [conjLin, pol, Pol.tensor, Pol.with_,
      Pol.conj]
  | disj A B ihA ihB =>
    simp only [toLL, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [disjLin, pol, Pol.plus, Pol.par,
      Pol.disj]
  | imp A B ihA ihB =>
    simp only [toLL, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [impLin, pol, Pol.plus, Pol.par,
      Pol.lolli, Pol.imp, Pol.dual]
  | iimp A B ihA ihB =>
    simp only [toLL, pol]
    cases hA : A.pol <;> cases hB : B.pol <;> simp_all [iimpLin, pol, Pol.lolli, Pol.iimp]
  | call A ihA =>
    simp only [toLL, pol]
    cases hA : A.pol <;> simp_all [callLin, pol, Pol.lall]
  | cex A ihA =>
    simp only [toLL, pol]
    cases hA : A.pol <;> simp_all [cexLin, pol, Pol.lex]
  | _ => simp_all [toLL, pol]

theorem isNeutralLinear_toLL (A : Formula) : A.toLL.IsNeutralLinear := by
  induction A with
  | atom p ts => unfold toLL atomLL; split <;> simp_all [IsNeutralLinear]
  | conj A B ihA ihB =>
    simp only [toLL]; cases A.pol <;> cases B.pol <;> simp_all [conjLin, IsNeutralLinear]
  | disj A B ihA ihB =>
    simp only [toLL]; cases A.pol <;> cases B.pol <;> simp_all [disjLin, IsNeutralLinear]
  | imp A B ihA ihB =>
    simp only [toLL]; cases A.pol <;> cases B.pol <;> simp_all [impLin, IsNeutralLinear]
  | iimp A B ihA ihB =>
    simp only [toLL]; cases A.pol <;> simp_all [iimpLin, IsNeutralLinear]
  | call A ihA => simp only [toLL]; cases A.pol <;> simp_all [callLin, IsNeutralLinear]
  | cex A ihA => simp only [toLL]; cases A.pol <;> simp_all [cexLin, IsNeutralLinear]
  | _ => simp_all [toLL, IsNeutralLinear]

theorem toLL_shiftFrom (c : ℕ) (A : Formula) : (A.shiftFrom c).toLL = A.toLL.shiftFrom c := by
  induction A generalizing c with
  | atom p ts => unfold shiftFrom toLL atomLL; split <;> simp [shiftFrom]
  | conj A B ihA ihB =>
    simp only [shiftFrom, toLL, pol_shiftFrom, ihA, ihB]
    cases A.pol <;> cases B.pol <;> simp [conjLin, shiftFrom]
  | disj A B ihA ihB =>
    simp only [shiftFrom, toLL, pol_shiftFrom, ihA, ihB]
    cases A.pol <;> cases B.pol <;> simp [disjLin, shiftFrom]
  | imp A B ihA ihB =>
    simp only [shiftFrom, toLL, pol_shiftFrom, ihA, ihB]
    cases A.pol <;> cases B.pol <;> simp [impLin, shiftFrom]
  | iimp A B ihA ihB =>
    simp only [shiftFrom, toLL, pol_shiftFrom, ihA, ihB]
    cases A.pol <;> simp [iimpLin, shiftFrom]
  | call A ih =>
    simp only [shiftFrom, toLL, pol_shiftFrom, ih]; cases A.pol <;> simp [callLin, shiftFrom]
  | cex A ih =>
    simp only [shiftFrom, toLL, pol_shiftFrom, ih]; cases A.pol <;> simp [cexLin, shiftFrom]
  | _ => simp_all [shiftFrom, toLL]

theorem toLL_substAt (k : ℕ) (s : Term) (A : Formula) :
    (A.substAt k s).toLL = A.toLL.substAt k s := by
  induction A generalizing k s with
  | atom p ts => unfold substAt toLL atomLL; split <;> simp [substAt]
  | conj A B ihA ihB =>
    simp only [substAt, toLL, pol_substAt, ihA, ihB]
    cases A.pol <;> cases B.pol <;> simp [conjLin, substAt]
  | disj A B ihA ihB =>
    simp only [substAt, toLL, pol_substAt, ihA, ihB]
    cases A.pol <;> cases B.pol <;> simp [disjLin, substAt]
  | imp A B ihA ihB =>
    simp only [substAt, toLL, pol_substAt, ihA, ihB]
    cases A.pol <;> cases B.pol <;> simp [impLin, substAt]
  | iimp A B ihA ihB =>
    simp only [substAt, toLL, pol_substAt, ihA, ihB]
    cases A.pol <;> simp [iimpLin, substAt]
  | call A ih =>
    simp only [substAt, toLL, pol_substAt, ih]; cases A.pol <;> simp [callLin, substAt]
  | cex A ih =>
    simp only [substAt, toLL, pol_substAt, ih]; cases A.pol <;> simp [cexLin, substAt]
  | _ => simp_all [substAt, toLL]

theorem toLL_inst (A : Formula) (t : Term) : (A.inst t).toLL = A.toLL.inst t :=
  toLL_substAt 0 t A

end Formula

theorem map_toLL_sh (Γ : Multiset Formula) : (sh Γ).map toLL = sh (Γ.map toLL) := by
  simp [sh, Multiset.map_map, Formula.shift, toLL_shiftFrom]

/-! ## Table 3 for the various polarity cases -/

namespace Formula

variable {a b : Pol} {X Y : Formula}

theorem conjLin_PQ (ha : a = .pos) (hb : b = .pos) : conjLin a b X Y = tensor X Y := by
  subst ha hb; rfl
theorem conjLin_AQ (ha : a ≠ .pos) (hb : b = .pos) : conjLin a b X Y = tensor (bang X) Y := by
  subst hb; cases a <;> simp_all [conjLin]
theorem conjLin_PB (ha : a = .pos) (hb : b ≠ .pos) : conjLin a b X Y = tensor X (bang Y) := by
  subst ha; cases b <;> simp_all [conjLin]
theorem conjLin_AB (ha : a ≠ .pos) (hb : b ≠ .pos) : conjLin a b X Y = with_ X Y := by
  cases a <;> cases b <;> simp_all [conjLin]
theorem iimpLin_P (ha : a = .pos) : iimpLin a X Y = lolli X Y := by subst ha; rfl
theorem iimpLin_A (ha : a ≠ .pos) : iimpLin a X Y = lolli (bang X) Y := by
  cases a <;> simp_all [iimpLin]
theorem callLin_N (ha : a = .neg) : callLin a X = lall X := by subst ha; rfl
theorem callLin_A (ha : a ≠ .neg) : callLin a X = lall (quest X) := by
  cases a <;> simp_all [callLin]
theorem cexLin_P (ha : a = .pos) : cexLin a X = lex X := by subst ha; rfl
theorem cexLin_A (ha : a ≠ .pos) : cexLin a X = lex (bang X) := by
  cases a <;> simp_all [cexLin]

end Formula

/-! ## Soundness -/

/-- Translation of a context. -/
abbrev tL (Γ : Multiset Formula) : Multiset Formula := Γ.map toLL
/-- Translation of a left central context: `!Γ*`. -/
abbrev bL (Γ : Multiset Formula) : Multiset Formula := (Γ.map toLL).map bang
/-- Translation of a right central context: `?Δ*`. -/
abbrev qL (Δ : Multiset Formula) : Multiset Formula := (Δ.map toLL).map quest

/-- Close an equation between translated multisets. -/
local macro "mset_tac3" : tactic => `(tactic| ((try simp only [← Multiset.singleton_add,
  Multiset.insert_eq_cons, sh, tL, bL, qL, Multiset.map_add, Multiset.map_singleton,
  Multiset.map_zero, Multiset.map_cons, toLL, toLL_inst]) <;>
  (try simp only [← Multiset.singleton_add]) <;> abel))

/-- As `mset_tac3`, also rewriting with the given equations. -/
local macro "mset_tac3w " e:term : tactic => `(tactic| ((try simp only
  [← Multiset.singleton_add, Multiset.insert_eq_cons, sh, tL, bL, qL, Multiset.map_add,
  Multiset.map_singleton, Multiset.map_zero, Multiset.map_cons, toLL, toLL_inst, $e:term]) <;>
  (try simp only [← Multiset.singleton_add]) <;> abel))

/-- `llc h`: use `h` up to an equation between the multisets of both sides. -/
local macro "llc " h:term : term => `(LL.congr $h (by mset_tac3) (by mset_tac3))
/-- `llcw e h`: as `llc`, also rewriting with the equations `e`. -/
local macro "llcw " e:term:max h:term:max : term =>
  `(LL.congr $h (by mset_tac3w $e) (by mset_tac3w $e))

theorem pos_toLL {A : Formula} (h : A.pol = .pos) : LL true {A.toLL} {bang A.toLL} :=
  (isNeutralLinear_toLL A).bang_quest.1 (by rw [pol_toLL]; exact h)

theorem neg_toLL {A : Formula} (h : A.pol = .neg) : LL true {quest A.toLL} {A.toLL} :=
  (isNeutralLinear_toLL A).bang_quest.2 (by rw [pol_toLL]; exact h)

theorem LL.questD' (A : Formula) : LL true {A} {quest A} :=
  LL.questD (LL.ax A : LL true {A} (A ::ₘ 0))

set_option maxHeartbeats 8000000 in
/-- **Soundness of LU with respect to Table 3.**  If `Γ;Γ' ⊢ Δ';Δ` is provable in LU (with
cuts), then `Γ*, !Γ'* ⊢ ?Δ'*, Δ*` is provable in linear logic (with cut), where `A* = A.toLL`
is the decomposition of Table 3 (with positive atoms read as `!p` and negative ones as
`?p`). -/
theorem LL.of_provable_table3 {S : Sequent} (h : Provable S) :
    LL true (S.L.map toLL + (S.CL.map toLL).map bang)
      ((S.CR.map toLL).map quest + S.R.map toLL) := by
  induction h with
  | mk ps c hr _ hps ih =>
  clear hps
  rcases hr with hr | hr
  · cases hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        IsEmpty.forall_iff, implies_true] at ih <;>
      dsimp only at ih ⊢
    case ax A => exact llc (LL.ax A.toLL)
    case weakR Γ Γ' Δ' Δ A => exact llc (LL.questW A.toLL ih)
    case weakL Γ Γ' Δ' Δ A => exact llc (LL.bangW A.toLL ih)
    case contrR Γ Γ' Δ' Δ A =>
      have h1 : LL true (tL Γ + bL Γ') (quest A.toLL ::ₘ quest A.toLL ::ₘ (qL Δ' + tL Δ)) :=
        llc ih
      exact llc (LL.questC h1)
    case contrL Γ Γ' Δ' Δ A =>
      have h1 : LL true (bang A.toLL ::ₘ bang A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) :=
        llc ih
      exact llc (LL.bangC h1)
    case inR Γ Γ' Δ' Δ A =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.questD h1)
    case inL Γ Γ' Δ' Δ A =>
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.bangD h1)
    case outR Γ Γ' Δ' Δ N hN =>
      have h1 : LL true (tL Γ + bL Γ') (quest N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.cut' (Λ := 0) _ h1 (neg_toLL hN))
    case outL Γ Γ' Δ' Δ P hP =>
      have h1 : LL true (bang P.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.cut' _ (pos_toLL hP) h1)
    case oneR => exact llc LL.oneR
    case botL => exact llc LL.botL
    case tensorR Γ Λ Γ' Δ' Δ Θ A B =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (tL Λ + bL Γ') (B.toLL ::ₘ (qL Δ' + tL Θ)) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (tL Γ + tL Λ))
          (qL Δ' + qL Δ' + (tensor A.toLL B.toLL ::ₘ (tL Δ + tL Θ))) := llc (LL.tensorR h1 h2)
      exact llc (LL.contr_central h3)
    case tensorL Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A.toLL ::ₘ B.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.tensorL h1)
    case parR Γ Γ' Δ' Δ A B =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.parR h1)
    case parL Γ Λ Γ' Δ' Δ Θ A B =>
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (B.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (par A.toLL B.toLL ::ₘ (tL Γ + tL Λ)))
          (qL Δ' + qL Δ' + (tL Δ + tL Θ)) := llc (LL.parL h1 h2)
      exact llc (LL.contr_central h3)
    case lolliR Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.lolliR h1)
    case lolliL Γ Λ Γ' Δ' Δ Θ A B =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (B.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (lolli A.toLL B.toLL ::ₘ (tL Γ + tL Λ)))
          (qL Δ' + qL Δ' + (tL Δ + tL Θ)) := llc (LL.lolliL h1 h2)
      exact llc (LL.contr_central h3)
    case topR Γ Δ => exact llc (LL.topR (tL Γ) (tL Δ))
    case zeroL Γ Δ => exact llc (LL.zeroL (tL Γ) (tL Δ))
    case withR Γ Γ' Δ' Δ A B =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (tL Γ + bL Γ') (B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.2
      exact llc (LL.withR h1 h2)
    case withL₁ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.withL₁ B.toLL h1)
    case withL₂ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (B.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.withL₂ A.toLL h1)
    case plusR₁ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.plusR₁ B.toLL h1)
    case plusR₂ Γ Γ' Δ' Δ A B =>
      have h1 : LL true (tL Γ + bL Γ') (B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.plusR₂ A.toLL h1)
    case plusL Γ Γ' Δ' Δ A B =>
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (B.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.2
      exact llc (LL.plusL h1 h2)
    case negL Γ Γ' Δ' Δ A =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.negL h1)
    case negR Γ Γ' Δ' Δ A =>
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.negR h1)
    case bangR Γ' Δ' A =>
      have h1 : LL true (bL Γ') (A.toLL ::ₘ qL Δ') := llc ih
      exact llc (LL.bangR h1)
    case bangL Γ Γ' Δ' Δ A => exact llc ih
    case questR Γ Γ' Δ' Δ A => exact llc ih
    case questL Γ' Δ' A =>
      have h1 : LL true (A.toLL ::ₘ bL Γ') (qL Δ') := llc ih
      exact llc (LL.questL h1)
    case lallR Γ Γ' Δ' Δ A =>
      have h1 : LL true (sh (tL Γ + bL Γ')) (A.toLL ::ₘ sh (qL Δ' + tL Δ)) := by
        simp only [tL, bL, qL, sh_add, sh_map_bang, sh_map_quest, ← map_toLL_sh]; exact llc ih
      exact llc (LL.lallR h1)
    case lallL Γ Γ' Δ' Δ A t =>
      have h1 : LL true (A.toLL.inst t ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llc (LL.lallL t h1)
    case lexR Γ Γ' Δ' Δ A t =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL.inst t ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llc (LL.lexR t h1)
    case lexL Γ Γ' Δ' Δ A =>
      have h1 : LL true (A.toLL ::ₘ sh (tL Γ + bL Γ')) (sh (qL Δ' + tL Δ)) := by
        simp only [tL, bL, qL, sh_add, sh_map_bang, sh_map_quest, ← map_toLL_sh]; exact llc ih
      exact llc (LL.lexL h1)
    case conjR_PQ Γ Λ Γ' Δ' Δ Θ P Q hP hQ =>
      have e : conjLin P.pol Q.pol P.toLL Q.toLL = tensor P.toLL Q.toLL := conjLin_PQ hP hQ
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (tL Λ + bL Γ') (Q.toLL ::ₘ (qL Δ' + tL Θ)) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (tL Γ + tL Λ))
          (qL Δ' + qL Δ' + (tensor P.toLL Q.toLL ::ₘ (tL Δ + tL Θ))) := llc (LL.tensorR h1 h2)
      exact llcw e (LL.contr_central h3)
    case conjL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
      have e : conjLin P.pol Q.pol P.toLL Q.toLL = tensor P.toLL Q.toLL := conjLin_PQ hP hQ
      have h1 : LL true (P.toLL ::ₘ Q.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.tensorL h1)
    case conjR_AQ Λ Γ' Δ' Θ A Q hA hQ =>
      have e : conjLin A.pol Q.pol A.toLL Q.toLL = tensor (bang A.toLL) Q.toLL :=
        conjLin_AQ hA hQ
      have h1 : LL true (bL Γ') (A.toLL ::ₘ qL Δ') := llc ih.1
      have h2 : LL true (tL Λ + bL Γ') (Q.toLL ::ₘ (qL Δ' + tL Θ)) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + tL Λ)
          (qL Δ' + qL Δ' + (tensor (bang A.toLL) Q.toLL ::ₘ tL Θ)) :=
        llc (LL.tensorR (LL.bangR h1) h2)
      exact llcw e (LL.contr_central h3)
    case conjL_AQ Γ Γ' Δ' Δ A Q hA hQ =>
      have e : conjLin A.pol Q.pol A.toLL Q.toLL = tensor (bang A.toLL) Q.toLL :=
        conjLin_AQ hA hQ
      have h1 : LL true (bang A.toLL ::ₘ Q.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.tensorL h1)
    case conjR_PB Γ Γ' Δ' Δ P B hP hB =>
      have e : conjLin P.pol B.pol P.toLL B.toLL = tensor P.toLL (bang B.toLL) :=
        conjLin_PB hP hB
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (bL Γ') (B.toLL ::ₘ qL Δ') := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + tL Γ)
          (qL Δ' + qL Δ' + (tensor P.toLL (bang B.toLL) ::ₘ tL Δ)) :=
        llc (LL.tensorR h1 (LL.bangR h2))
      exact llcw e (LL.contr_central h3)
    case conjL_PB Γ Γ' Δ' Δ P B hP hB =>
      have e : conjLin P.pol B.pol P.toLL B.toLL = tensor P.toLL (bang B.toLL) :=
        conjLin_PB hP hB
      have h1 : LL true (P.toLL ::ₘ bang B.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.tensorL h1)
    case conjR_AB Γ Γ' Δ' Δ A B hA hB =>
      have e : conjLin A.pol B.pol A.toLL B.toLL = with_ A.toLL B.toLL := conjLin_AB hA hB
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (tL Γ + bL Γ') (B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.2
      exact llcw e (LL.withR h1 h2)
    case conjL_AB₁ Γ Γ' Δ' Δ A B hA hB =>
      have e : conjLin A.pol B.pol A.toLL B.toLL = with_ A.toLL B.toLL := conjLin_AB hA hB
      have h1 : LL true (A.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.withL₁ B.toLL h1)
    case conjL_AB₂ Γ Γ' Δ' Δ A B hA hB =>
      have e : conjLin A.pol B.pol A.toLL B.toLL = with_ A.toLL B.toLL := conjLin_AB hA hB
      have h1 : LL true (B.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.withL₂ A.toLL h1)
    case iimpR_P Γ Γ' Δ' Δ P B hP =>
      have e : iimpLin P.pol P.toLL B.toLL = lolli P.toLL B.toLL := iimpLin_P hP
      have h1 : LL true (P.toLL ::ₘ (tL Γ + bL Γ')) (B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.lolliR h1)
    case iimpL_P Γ Λ Γ' Δ' Δ Θ P B hP =>
      have e : iimpLin P.pol P.toLL B.toLL = lolli P.toLL B.toLL := iimpLin_P hP
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (B.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (lolli P.toLL B.toLL ::ₘ (tL Γ + tL Λ)))
          (qL Δ' + qL Δ' + (tL Δ + tL Θ)) := llc (LL.lolliL h1 h2)
      exact llcw e (LL.contr_central h3)
    case iimpR_A Γ Γ' Δ' Δ A B hA =>
      have e : iimpLin A.pol A.toLL B.toLL = lolli (bang A.toLL) B.toLL := iimpLin_A hA
      have h1 : LL true (bang A.toLL ::ₘ (tL Γ + bL Γ')) (B.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.lolliR h1)
    case iimpL_A Λ Γ' Δ' Θ A B hA =>
      have e : iimpLin A.pol A.toLL B.toLL = lolli (bang A.toLL) B.toLL := iimpLin_A hA
      have h1 : LL true (bL Γ') (A.toLL ::ₘ qL Δ') := llc ih.1
      have h2 : LL true (B.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (lolli (bang A.toLL) B.toLL ::ₘ tL Λ))
          (qL Δ' + qL Δ' + tL Θ) := llc (LL.lolliL (LL.bangR h1) h2)
      exact llcw e (LL.contr_central h3)
    case callR_A Γ Γ' Δ' Δ A hA =>
      have e : callLin A.pol A.toLL = lall (quest A.toLL) := callLin_A hA
      have h1 : LL true (sh (tL Γ + bL Γ')) (quest A.toLL ::ₘ sh (qL Δ' + tL Δ)) := by
        simp only [tL, bL, qL, sh_add, sh_map_bang, sh_map_quest, ← map_toLL_sh]; exact llc ih
      exact llcw e (LL.lallR h1)
    case callL_A Γ' Δ' A t hA =>
      have e : callLin A.pol A.toLL = lall (quest A.toLL) := callLin_A hA
      have h1 : LL true (A.toLL.inst t ::ₘ bL Γ') (qL Δ') := llc ih
      have h2 : LL true ((quest A.toLL).inst t ::ₘ bL Γ') (qL Δ') := LL.questL h1
      exact llcw e (LL.lallL t h2)
    case callR_N Γ Γ' Δ' Δ N hN =>
      have e : callLin N.pol N.toLL = lall N.toLL := callLin_N hN
      have h1 : LL true (sh (tL Γ + bL Γ')) (N.toLL ::ₘ sh (qL Δ' + tL Δ)) := by
        simp only [tL, bL, qL, sh_add, sh_map_bang, sh_map_quest, ← map_toLL_sh]; exact llc ih
      exact llcw e (LL.lallR h1)
    case callL_N Γ Γ' Δ' Δ N t hN =>
      have e : callLin N.pol N.toLL = lall N.toLL := callLin_N hN
      have h1 : LL true (N.toLL.inst t ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.lallL t h1)
    case cexR_P Γ Γ' Δ' Δ P t hP =>
      have e : cexLin P.pol P.toLL = lex P.toLL := cexLin_P hP
      have h1 : LL true (tL Γ + bL Γ') (P.toLL.inst t ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.lexR t h1)
    case cexL_P Λ Λ' Θ' Θ P hP =>
      have e : cexLin P.pol P.toLL = lex P.toLL := cexLin_P hP
      have h1 : LL true (P.toLL ::ₘ sh (tL Λ + bL Λ')) (sh (qL Θ' + tL Θ)) := by
        simp only [tL, bL, qL, sh_add, sh_map_bang, sh_map_quest, ← map_toLL_sh]; exact llc ih
      exact llcw e (LL.lexL h1)
    case cexR_A Γ' Δ' A t hA =>
      have e : cexLin A.pol A.toLL = lex (bang A.toLL) := cexLin_A hA
      have h1 : LL true (bL Γ') (A.toLL.inst t ::ₘ qL Δ') := llc ih
      have h2 : LL true (bL Γ') ((bang A.toLL).inst t ::ₘ qL Δ') := LL.bangR h1
      exact llcw e (LL.lexR t h2)
    case cexL_A Λ Λ' Θ' Θ A hA =>
      have e : cexLin A.pol A.toLL = lex (bang A.toLL) := cexLin_A hA
      have h1 : LL true (bang A.toLL ::ₘ sh (tL Λ + bL Λ')) (sh (qL Θ' + tL Θ)) := by
        simp only [tL, bL, qL, sh_add, sh_map_bang, sh_map_quest, ← map_toLL_sh]; exact llc ih
      exact llcw e (LL.lexL h1)
    case disjR₁_PQ Γ Γ' Δ' Δ P Q hP hQ =>
      have e : disjLin P.pol Q.pol P.toLL Q.toLL = plus P.toLL Q.toLL := by rw [hP, hQ]; rfl
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.plusR₁ Q.toLL h1)
    case disjR₂_PQ Γ Γ' Δ' Δ P Q hP hQ =>
      have e : disjLin P.pol Q.pol P.toLL Q.toLL = plus P.toLL Q.toLL := by rw [hP, hQ]; rfl
      have h1 : LL true (tL Γ + bL Γ') (Q.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.plusR₂ P.toLL h1)
    case disjL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
      have e : disjLin P.pol Q.pol P.toLL Q.toLL = plus P.toLL Q.toLL := by rw [hP, hQ]; rfl
      have h1 : LL true (P.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (Q.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.2
      exact llcw e (LL.plusL h1 h2)
    case disjR₁_SQ Γ' Δ' S Q hS hQ =>
      have e : disjLin S.pol Q.pol S.toLL Q.toLL = plus (bang S.toLL) Q.toLL := by
        rw [hS, hQ]; rfl
      have h1 : LL true (bL Γ') (S.toLL ::ₘ qL Δ') := llc ih
      exact llcw e (LL.plusR₁ Q.toLL (LL.bangR h1))
    case disjR₂_SQ Γ Γ' Δ' Δ S Q hS hQ =>
      have e : disjLin S.pol Q.pol S.toLL Q.toLL = plus (bang S.toLL) Q.toLL := by
        rw [hS, hQ]; rfl
      have h1 : LL true (tL Γ + bL Γ') (Q.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.plusR₂ (bang S.toLL) h1)
    case disjL_SQ Γ Γ' Δ' Δ S Q hS hQ =>
      have e : disjLin S.pol Q.pol S.toLL Q.toLL = plus (bang S.toLL) Q.toLL := by
        rw [hS, hQ]; rfl
      have h1 : LL true (bang S.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (Q.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.2
      exact llcw e (LL.plusL h1 h2)
    case disjR_MQ Γ Γ' Δ' Δ M Q hM hQ =>
      have e : disjLin M.pol Q.pol M.toLL Q.toLL = par M.toLL (quest Q.toLL) := by
        rw [hM, hQ]; rfl
      have h1 : LL true (tL Γ + bL Γ') (M.toLL ::ₘ quest Q.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.parR h1)
    case disjL_MQ Γ Γ' Δ' Δ M Q hM hQ =>
      have e : disjLin M.pol Q.pol M.toLL Q.toLL = par M.toLL (quest Q.toLL) := by
        rw [hM, hQ]; rfl
      have h1 : LL true (M.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (bang Q.toLL ::ₘ bL Γ') (qL Δ') := llc ih.2
      have h3 : LL true (Q.toLL ::ₘ bL Γ') (qL Δ') := llc (LL.cut' _ (pos_toLL hQ) h2)
      have h4 : LL true (bL Γ' + bL Γ' + (par M.toLL (quest Q.toLL) ::ₘ tL Γ))
          (qL Δ' + qL Δ' + tL Δ) := llc (LL.parL h1 (LL.questL h3))
      exact llcw e (LL.contr_central h4)
    case disjR₁_PT Γ Γ' Δ' Δ P T hP hT =>
      have e : disjLin P.pol T.pol P.toLL T.toLL = plus P.toLL (bang T.toLL) := by
        rw [hP, hT]; rfl
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.plusR₁ (bang T.toLL) h1)
    case disjR₂_PT Γ' Δ' P T hP hT =>
      have e : disjLin P.pol T.pol P.toLL T.toLL = plus P.toLL (bang T.toLL) := by
        rw [hP, hT]; rfl
      have h1 : LL true (bL Γ') (T.toLL ::ₘ qL Δ') := llc ih
      exact llcw e (LL.plusR₂ P.toLL (LL.bangR h1))
    case disjL_PT Γ Γ' Δ' Δ P T hP hT =>
      have e : disjLin P.pol T.pol P.toLL T.toLL = plus P.toLL (bang T.toLL) := by
        rw [hP, hT]; rfl
      have h1 : LL true (P.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (bang T.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.2
      exact llcw e (LL.plusL h1 h2)
    case disjR₁_ST Γ' Δ' S T hS hT =>
      have e : disjLin S.pol T.pol S.toLL T.toLL = plus (bang S.toLL) (bang T.toLL) := by
        rw [hS, hT]; rfl
      have h1 : LL true (bL Γ') (S.toLL ::ₘ qL Δ') := llc ih
      exact llcw e (LL.plusR₁ (bang T.toLL) (LL.bangR h1))
    case disjR₂_ST Γ' Δ' S T hS hT =>
      have e : disjLin S.pol T.pol S.toLL T.toLL = plus (bang S.toLL) (bang T.toLL) := by
        rw [hS, hT]; rfl
      have h1 : LL true (bL Γ') (T.toLL ::ₘ qL Δ') := llc ih
      exact llcw e (LL.plusR₂ (bang S.toLL) (LL.bangR h1))
    case disjL_ST Γ Γ' Δ' Δ S T hS hT =>
      have e : disjLin S.pol T.pol S.toLL T.toLL = plus (bang S.toLL) (bang T.toLL) := by
        rw [hS, hT]; rfl
      have h1 : LL true (bang S.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (bang T.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.2
      exact llcw e (LL.plusL h1 h2)
    case disjR₁_MT Γ Γ' Δ' Δ M T hM hT =>
      have e : disjLin M.pol T.pol M.toLL T.toLL = par M.toLL (quest (bang T.toLL)) := by
        rw [hM, hT]; rfl
      have h1 : LL true (tL Γ + bL Γ') (M.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      have h2 : LL true (tL Γ + bL Γ') (M.toLL ::ₘ quest (bang T.toLL) ::ₘ (qL Δ' + tL Δ)) :=
        llc (LL.questW (bang T.toLL) h1)
      exact llcw e (LL.parR h2)
    case disjR₂_MT Γ' Δ' M T hM hT =>
      have e : disjLin M.pol T.pol M.toLL T.toLL = par M.toLL (quest (bang T.toLL)) := by
        rw [hM, hT]; rfl
      have h1 : LL true (bL Γ') (M.toLL ::ₘ T.toLL ::ₘ qL Δ') := llc ih
      have h2 : LL true (bL Γ') (quest M.toLL ::ₘ T.toLL ::ₘ qL Δ') :=
        llc (LL.cut' (Λ := 0) _ h1 (LL.questD' M.toLL))
      have h3 : LL true (Multiset.map bang (Γ'.map toLL))
          (T.toLL ::ₘ Multiset.map quest (M.toLL ::ₘ Δ'.map toLL)) := llc h2
      have h4 : LL true (bL Γ') (quest M.toLL ::ₘ quest (bang T.toLL) ::ₘ qL Δ') :=
        llc (LL.questD (LL.bangR h3))
      have h5 : LL true (bL Γ') (M.toLL ::ₘ quest (bang T.toLL) ::ₘ qL Δ') :=
        llc (LL.cut' (Λ := 0) _ h4 (neg_toLL hM))
      exact llcw e (LL.parR h5)
    case disjL_MT Γ Γ' Δ' Δ M T hM hT =>
      have e : disjLin M.pol T.pol M.toLL T.toLL = par M.toLL (quest (bang T.toLL)) := by
        rw [hM, hT]; rfl
      have h1 : LL true (M.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (bang T.toLL ::ₘ bL Γ') (qL Δ') := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (par M.toLL (quest (bang T.toLL)) ::ₘ tL Γ))
          (qL Δ' + qL Δ' + tL Δ) := llc (LL.parL h1 (LL.questL h2))
      exact llcw e (LL.contr_central h3)
    case disjR_PN Γ Γ' Δ' Δ P N hP hN =>
      have e : disjLin P.pol N.pol P.toLL N.toLL = par (quest P.toLL) N.toLL := by
        rw [hP, hN]; rfl
      have h1 : LL true (tL Γ + bL Γ') (quest P.toLL ::ₘ N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.parR h1)
    case disjL_PN Λ Γ' Δ' Θ P N hP hN =>
      have e : disjLin P.pol N.pol P.toLL N.toLL = par (quest P.toLL) N.toLL := by
        rw [hP, hN]; rfl
      have h1 : LL true (P.toLL ::ₘ bL Γ') (qL Δ') := llc ih.1
      have h2 : LL true (N.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (par (quest P.toLL) N.toLL ::ₘ tL Λ))
          (qL Δ' + qL Δ' + tL Θ) := llc (LL.parL (LL.questL h1) h2)
      exact llcw e (LL.contr_central h3)
    case disjR₁_SN Γ' Δ' S N hS hN =>
      have e : disjLin S.pol N.pol S.toLL N.toLL = par (quest (bang S.toLL)) N.toLL := by
        rw [hS, hN]; rfl
      have h1 : LL true (bL Γ') (N.toLL ::ₘ S.toLL ::ₘ qL Δ') := llc ih
      have h2 : LL true (bL Γ') (quest N.toLL ::ₘ S.toLL ::ₘ qL Δ') :=
        llc (LL.cut' (Λ := 0) _ h1 (LL.questD' N.toLL))
      have h3 : LL true (Multiset.map bang (Γ'.map toLL))
          (S.toLL ::ₘ Multiset.map quest (N.toLL ::ₘ Δ'.map toLL)) := llc h2
      have h4 : LL true (bL Γ') (quest N.toLL ::ₘ quest (bang S.toLL) ::ₘ qL Δ') :=
        llc (LL.questD (LL.bangR h3))
      have h5 : LL true (bL Γ') (quest (bang S.toLL) ::ₘ N.toLL ::ₘ qL Δ') :=
        llc (LL.cut' (Λ := 0) _ h4 (neg_toLL hN))
      exact llcw e (LL.parR h5)
    case disjR₂_SN Γ Γ' Δ' Δ S N hS hN =>
      have e : disjLin S.pol N.pol S.toLL N.toLL = par (quest (bang S.toLL)) N.toLL := by
        rw [hS, hN]; rfl
      have h1 : LL true (tL Γ + bL Γ') (N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      have h2 : LL true (tL Γ + bL Γ') (quest (bang S.toLL) ::ₘ N.toLL ::ₘ (qL Δ' + tL Δ)) :=
        llc (LL.questW (bang S.toLL) h1)
      exact llcw e (LL.parR h2)
    case disjL_SN Λ Γ' Δ' Θ S N hS hN =>
      have e : disjLin S.pol N.pol S.toLL N.toLL = par (quest (bang S.toLL)) N.toLL := by
        rw [hS, hN]; rfl
      have h1 : LL true (bang S.toLL ::ₘ bL Γ') (qL Δ') := llc ih.1
      have h2 : LL true (N.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (par (quest (bang S.toLL)) N.toLL ::ₘ tL Λ))
          (qL Δ' + qL Δ' + tL Θ) := llc (LL.parL (LL.questL h1) h2)
      exact llcw e (LL.contr_central h3)
    case disjR_MN Γ Γ' Δ' Δ M N hM hN =>
      have e : disjLin M.pol N.pol M.toLL N.toLL = par M.toLL N.toLL := by rw [hM, hN]; rfl
      have h1 : LL true (tL Γ + bL Γ') (M.toLL ::ₘ N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.parR h1)
    case disjL_MN Γ Λ Γ' Δ' Δ Θ M N hM hN =>
      have e : disjLin M.pol N.pol M.toLL N.toLL = par M.toLL N.toLL := by rw [hM, hN]; rfl
      have h1 : LL true (M.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.1
      have h2 : LL true (N.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (par M.toLL N.toLL ::ₘ (tL Γ + tL Λ)))
          (qL Δ' + qL Δ' + (tL Δ + tL Θ)) := llc (LL.parL h1 h2)
      exact llcw e (LL.contr_central h3)
    case impR₁_NP Γ Γ' Δ' Δ N P hN hP =>
      have e : impLin N.pol P.pol N.toLL P.toLL = plus (neg N.toLL) P.toLL := by
        rw [hN, hP]; rfl
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.plusR₂ (neg N.toLL) h1)
    case impR₂_NP Γ Γ' Δ' Δ N P hN hP =>
      have e : impLin N.pol P.pol N.toLL P.toLL = plus (neg N.toLL) P.toLL := by
        rw [hN, hP]; rfl
      have h1 : LL true (N.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih
      exact llcw e (LL.plusR₁ P.toLL (LL.negR h1))
    case impL_NP Γ Γ' Δ' Δ N P hN hP =>
      have e : impLin N.pol P.pol N.toLL P.toLL = plus (neg N.toLL) P.toLL := by
        rw [hN, hP]; rfl
      have h1 : LL true (tL Γ + bL Γ') (N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (P.toLL ::ₘ (tL Γ + bL Γ')) (qL Δ' + tL Δ) := llc ih.2
      exact llcw e (LL.plusL (LL.negL h1) h2)
    case impR_PQ Γ Γ' Δ' Δ P Q hP hQ =>
      have e : impLin P.pol Q.pol P.toLL Q.toLL = lolli P.toLL (quest Q.toLL) := by
        rw [hP, hQ]; rfl
      have h1 : LL true (P.toLL ::ₘ (tL Γ + bL Γ')) (quest Q.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.lolliR h1)
    case impL_PQ Γ Γ' Δ' Δ P Q hP hQ =>
      have e : impLin P.pol Q.pol P.toLL Q.toLL = lolli P.toLL (quest Q.toLL) := by
        rw [hP, hQ]; rfl
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (Q.toLL ::ₘ bL Γ') (qL Δ') := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (lolli P.toLL (quest Q.toLL) ::ₘ tL Γ))
          (qL Δ' + qL Δ' + tL Δ) := llc (LL.lolliL h1 (LL.questL h2))
      exact llcw e (LL.contr_central h3)
    case impR_MN Γ Γ' Δ' Δ M N hM hN =>
      have e : impLin M.pol N.pol M.toLL N.toLL = lolli (bang M.toLL) N.toLL := by
        rw [hM, hN]; rfl
      have h1 : LL true (bang M.toLL ::ₘ (tL Γ + bL Γ')) (N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.lolliR h1)
    case impL_MN Λ Γ' Δ' Θ M N hM hN =>
      have e : impLin M.pol N.pol M.toLL N.toLL = lolli (bang M.toLL) N.toLL := by
        rw [hM, hN]; rfl
      have h1 : LL true (bL Γ') (M.toLL ::ₘ qL Δ') := llc ih.1
      have h2 : LL true (N.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (lolli (bang M.toLL) N.toLL ::ₘ tL Λ))
          (qL Δ' + qL Δ' + tL Θ) := llc (LL.lolliL (LL.bangR h1) h2)
      exact llcw e (LL.contr_central h3)
    case impR_PN Γ Γ' Δ' Δ P N hP hN =>
      have e : impLin P.pol N.pol P.toLL N.toLL = lolli P.toLL N.toLL := by rw [hP, hN]; rfl
      have h1 : LL true (P.toLL ::ₘ (tL Γ + bL Γ')) (N.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih
      exact llcw e (LL.lolliR h1)
    case impL_PN Γ Λ Γ' Δ' Δ Θ P N hP hN =>
      have e : impLin P.pol N.pol P.toLL N.toLL = lolli P.toLL N.toLL := by rw [hP, hN]; rfl
      have h1 : LL true (tL Γ + bL Γ') (P.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (N.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (lolli P.toLL N.toLL ::ₘ (tL Γ + tL Λ)))
          (qL Δ' + qL Δ' + (tL Δ + tL Θ)) := llc (LL.lolliL h1 h2)
      exact llcw e (LL.contr_central h3)
  · cases hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ih <;>
      dsimp only at ih ⊢
    case cut Γ Λ Γ' Δ' Δ Θ A =>
      have h1 : LL true (tL Γ + bL Γ') (A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (A.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + (tL Γ + tL Λ))
          (qL Δ' + qL Δ' + (tL Δ + tL Θ)) := llc (LL.cut' _ h1 h2)
      exact llc (LL.contr_central h3)
    case cutR Γ Γ' Δ' Δ A =>
      have h1 : LL true (tL Γ + bL Γ') (quest A.toLL ::ₘ (qL Δ' + tL Δ)) := llc ih.1
      have h2 : LL true (A.toLL ::ₘ bL Γ') (qL Δ') := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + tL Γ) (qL Δ' + qL Δ' + tL Δ) :=
        llc (LL.cut' _ h1 (LL.questL h2))
      exact llc (LL.contr_central h3)
    case cutL Λ Γ' Δ' Θ A =>
      have h1 : LL true (bL Γ') (A.toLL ::ₘ qL Δ') := llc ih.1
      have h2 : LL true (bang A.toLL ::ₘ (tL Λ + bL Γ')) (qL Δ' + tL Θ) := llc ih.2
      have h3 : LL true (bL Γ' + bL Γ' + tL Λ) (qL Δ' + qL Δ' + tL Θ) :=
        llc (LL.cut' _ (LL.bangR h1) h2)
      exact llc (LL.contr_central h3)

/-- Soundness w.r.t. Table 3 for sequents `Γ; ⊢ ;Δ`: `Γ* ⊢ Δ*` is provable in linear logic. -/
theorem LL.of_provable_table3_linear {Γ Δ : Multiset Formula}
    (h : Provable ⟪Γ ; 0 ⊢ 0 ; Δ⟫) : LL true (Γ.map toLL) (Δ.map toLL) := by
  simpa using LL.of_provable_table3 h

/-- **Soundness w.r.t. Table 3, neutral atoms.**  If all atoms are neutral and `Γ; ⊢ ;Δ` is
provable in LU, then the Table 3 decomposition `toLinear` gives an LL-provable sequent. -/
theorem LL.of_provable_toLinear {Γ Δ : Multiset Formula} (hΓ : ∀ A ∈ Γ, A.AtomsNeutral)
    (hΔ : ∀ A ∈ Δ, A.AtomsNeutral) (h : Provable ⟪Γ ; 0 ⊢ 0 ; Δ⟫) :
    LL true (Γ.map toLinear) (Δ.map toLinear) := by
  have e₁ : Γ.map toLL = Γ.map toLinear :=
    Multiset.map_congr rfl fun A hA => toLL_eq_toLinear (hΓ A hA)
  have e₂ : Δ.map toLL = Δ.map toLinear :=
    Multiset.map_congr rfl fun A hA => toLL_eq_toLinear (hΔ A hA)
  exact (LL.of_provable_table3_linear h).congr e₁ e₂

/-! ## §4 again: the equivalence of LU (neutral linear) and LL -/

/-- On linear formulas with neutral atoms the translation is the identity. -/
theorem Formula.toLL_of_isNeutralLinear {A : Formula} (h : A.IsNeutralLinear) : A.toLL = A := by
  induction A <;> simp_all [IsNeutralLinear, toLL, atomLL]

theorem map_toLL_of_neutralLinear {Γ : Multiset Formula} (h : ∀ A ∈ Γ, A.IsNeutralLinear) :
    Γ.map toLL = Γ := by
  conv_rhs => rw [← Multiset.map_id Γ]
  exact Multiset.map_congr rfl fun A hA => Formula.toLL_of_isNeutralLinear (h A hA)

/-- **§4: LU with neutral atoms is equivalent to linear logic.**  For linear formulas with
neutral atoms, `Γ; ⊢ ;Δ` is provable in LU (with cuts, on arbitrary formulas) iff `Γ ⊢ Δ` is
provable in linear logic. -/
theorem provable_iff_LL {Γ Δ : Multiset Formula} (hΓ : ∀ A ∈ Γ, A.IsNeutralLinear)
    (hΔ : ∀ A ∈ Δ, A.IsNeutralLinear) : Provable ⟪Γ ; 0 ⊢ 0 ; Δ⟫ ↔ LL true Γ Δ :=
  ⟨fun h => (LL.of_provable_table3_linear h).congr (map_toLL_of_neutralLinear hΓ)
    (map_toLL_of_neutralLinear hΔ), LL.provable⟩

/-- Cut elimination for linear logic (not proved here). -/
def LLCutElimination : Prop := ∀ Γ Δ : Multiset Formula, LL true Γ Δ → LL false Γ Δ

/-- Cut elimination for LU on linear sequents `Γ; ⊢ ;Δ` with neutral atoms reduces to cut
elimination for linear logic (taken as a hypothesis). -/
theorem cutFreeProvable_of_LLCutElimination (hLL : LLCutElimination) {Γ Δ : Multiset Formula}
    (hΓ : ∀ A ∈ Γ, A.IsNeutralLinear) (hΔ : ∀ A ∈ Δ, A.IsNeutralLinear)
    (h : Provable ⟪Γ ; 0 ⊢ 0 ; Δ⟫) : CutFreeProvable ⟪Γ ; 0 ⊢ 0 ; Δ⟫ :=
  LL.cutFreeProvable (hLL _ _ ((provable_iff_LL hΓ hΔ).1 h))

end LU
