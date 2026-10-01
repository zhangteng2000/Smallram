import ModifiedCartan.EntireZeroCopies

open scoped Topology
open Filter Set Metric Function Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual copies of a locally finite integral divisor's positive multiplicities.
The point at the origin is included. Dependency of scalar `thm:A`. -/
abbrev divisorCopies (D : locallyFinsupp ℂ ℤ) := (z : ℂ) × Fin (D z).toNat

theorem divisorCopies_mem_support (D : locallyFinsupp ℂ ℤ) (a : divisorCopies D) :
    a.1 ∈ D.support := by
  change D a.1 ≠ 0
  intro he
  have ha := a.2.isLt
  simp [he] at ha

theorem divisorCopies_countable (D : locallyFinsupp ℂ ℤ) : Countable (divisorCopies D) := by
  letI : Countable D.support := (locallyFinsupp_support_countable D).to_subtype
  let e : divisorCopies D → D.support × ℕ :=
    fun a => (⟨a.1, divisorCopies_mem_support D a⟩, a.2.val)
  apply Function.Injective.countable (f := e)
  rintro ⟨z, i⟩ ⟨w, j⟩ h
  have hzw : z = w := congrArg (fun p => p.1.val) h
  have hij : i.val = j.val := congrArg Prod.snd h
  subst w
  exact congrArg (Sigma.mk z) (Fin.ext hij)

/-- Finitely many copies lie in each closed disk, without any growth assumption. -/
theorem divisorCopies_finite_in_closedBall (D : locallyFinsupp ℂ ℤ) (R : ℝ) :
    {a : divisorCopies D | ‖a.1‖ ≤ R}.Finite := by
  let S := (toClosedBall R D).support
  have hS : S.Finite := (toClosedBall R D).finiteSupport (isCompact_closedBall ..)
  have hfin : (⋃ z ∈ S, Set.range (fun i : Fin (D z).toNat => (⟨z, i⟩ : divisorCopies D))).Finite :=
    hS.biUnion (t := fun z => Set.range (fun i : Fin (D z).toNat => (⟨z, i⟩ : divisorCopies D)))
      (fun z _ => Set.finite_range _)
  apply hfin.subset
  rintro ⟨z, i⟩ hz
  refine mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨?_, ⟨i, rfl⟩⟩⟩
  change toClosedBall R D z ≠ 0
  rw [toClosedBall_eval_within D (by
    simpa only [mem_closedBall, dist_zero_right] using hz.trans (le_abs_self R))]
  exact divisorCopies_mem_support D ⟨z, i⟩

theorem divisorCopies_eventually_norm_gt (D : locallyFinsupp ℂ ℤ) (R : ℝ) :
    ∀ᶠ a : divisorCopies D in cofinite, R < ‖a.1‖ := by
  filter_upwards [(divisorCopies_finite_in_closedBall D R).compl_mem_cofinite] with a ha
  exact not_le.mp ha

/-- The finite fiber has precisely the prescribed multiplicity. -/
def divisorCopiesFiberEquiv (D : locallyFinsupp ℂ ℤ) (z : ℂ) :
    {a : divisorCopies D // a.1 = z} ≃ Fin (D z).toNat where
  toFun a := a.property ▸ a.val.2
  invFun i := ⟨⟨z, i⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨w, i⟩, h⟩
    dsimp only at h
    subst w
    rfl
  right_inv := by intro i; rfl

end ModifiedCartan
#print axioms ModifiedCartan.divisorCopies_countable
#print axioms ModifiedCartan.divisorCopies_finite_in_closedBall

