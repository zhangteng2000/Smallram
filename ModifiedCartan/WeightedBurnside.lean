import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Module.BigOperators

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem burnsideEquiv_orbit {G X : Type*} [Group G] [MulAction G X]
    (p : Σ g : G, MulAction.fixedBy X g) :
    (MulAction.sigmaFixedByEquivOrbitsProdGroup G X p).1 =
      (Quotient.mk _ p.2.val : Quotient (MulAction.orbitRel G X)) := by
  rfl

/-- Weighted finite Burnside counting, with weights attached to actual orbits. -/
theorem sum_fixedBy_orbit_weights {G X V : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype X] [DecidableEq X] [AddCommMonoid V]
    (w : Quotient (MulAction.orbitRel G X) → V) :
    (∑ g : G, ∑ x : MulAction.fixedBy X g, w (Quotient.mk _ x.val)) =
      Fintype.card G • ∑ q : Quotient (MulAction.orbitRel G X), w q := by
  let e := MulAction.sigmaFixedByEquivOrbitsProdGroup G X
  calc
    _ = ∑ p : Σ g : G, MulAction.fixedBy X g, w (Quotient.mk _ p.2.val) :=
      (Fintype.sum_sigma _).symm
    _ = ∑ p : Quotient (MulAction.orbitRel G X) × G, w p.1 := by
      simpa only [e, burnsideEquiv_orbit] using e.sum_comp (fun p => w p.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ]
      rw [Finset.smul_sum]

end
end ModifiedCartan


