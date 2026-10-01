import ModifiedCartan.KPAlphaCoefficients

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem subgroup_finite_sum_coefficient {G R : Type*} [Group G] [Semiring R]
    (H : Subgroup G) [Fintype H] (f : H → R) (g : G) :
    (∑ h : H, MonoidAlgebra.single h.val (f h)).coeff g =
      if hg : g ∈ H then f ⟨g, hg⟩ else 0 := by
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hg : g ∈ H
  · rw [dite_eq_left hg, Finset.sum_eq_single (⟨g, hg⟩ : H)]
    · simp
    · intro h hh hn
      have he : h.val ≠ g := fun he => hn (Subtype.ext he)
      simp [he]
    · simp
  · rw [dite_eq_right hg]
    apply Finset.sum_eq_zero
    intro h hh
    have he : h.val ≠ g := fun he => hg (he ▸ h.property)
    simp [he]

end
end ModifiedCartan

