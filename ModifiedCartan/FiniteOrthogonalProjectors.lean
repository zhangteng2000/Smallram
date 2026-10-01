import ModifiedCartan.CharacterProjectorRange

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {I W : Type*} [Fintype I] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
theorem sum_orthogonal_projectors_idempotent (P : I → Module.End ℂ W)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0) :
    IsIdempotentElem (∑ i, P i) := by
  change (∑ i, P i) * (∑ i, P i) = ∑ i, P i
  simp only [Finset.sum_mul, Finset.mul_sum, hmul]
  simp

/-- A proved finite family of orthogonal projectors exhausts the space when
its traces add to the dimension. -/
theorem sum_orthogonal_projectors_eq_one (P : I → Module.End ℂ W)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (htrace : (∑ i, LinearMap.trace ℂ W (P i)) = (Module.finrank ℂ W : ℂ)) :
    (∑ i, P i) = 1 := by
  have hp := sum_orthogonal_projectors_idempotent P hmul
  have ht : LinearMap.trace ℂ W (1 - ∑ i, P i) = 0 := by
    rw [map_sub, LinearMap.trace_one, map_sum, htrace, sub_self]
  exact (sub_eq_zero.mp (LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hp.one_sub ht)).symm

end
end ModifiedCartan


