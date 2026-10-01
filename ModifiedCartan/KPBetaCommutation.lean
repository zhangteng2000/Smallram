import ModifiedCartan.SpechtKPCommutation
import ModifiedCartan.SpechtAlgebraFaithful

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- LaTeX `lem:KP-correspondence`, the commutativity assertion in item (i).
The parameters may repeat; both partitions and centers are arbitrary. -/
theorem kpBeta_commute {N : ℕ} (z : Fin N → ℂ) (μ ν : YoungDiagram) (a b : ℂ) :
    Commute (kpBeta μ z a) (kpBeta ν z b) := by
  change _ = _
  apply sub_eq_zero.mp
  apply eq_zero_of_all_specht_actions_zero
  intro τ
  rw [map_sub, map_mul, map_mul]
  exact sub_eq_zero.mpr (specht_kpBeta_commute τ.val τ.property.symm z μ ν a b).eq

namespace Paper

/-- LaTeX `lem:KP-correspondence`, commutativity clause only. -/
theorem lem_KP_correspondence_commutativity {N : ℕ} (z : Fin N → ℂ)
    (μ ν : YoungDiagram) (a b : ℂ) : kpBeta μ z a * kpBeta ν z b = kpBeta ν z b * kpBeta μ z a :=
  (kpBeta_commute z μ ν a b).eq

end Paper
end
end ModifiedCartan


