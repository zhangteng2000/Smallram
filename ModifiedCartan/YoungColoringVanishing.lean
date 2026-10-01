import ModifiedCartan.YoungColoringMinimum
import ModifiedCartan.ColoringColumnCancellation
import ModifiedCartan.YoungSpechtGenerator

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem youngSpecht_weightColoring_intertwiner_zero {m : ℕ} (μ : YoungDiagram)
    (d : Fin m →₀ ℕ) (hd : finiteColorWeight d < partitionRowWeight μ)
    (F : Representation.IntertwiningMap (youngSpechtRepresentation μ)
      (weightColoringRepresentation (YoungBoxes μ) d)) : F = 0 := by
  apply youngSpechtIntertwiner_eq_zero_of_generator μ _ F
  ext f
  obtain ⟨a, b, hne, hcol, hc⟩ := weightColoring_column_collision μ d hd f
  exact columnSignVector_collision_coeff μ d (F (youngSpechtGenerator μ))
    (youngSpechtIntertwiner_generator_column μ _ F) f a b hne hcol hc

end
end ModifiedCartan


