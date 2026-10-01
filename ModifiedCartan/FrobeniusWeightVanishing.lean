import ModifiedCartan.YoungFrobeniusCoefficients
import ModifiedCartan.YoungColoringVanishing

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The exact triangular support bound for the finite Specht character transform.
Auxiliary to the Schur identification in `lem:KP-correspondence`. -/
theorem finiteFrobeniusPolynomial_coeff_zero_of_weight_lt {m : ℕ}
    (μ : YoungDiagram) (d : Fin m →₀ ℕ) (hd : finiteColorWeight d < partitionRowWeight μ) :
    MvPolynomial.coeff d (finiteFrobeniusPolynomial (Fin m) μ) = 0 := by
  rw [finiteFrobeniusPolynomial_coeff_finrank_young,
    finrank_zero_iff_forall_zero.mpr (youngSpecht_weightColoring_intertwiner_zero μ d hd)]
  simp

end
end ModifiedCartan


