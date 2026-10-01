import ModifiedCartan.ScalarTargetLinearBounds
import ModifiedCartan.UnitaryNorm
import ModifiedCartan.ScaledPolynomialJets

open scoped Topology ComplexConjugate BigOperators Matrix
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def scalarFiniteTargetMatrix (b : ℂ) : Matrix (Index 1) (Index 1) ℂ :=
  !![-b / (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ), 1 / (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ);
      1 / (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ), conj b / (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ)]

theorem scalarFiniteTargetMatrix_unitary (b : ℂ) :
    scalarFiniteTargetMatrix b ∈ Matrix.unitaryGroup (Index 1) ℂ := by
  have hd : 0 < Real.sqrt (1 + ‖b‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hd0 : (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hsq : (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ) ^ 2 = 1 + b * conj b := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1 + ‖b‖ ^ 2 by positivity)
  apply Matrix.mem_unitaryGroup_iff'.2
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  change (∑ k : Fin 2, conj (scalarFiniteTargetMatrix b k i) * scalarFiniteTargetMatrix b k j) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [scalarFiniteTargetMatrix, map_div₀, Complex.conj_ofReal, Complex.conj_conj] <;>
    field_simp [hd0]
  all_goals first | (solve | ring) | (simpa only [mul_comm, add_comm] using hsq.symm)

def scalarTargetUnitary (β : WithTop ℂ) : Matrix.unitaryGroup (Index 1) ℂ :=
  β.recTopCoe 1 (fun b => ⟨scalarFiniteTargetMatrix b, scalarFiniteTargetMatrix_unitary b⟩)

def scalarTargetNormalizingSize (β : WithTop ℂ) : ℝ :=
  β.recTopCoe 1 (fun b => Real.sqrt (1 + ‖b‖ ^ 2))

theorem scalarTargetNormalizingSize_pos (β : WithTop ℂ) : 0 < scalarTargetNormalizingSize β := by
  induction β using WithTop.recTopCoe with
  | top => exact zero_lt_one
  | coe b => exact Real.sqrt_pos.2 (by positivity)

theorem one_le_scalarTargetNormalizingSize (β : WithTop ℂ) : 1 ≤ scalarTargetNormalizingSize β := by
  induction β using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe b =>
    change 1 ≤ Real.sqrt (1 + ‖b‖ ^ 2)
    have hs := Real.sq_sqrt (show 0 ≤ 1 + ‖b‖ ^ 2 by positivity)
    have hp := Real.sqrt_nonneg (1 + ‖b‖ ^ 2)
    nlinarith [sq_nonneg ‖b‖]

/-- The first column is the normalized actual target form, also at infinity. -/
theorem scalarTargetUnitary_first (β : WithTop ℂ) (v : Index 1 → ℂ) :
    (v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0 =
      scalarTargetLinearForm β (v 0) (v 1) / (scalarTargetNormalizingSize β : ℂ) := by
  induction β using WithTop.recTopCoe with
  | top =>
    change (v ᵥ* (1 : Matrix (Index 1) (Index 1) ℂ)) 0 = v 0 / 1
    rw [Matrix.vecMul_one, div_one]
  | coe b =>
    change (v ᵥ* scalarFiniteTargetMatrix b) 0 =
      (v 1 - b * v 0) / (Real.sqrt (1 + ‖b‖ ^ 2) : ℂ)
    change (∑ k : Fin 2, v k * scalarFiniteTargetMatrix b k 0) = _
    rw [Fin.sum_univ_two]
    dsimp [scalarFiniteTargetMatrix]
    ring

theorem scalarTargetUnitary_polynomial_first (β : WithTop ℂ) (p : Index 1 → Polynomial ℂ) (z : ℂ) :
    (polynomialMatrixGauge p (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval z =
      scalarTargetLinearForm β ((p 0).eval z) ((p 1).eval z) / (scalarTargetNormalizingSize β : ℂ) := by
  have hh := congrFun (polynomialMatrixGauge_eval_vecMul p
    (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) z) 0
  exact hh.trans (scalarTargetUnitary_first β (fun j => (p j).eval z))

theorem scalarTargetUnitary_first_norm_le (β : WithTop ℂ) (v : Index 1 → ℂ) :
    ‖(v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0‖ ≤
      ‖scalarTargetLinearForm β (v 0) (v 1)‖ := by
  rw [scalarTargetUnitary_first, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (scalarTargetNormalizingSize_pos β).le]
  exact div_le_self (norm_nonneg _) (one_le_scalarTargetNormalizingSize β)

theorem scalarTargetLinearForm_difference_le (β : WithTop ℂ) {v w : Index 1 → ℂ} {E : ℝ}
    (hE : 0 ≤ E) (h : ∀ j, ‖v j - w j‖ ≤ E) :
    ‖scalarTargetLinearForm β (v 0) (v 1) - scalarTargetLinearForm β (w 0) (w 1)‖ ≤
      scalarTargetLinearSize β * E := by
  induction β using WithTop.recTopCoe with
  | top =>
    change ‖v 0 - w 0‖ ≤ 1 * E
    simpa only [one_mul] using h 0
  | coe b =>
    change ‖(v 1 - b * v 0) - (w 1 - b * w 0)‖ ≤ (1 + ‖b‖) * E
    rw [show (v 1 - b * v 0) - (w 1 - b * w 0) = (v 1 - w 1) - b * (v 0 - w 0) by ring]
    calc
      _ ≤ ‖v 1 - w 1‖ + ‖b‖ * ‖v 0 - w 0‖ := by
        simpa only [norm_mul] using norm_sub_le (v 1 - w 1) (b * (v 0 - w 0))
      _ ≤ E + ‖b‖ * E := add_le_add (h 1) (mul_le_mul_of_nonneg_left (h 0) (norm_nonneg b))
      _ = _ := by ring

theorem scalarTargetUnitary_first_difference_bound (β : WithTop ℂ) {v w : Index 1 → ℂ} {E : ℝ}
    (hE : 0 ≤ E) (h : ∀ j, ‖v j - w j‖ ≤ E) :
    ‖(v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0 -
      (w ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0‖ ≤
      scalarTargetLinearSize β * E := by
  rw [scalarTargetUnitary_first, scalarTargetUnitary_first, ← sub_div, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (scalarTargetNormalizingSize_pos β).le]
  exact (div_le_self (norm_nonneg _) (one_le_scalarTargetNormalizingSize β)).trans
    (scalarTargetLinearForm_difference_le β hE h)

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarFiniteTargetMatrix_unitary
#print axioms ModifiedCartan.scalarTargetUnitary_polynomial_first
