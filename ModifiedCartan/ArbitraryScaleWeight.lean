import ModifiedCartan.UniformPowerBounds
import ModifiedCartan.PeakRescaling

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal M_epsilon(R) of Section `sec:arbitrary-limits`. -/
noncomputable def arbitraryScaleWeight (ρ ε R : ℝ) : ℝ :=
  max (R ^ (ρ - ε)) (R ^ (ρ + ε))

theorem arbitraryScaleWeight_pos (ρ ε : ℝ) {R : ℝ} (hR : 0 < R) :
    0 < arbitraryScaleWeight ρ ε R :=
  (Real.rpow_pos_of_pos hR _).trans_le (le_max_left _ _)

theorem arbitraryScaleWeight_one (ρ ε : ℝ) : arbitraryScaleWeight ρ ε 1 = 1 := by
  simp [arbitraryScaleWeight]

theorem arbitraryScaleWeight_mul_le (ρ : ℝ) {ε A R : ℝ} (hε : 0 ≤ ε)
    (hA : 1 ≤ A) (hR : 0 < R) :
    arbitraryScaleWeight ρ ε (A * R) ≤ A ^ (ρ + ε) * arbitraryScaleWeight ρ ε R := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hpow : A ^ (ρ - ε) ≤ A ^ (ρ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  unfold arbitraryScaleWeight
  rw [Real.mul_rpow hAp.le hR.le, Real.mul_rpow hAp.le hR.le]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hR.le _)).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg hAp.le _))
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg hAp.le _)

/-- General scalar rescaling with the actual positive normalization M(R). -/
theorem arbitrary_rescaling_relation (Q : ℂ → ℂ) {R M r S : ℝ}
    (hR : 0 < R) (hM : 0 < M) (q : ℕ) (z : ℂ) :
    ((r / S : ℝ) : ℂ) ^ q * Q ((r : ℂ) * ((R : ℂ) * z)) =
      ((M / R : ℝ) : ℂ) ^ q *
        ((((R * r / (M * S)) : ℝ) : ℂ) ^ q * Q (((R * r : ℝ) : ℂ) * z)) := by
  have hscalar : (M / R) * (R * r / (M * S)) = r / S := by field_simp
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hscalar
  rw [Complex.ofReal_mul] at hc
  have hz : (r : ℂ) * ((R : ℂ) * z) = ((R * r : ℝ) : ℂ) * z := by push_cast; ring
  rw [hz, ← mul_assoc, ← mul_pow]
  congr 1
  exact congrArg (fun x : ℂ => x ^ q) hc.symm

end ModifiedCartan
#print axioms ModifiedCartan.arbitraryScaleWeight_mul_le
#print axioms ModifiedCartan.arbitrary_rescaling_relation
