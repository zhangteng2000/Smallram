import ModifiedCartan.NormComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology
set_option autoImplicit false
namespace ModifiedCartan

theorem peak_rescaling_scalar {R μ r S : ℝ} (hR : 0 < R) (q : ℕ) :
    R ^ ((q : ℝ) * (μ - 1)) * (R * r / (R ^ μ * S)) ^ q = (r / S) ^ q := by
  have hweight : R ^ ((q : ℝ) * (μ - 1)) = (R ^ μ / R) ^ q := by
    rw [mul_comm, Real.rpow_mul_natCast hR.le, Real.rpow_sub_one hR.ne']
  rw [hweight, ← mul_pow]
  congr 1
  by_cases hS : S = 0
  · simp only [hS, mul_zero, div_zero, mul_zero]
  · have hRp := (Real.rpow_pos_of_pos hR μ).ne'
    field_simp

/-- LaTeX `eq:peak-rescaling-relation`. This algebraic equality holds even
when r or S vanishes; only the fixed dilation R must be positive. -/
theorem peak_rescaling_relation (Q : ℂ → ℂ) {R μ r S : ℝ} (hR : 0 < R)
    (q : ℕ) (z : ℂ) :
    ((r / S : ℝ) : ℂ) ^ q * Q ((r : ℂ) * ((R : ℂ) * z)) =
      ((R ^ ((q : ℝ) * (μ - 1)) : ℝ) : ℂ) *
        ((((R * r / (R ^ μ * S)) : ℝ) : ℂ) ^ q * Q (((R * r : ℝ) : ℂ) * z)) := by
  have hscalar := congrArg (fun x : ℝ => (x : ℂ)) (peak_rescaling_scalar (r := r) (S := S) (μ := μ) hR q)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hscalar
  have hz : (r : ℂ) * ((R : ℂ) * z) = ((R * r : ℝ) : ℂ) * z := by
    push_cast
    ring
  rw [hz, ← hscalar, mul_assoc]

end ModifiedCartan
#print axioms ModifiedCartan.peak_rescaling_relation
