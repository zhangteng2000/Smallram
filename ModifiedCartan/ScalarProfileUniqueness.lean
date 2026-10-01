import ModifiedCartan.ScalarQuadraticProfile
import ModifiedCartan.LocalMeasureUniqueness

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- On a fixed coefficient circle the continuous profile determines its
coefficient uniquely, already on the open unit disk. -/
theorem scalarQuadraticProfile_injective_of_norm_eq {m : ℕ} (hm : m ≠ 0)
    {C D : ℂ} (hnorm : ‖C‖ = ‖D‖)
    (h : EqOn (scalarQuadraticProfile m C) (scalarQuadraticProfile m D) (ball (0 : ℂ) 1)) :
    C = D := by
  have hre (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : (C * z ^ m).re = (D * z ^ m).re := by
    have hh := congrArg (fun x : ℝ => x ^ 2) (h hz)
    rw [scalarQuadraticProfile_sq, scalarQuadraticProfile_sq] at hh
    simp only [norm_mul, hnorm] at hh
    linarith
  let q : ℝ := (1 / 2 : ℝ) ^ m
  have hq : q ≠ 0 := pow_ne_zero m (by norm_num)
  have hz0 : (((1 / 2 : ℝ) : ℂ)) ∈ ball (0 : ℂ) 1 := by norm_num
  have hreal := hre (((1 / 2 : ℝ) : ℂ)) hz0
  rw [← Complex.ofReal_pow] at hreal
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
  have heRe : C.re = D.re := mul_right_cancel₀ hq hreal
  let w : ℂ := Complex.I ^ ((m : ℂ)⁻¹)
  have hwpow : w ^ m = Complex.I := Complex.cpow_nat_inv_pow Complex.I hm
  have hw : ‖w‖ = 1 := (pow_left_inj₀ (norm_nonneg w) zero_le_one hm).mp (by
    rw [← norm_pow, hwpow, Complex.norm_I, one_pow])
  have hzI : (((1 / 2 : ℝ) : ℂ)) * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, norm_mul, hw]
    norm_num
  have him := hre ((((1 / 2 : ℝ) : ℂ)) * w) hzI
  rw [mul_pow, hwpow, ← Complex.ofReal_pow] at him
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, zero_sub, add_zero] at him
  have heIm : C.im = D.im := mul_right_cancel₀ hq (by linarith : C.im * q = D.im * q)
  exact Complex.ext heRe heIm

theorem scalarQuadraticProfile_injective_of_ae_eq {m : ℕ} (hm : m ≠ 0)
    {C D : ℂ} (hnorm : ‖C‖ = ‖D‖)
    (h : scalarQuadraticProfile m C =ᵐ[volume.restrict (ball (0 : ℂ) 1)] scalarQuadraticProfile m D) :
    C = D := by
  apply scalarQuadraticProfile_injective_of_norm_eq hm hnorm
  apply Measure.eqOn_open_of_ae_eq h isOpen_ball
  · exact ((continuous_scalarQuadraticProfile m).comp (continuous_const.prodMk continuous_id)).continuousOn
  · exact ((continuous_scalarQuadraticProfile m).comp (continuous_const.prodMk continuous_id)).continuousOn

end ModifiedCartan
#print axioms ModifiedCartan.scalarQuadraticProfile_injective_of_norm_eq
#print axioms ModifiedCartan.scalarQuadraticProfile_injective_of_ae_eq
