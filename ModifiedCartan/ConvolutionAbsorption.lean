import ModifiedCartan.Convolution
import ModifiedCartan.Envelope
import ModifiedCartan.CountingPowerEnvelope

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The constant term of the convolution in LaTeX `eq:absorption`. -/
theorem constant_counting_kernel {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => 1 / (r + t) ^ 2) (Ioi 0) ∧
      r * (∫ t in Ioi 0, 1 / (r + t) ^ 2) = 1 := by
  refine ⟨?_, ?_⟩
  · simpa only [Real.rpow_zero, max_self] using
      power_counting_kernel_integrable (σ := 0) le_rfl (by norm_num) hr
  · have hh := envelope_integral_rescale (fun _ => 1) hr
    have hv : (∫ u in Ioi 0, 1 / (1 + u) ^ 2) = (1 : ℝ) := by
      simpa only [envelopeConstant, envelopeIntegrand, Real.rpow_zero, max_self] using
        envelopeConstant_zero
    exact hh.trans hv

theorem convolution_le_of_counting_bound {N H : ℝ → ℝ} {r c C : ℝ}
    (hr : 0 < r)
    (hN : IntegrableOn (fun t => N t / (r + t) ^ 2) (Ioi 0))
    (hH : IntegrableOn (fun t => H (3 * t) / (r + t) ^ 2) (Ioi 0))
    (hb : ∀ t, 0 < t → N t ≤ c * H (3 * t) + C) :
    r * (∫ t in Ioi 0, N t / (r + t) ^ 2) ≤
      c * (r * ∫ t in Ioi 0, H (3 * t) / (r + t) ^ 2) + C := by
  have hk := constant_counting_kernel hr
  have hmajor : IntegrableOn
      (fun t => c * (H (3 * t) / (r + t) ^ 2) + C * (1 / (r + t) ^ 2)) (Ioi 0) :=
    (hH.const_mul c).add (hk.1.const_mul C)
  have hi := integral_mono_ae hN hmajor (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hh := div_le_div_of_nonneg_right (hb t ht) (sq_nonneg (r + t))
    convert! hh using 1 <;> ring)
  rw [integral_add (hH.const_mul c) (hk.1.const_mul C),
    integral_const_mul, integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi hr.le
  calc
    _ ≤ _ := hh
    _ = c * (r * ∫ t in Ioi 0, H (3 * t) / (r + t) ^ 2) +
        C * (r * ∫ t in Ioi 0, 1 / (r + t) ^ 2) := by ring
    _ = _ := by rw [hk.2, mul_one]

/-- LaTeX `eq:absorption`, before choosing the size of the coefficient.
Its counting and envelope hypotheses are discharged by the subsequent
small-order and order-zero arguments. -/
theorem system_absorption_at_radius {n : ℕ} {y : Index n → ℂ → ℂ}
    (hy : ∀ j, Differentiable ℂ (y j)) (ho : ∀ j, entireOrder (y j) < 1)
    (hjets : ∀ i j : Index n, iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0)
    {r c C I : ℝ} (hr : 1 ≤ r) (hc : 0 ≤ c)
    (hN : ∀ t, 0 < t → systemCounting y t ≤ c * systemLogMaximum y (3 * t) + C)
    (hH : IntegrableOn (fun t => systemLogMaximum y (3 * t) / (r + t) ^ 2) (Ioi 0))
    (hI : r * (∫ t in Ioi 0, systemLogMaximum y (3 * t) / (r + t) ^ 2) ≤
      I * systemLogMaximum y r) :
    (1 - c * I) * systemLogMaximum y r ≤ (n : ℝ) * Real.log r + C := by
  have hr0 := zero_lt_one.trans_le hr
  obtain ⟨hi, hb⟩ := Paper.cor_convolution hy ho hjets hr0
  have hn := convolution_le_of_counting_bound hr0 hi hH hN
  have he := mul_le_mul_of_nonneg_left hI hc
  rw [Real.posLog_eq_log (by rw [abs_of_pos hr0]; exact hr)] at hb
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.constant_counting_kernel
#print axioms ModifiedCartan.system_absorption_at_radius
