import ModifiedCartan.LocalCoefficientSplit
import ModifiedCartan.FiniteCauchyDerivatives
import ModifiedCartan.CanonicalCoefficients
import ModifiedCartan.SmallRootPoleSums
import ModifiedCartan.LogDerivativeLimit

open scoped Topology Classical BigOperators
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem polynomial_logDeriv_eq_root_sum {M : ℕ} (P : Polynomial ℂ)
    (a : Fin M → ℂ) (hP : P = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    {z : ℂ} (hz : ∀ i, z ≠ a i) :
    logDeriv (fun w => P.eval w) z = ∑ i, (z - a i)⁻¹ := by
  have he : (fun w => P.eval w) = fun w => ∏ i, (w - a i) := by
    funext w
    rw [hP, Polynomial.eval_prod]
    simp
  rw [he, logDeriv_prod (fun i _ => sub_ne_zero.mpr (hz i))
    (fun i _ => (show DifferentiableAt ℂ (fun w => w - a i) z by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  simp [logDeriv_apply]

theorem polynomial_logDeriv_jet_eq_root_sum_ae {M : ℕ} (P : Polynomial ℂ)
    (a : Fin M → ℂ) (hP : P = ∏ i, (Polynomial.X - Polynomial.C (a i))) (j : ℕ) :
    (fun z => iteratedDeriv j (logDeriv (fun w => P.eval w)) z) =ᵐ[volume]
      (fun z => (-1 : ℂ) ^ j * (j.factorial : ℂ) * ∑ i, (z - a i)⁻¹ ^ (j + 1)) := by
  filter_upwards [linear_root_product_ne_zero_ae a] with z hz
  have hza (i : Fin M) : z ≠ a i := by
    intro h
    apply hz
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact sub_eq_zero.mpr h
  have hn : ∀ᶠ w in 𝓝 z, ∀ i, w ≠ a i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_id.continuousAt : ContinuousAt (fun w : ℂ => w) z).eventually_ne (hza i)
  have hlog : logDeriv (fun w => P.eval w) =ᶠ[𝓝 z] (fun w => ∑ i, (w - a i)⁻¹) := by
    filter_upwards [hn] with w hw
    exact polynomial_logDeriv_eq_root_sum P a hP hw
  rw [(hlog.iteratedDeriv j).eq_of_nhds]
  have hd := iteratedDeriv_finite_cauchy_sum Finset.univ a (fun _ => 1) j
    (fun i _ => hza i)
  simpa only [one_mul, one_div, inv_pow] using hd

theorem canonicalLogDerivative_eq_polynomial {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Index n → ℂ → ℂ} (P : Polynomial ℂ)
    (hW : ∀ z ∈ U, FewInflection.wronskian n g z = P.eval z) {z : ℂ} (hz : z ∈ U) :
    canonicalLogDerivative n g z = -logDeriv (fun w => P.eval w) z / (n + 1 : ℂ) := by
  have he : (fun w => FewInflection.wronskian n g w) =ᶠ[𝓝 z] (fun w => P.eval w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hW w hw
  rw [canonicalLogDerivative, he.deriv_eq, hW z hz, logDeriv_apply]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem polynomial_logDeriv_jet_localMeasure_zero
    (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0)) (j : ℕ) :
    LocalMeasureConvergence (ball (0 : ℂ) 6)
      (fun ν z => iteratedDeriv j (logDeriv (fun w => (P ν).eval w)) z /
        (s ν : ℂ) ^ (j + 1)) (fun _ => 0) := by
  have hchoice (ν : ℕ) : ∃ a : Fin (P ν).natDegree → ℂ,
      P ν = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    obtain ⟨a, ha⟩ := exists_normalized_polynomial_root_list (P ν) (hP ν).ne_zero
    rw [(hP ν).normalize_eq_self] at ha
    exact ⟨a, ha⟩
  choose a ha using hchoice
  have hp := finite_pole_sum_normalized_localMeasure_zero a hs hm (by omega : 1 ≤ j + 1)
  have hc := hp.continuous_map
    (fun K _ _ ν => by dsimp [finitePoleSum]; fun_prop)
    (show Continuous (fun x : ℂ => (-1 : ℂ) ^ j * (j.factorial : ℂ) * x) by fun_prop)
  simp only [mul_zero] at hc
  apply hc.congr_ae
  apply Eventually.of_forall
  intro ν
  filter_upwards [polynomial_logDeriv_jet_eq_root_sum_ae (P ν) (a ν) (ha ν) j] with z hz
  rw [hz, finitePoleSum]
  ring

def polynomialGaugeLogDerivative (n : ℕ) (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  deriv (fun w => P.eval w) z / ((n + 1 : ℂ) * P.eval z)

theorem polynomialGaugeLogDerivative_eq (n : ℕ) (P : Polynomial ℂ) :
    polynomialGaugeLogDerivative n P =
      fun z => (n + 1 : ℂ)⁻¹ * logDeriv (fun w => P.eval w) z := by
  funext z
  simp only [polynomialGaugeLogDerivative, logDeriv_apply, div_eq_mul_inv, mul_inv_rev]
  ring

theorem polynomialGaugeLogDerivative_jet_normalized_eq (n : ℕ) (P : Polynomial ℂ)
    (j : ℕ) (s : ℝ) (z : ℂ) :
    iteratedDeriv j (polynomialGaugeLogDerivative n P) z / (s : ℂ) ^ (j + 1) =
      (n + 1 : ℂ)⁻¹ * (iteratedDeriv j (logDeriv (fun w => P.eval w)) z /
        (s : ℂ) ^ (j + 1)) := by
  rw [polynomialGaugeLogDerivative_eq, iteratedDeriv_const_mul_field]
  ring

namespace Paper

/-- LaTeX `eq:gaugesmall`. The exact polynomial ell is used; the
high-order convergence follows from the first-order root sum because
the actual total root count is o(s). -/
theorem eq_gaugesmall (n : ℕ) (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0)) (j : ℕ) :
    LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => iteratedDeriv j (polynomialGaugeLogDerivative n (P ν)) z /
        (s ν : ℂ) ^ (j + 1)) (fun _ => 0) := by
  have hj := polynomial_logDeriv_jet_localMeasure_zero P hP hs hm j
  have hc := hj.continuous_map
    (fun K hK _ ν => normalized_logDeriv_jet_aestronglyMeasurable
      (AnalyticOnNhd.eval_polynomial (P ν)) hK (subset_univ K) j (s ν))
    (show Continuous (fun x : ℂ => (n + 1 : ℂ)⁻¹ * x) by fun_prop)
  simp only [mul_zero] at hc
  have he := hc.mono (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 6))
  simpa only [polynomialGaugeLogDerivative_jet_normalized_eq] using he

end Paper

end
end ModifiedCartan
#print axioms ModifiedCartan.polynomial_logDeriv_jet_eq_root_sum_ae
#print axioms ModifiedCartan.canonicalLogDerivative_eq_polynomial
#print axioms ModifiedCartan.Paper.eq_gaugesmall
