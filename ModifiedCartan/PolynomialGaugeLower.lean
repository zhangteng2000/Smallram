import ModifiedCartan.ScalarSphericalDecay
import ModifiedCartan.ReplacementNormProperties
import ModifiedCartan.ScaledPolynomialJets
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem unitary_polynomial_component_norm_le {n : ℕ} (p : Index n → Polynomial ℂ)
    (V : Matrix.unitaryGroup (Index n) ℂ) (j : Index n) (z : ℂ) :
    ‖(polynomialMatrixGauge p (V : Matrix (Index n) (Index n) ℂ) j).eval z‖ ≤
      euclideanNorm (fun k => (p k).eval z) := by
  have hh := (norm_le_pi_norm
    (fun k => (polynomialMatrixGauge p (V : Matrix (Index n) (Index n) ℂ) k).eval z) j).trans
    (norm_le_euclideanNorm _)
  rw [polynomialMatrixGauge_unitary_norm] at hh
  exact hh

/-- The actual Taylor-vector norm error is uniformly at most one eventually. -/
theorem PolynomialReplacementData.norm_error_le_one {n : ℕ} {f : Curve n}
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (hA : 0 < A) (hs : Tendsto s atTop atTop) :
    ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 4,
      |euclideanNorm (fun j => (p ν j).eval z) -
        euclideanNorm (fun j => rescaledRepresentation f (t ν) (H ν) j z)| ≤ 1 := by
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.Tendsto.const_mul_atTop hA hs)
  have hlim := ht.const_mul (Real.sqrt (n + 1 : ℝ))
  simp only [mul_zero] at hlim
  filter_upwards [h.norm_error, hlim.eventually_lt_const zero_lt_one] with ν hν hn
  intro z hz
  exact (hν z hz).trans (by simpa only [Function.comp_def, neg_mul] using hn.le)

/-- A lower bound for any unitary polynomial component gives a lower bound
for the actual gauge norm. The loss of a factor two absorbs the proved error. -/
theorem PolynomialReplacementData.gauge_norm_lower_of_unitary_component
    {n : ℕ} {f : Curve n} {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (hA : 0 < A) (hs : Tendsto s atTop atTop) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ν in atTop, ∀ V : Matrix.unitaryGroup (Index n) ℂ, ∀ j : Index n,
      ∀ z ∈ ball (0 : ℂ) 4,
      δ * s ν ≤ Real.log ‖(polynomialMatrixGauge (p ν)
        (V : Matrix (Index n) (Index n) ℂ) j).eval z‖ →
      (δ / 2) * s ν ≤ Real.log (euclideanNorm
        (fun k => rescaledRepresentation f (t ν) (H ν) k z)) := by
  have hlarge := Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop (half_pos hδ) hs)
  filter_upwards [h.norm_error_le_one hA hs, hs.eventually_gt_atTop 0,
    hlarge.eventually_ge_atTop 2] with ν herr hsν htwo
  intro V j z hz hlog
  let q : ℂ := (polynomialMatrixGauge (p ν) (V : Matrix (Index n) (Index n) ℂ) j).eval z
  change δ * s ν ≤ Real.log ‖q‖ at hlog
  have hq : q ≠ 0 := by
    intro he
    change δ * s ν ≤ Real.log ‖q‖ at hlog
    rw [he, norm_zero, Real.log_zero] at hlog
    exact (not_le_of_gt (mul_pos hδ hsν)) hlog
  have hlower : Real.exp (δ * s ν) ≤ euclideanNorm (fun k => (p ν k).eval z) := by
    calc
      _ ≤ ‖q‖ := by simpa only [Real.exp_log (norm_pos_iff.mpr hq)] using Real.exp_le_exp.mpr hlog
      _ ≤ _ := unitary_polynomial_component_norm_le (p ν) V j z
  have hpow : Real.exp (δ * s ν) = Real.exp ((δ / 2) * s ν) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hclose := (abs_le.mp (herr z hz)).2
  have he : Real.exp ((δ / 2) * s ν) ≤ euclideanNorm
      (fun k => rescaledRepresentation f (t ν) (H ν) k z) := by
    rw [hpow] at hlower
    change 2 ≤ Real.exp ((δ / 2) * s ν) at htwo
    nlinarith
  have hh := Real.log_le_log (Real.exp_pos _) he
  simpa only [Real.log_exp] using hh

/-- Actual physical speed decay on points selected by a polynomial component.
All estimates are derived from the curve hypotheses and the actual Taylor data. -/
theorem ArbitraryRadiusLimitData.scalar_speed_decay_of_polynomial_component
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ν in atTop, ∀ V : Matrix.unitaryGroup (Index 1) ℂ, ∀ j : Index 1,
      ∀ z ∈ ball (0 : ℂ) 4,
      δ * characteristic f (r (d.subseq ν)) ≤ Real.log ‖(polynomialMatrixGauge (d.polynomial ν)
        (V : Matrix (Index 1) (Index 1) ℂ) j).eval z‖ →
      r (d.subseq ν) * scalarSphericalSpeed f.coord ((r (d.subseq ν) : ℂ) * z) ≤
        Real.exp (-(δ / 2) * characteristic f (r (d.subseq ν))) := by
  filter_upwards [d.replacement.gauge_norm_lower_of_unitary_component d.A_pos d.scale_tendsto hδ,
    d.scalar_physical_speed_exp_bound hlin htrans hsmall hρ hl hu hr (half_pos hδ)] with ν hν hspeed
  intro V j z hz hlog
  have hh := hspeed z hz (δ / 2) (hν V j z hz hlog)
  convert hh using 1
  congr 1
  ring

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.gauge_norm_lower_of_unitary_component
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_speed_decay_of_polynomial_component

