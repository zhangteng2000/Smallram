import ModifiedCartan.PolynomialGaugeLower

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual Taylor norm error permits any strict exponential margin,
instead of a fixed factor loss in the exponent. -/
theorem PolynomialReplacementData.gauge_norm_lower_of_unitary_component_margin
    {n : ℕ} {f : Curve n} {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (hA : 0 < A) (hs : Tendsto s atTop atTop) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ ν in atTop, ∀ V : Matrix.unitaryGroup (Index n) ℂ, ∀ j : Index n,
      ∀ z ∈ ball (0 : ℂ) 4,
      β * s ν ≤ Real.log ‖(polynomialMatrixGauge (p ν)
        (V : Matrix (Index n) (Index n) ℂ) j).eval z‖ →
      α * s ν ≤ Real.log (euclideanNorm
        (fun k => rescaledRepresentation f (t ν) (H ν) k z)) := by
  have hgap : 0 < β - α := sub_pos.mpr hαβ
  have hlarge := Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop hgap hs)
  filter_upwards [h.norm_error_le_one hA hs, hs.eventually_gt_atTop 0,
    hlarge.eventually_ge_atTop 2] with ν herr hsν htwo
  intro V j z hz hlog
  let q : ℂ := (polynomialMatrixGauge (p ν) (V : Matrix (Index n) (Index n) ℂ) j).eval z
  change β * s ν ≤ Real.log ‖q‖ at hlog
  have hq : q ≠ 0 := by
    intro he
    rw [he, norm_zero, Real.log_zero] at hlog
    exact (not_le_of_gt (mul_pos (hα.trans hαβ) hsν)) hlog
  have hlower : Real.exp (β * s ν) ≤ euclideanNorm (fun k => (p ν k).eval z) := by
    calc
      _ ≤ ‖q‖ := by simpa only [Real.exp_log (norm_pos_iff.mpr hq)] using Real.exp_le_exp.mpr hlog
      _ ≤ _ := unitary_polynomial_component_norm_le (p ν) V j z
  have he : Real.exp (β * s ν) = Real.exp (α * s ν) * Real.exp ((β - α) * s ν) := by
    rw [← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (α * s ν) := Real.one_le_exp_iff.mpr (mul_nonneg hα.le hsν.le)
  change 2 ≤ Real.exp ((β - α) * s ν) at htwo
  have hprod := mul_le_mul_of_nonneg_left htwo (Real.exp_pos (α * s ν)).le
  have hclose := (abs_le.mp (herr z hz)).2
  have hlower' : Real.exp (α * s ν) ≤ euclideanNorm
      (fun k => rescaledRepresentation f (t ν) (H ν) k z) := by
    rw [he] at hlower
    nlinarith
  have hh := Real.log_le_log (Real.exp_pos _) hlower'
  simpa only [Real.log_exp] using hh

/-- Sharp physical speed exponent from an actual polynomial component lower
bound, with independently chosen positive margin. -/
theorem ArbitraryRadiusLimitData.scalar_speed_decay_of_polynomial_component_margin
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {α β ε : ℝ} (hα : 0 < α) (hαβ : α < β) (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ V : Matrix.unitaryGroup (Index 1) ℂ, ∀ j : Index 1,
      ∀ z ∈ ball (0 : ℂ) 4,
      β * characteristic f (r (d.subseq ν)) ≤ Real.log ‖(polynomialMatrixGauge (d.polynomial ν)
        (V : Matrix (Index 1) (Index 1) ℂ) j).eval z‖ →
      r (d.subseq ν) * scalarSphericalSpeed f.coord ((r (d.subseq ν) : ℂ) * z) ≤
        Real.exp ((ε - 2 * α) * characteristic f (r (d.subseq ν))) := by
  filter_upwards [d.replacement.gauge_norm_lower_of_unitary_component_margin d.A_pos d.scale_tendsto hα hαβ,
    d.scalar_physical_speed_exp_bound hlin htrans hsmall hρ hl hu hr hε] with ν hν hspeed
  intro V j z hz hlog
  exact hspeed z hz α (hν V j z hz hlog)

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.gauge_norm_lower_of_unitary_component_margin
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_speed_decay_of_polynomial_component_margin