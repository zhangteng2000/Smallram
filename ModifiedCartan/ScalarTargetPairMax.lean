import ModifiedCartan.ScalarTargetLogData
import ModifiedCartan.ScalarDistinctTargetBounds
import ModifiedCartan.LocalL1Max
import ModifiedCartan.LocalSubsequence

open scoped Topology ENNReal Matrix
open Filter Set Metric MeasureTheory Matrix
set_option autoImplicit false
namespace ModifiedCartan

theorem normalized_log_le_pair_max {N x y C s : ℝ}
    (hN : 0 < N) (hx : 0 < x) (hy : 0 < y) (hC : 0 < C) (hs : 0 < s)
    (hbound : N ≤ C * max x y) :
    s⁻¹ * Real.log N ≤ s⁻¹ * Real.log C + max (s⁻¹ * Real.log x) (s⁻¹ * Real.log y) := by
  have he : Real.log (max x y) = max (Real.log x) (Real.log y) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log hx h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log hy h)]
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hN hbound) (inv_pos.mpr hs).le
  rw [Real.log_mul hC.ne' (ne_of_gt (hx.trans_le (le_max_left _ _))), he,
    mul_add, mul_max_of_nonneg _ _ (inv_pos.mpr hs).le] at hh
  exact hh

/-- Any two distinct fixed-target logarithmic limits recover the actual
norm profile as their maximum. The lower comparison constant disappears
after division by the characteristic. Auxiliary to LaTeX `thm:A` (b). -/
theorem ScalarTargetLogLimitData.norm_eq_max
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {α β : WithTop ℂ} (eα : ScalarTargetLogLimitData d α) (eβ : ScalarTargetLogLimitData d β)
    (hab : α ≠ β) :
    EqOn (fun z => (d.U z).toReal)
      (fun z => max (eα.u z).toReal (eβ.u z).toReal) (ball (0 : ℂ) 4) := by
  obtain ⟨C, hC, hbound⟩ := scalar_distinct_target_norm_bound hab
  have hN := d.polynomial_norm_limit.congr_ae (fun _ => EventuallyEq.rfl)
    (show d.V =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (d.U z).toReal) by
      filter_upwards [d.representative] with z hz
      rw [hz, EReal.toReal_coe])
  have hM := eα.real_convergence.max eβ.real_convergence
  obtain ⟨ns, hns, hnlim⟩ := hN.exists_seq_tendsto_ae (by norm_num) isOpen_ball
  obtain ⟨ms, hms, hmlim⟩ := (hM.comp_strictMono hns).exists_seq_tendsto_ae (by norm_num) isOpen_ball
  have hzero : Tendsto
      (fun ν => (characteristic f (r (d.subseq (ns (ms ν)))))⁻¹ * Real.log C)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((tendsto_inv_atTop_zero.comp d.scale_tendsto).comp
        (hns.tendsto_atTop.comp hms.tendsto_atTop)).mul_const (Real.log C)
  have hnα := ae_all_iff.mpr (fun ν =>
    eα.convergence.normalizedLog_ae_ne_zero (d.scale_pos ν))
  have hnβ := ae_all_iff.mpr (fun ν =>
    eβ.convergence.normalizedLog_ae_ne_zero (d.scale_pos ν))
  have hle : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4),
      (d.U z).toReal ≤ max (eα.u z).toReal (eβ.u z).toReal := by
    filter_upwards [hnlim, hmlim, hnα, hnβ] with z hnz hmz hαz hβz
    have hright := hzero.add hmz
    simp only [zero_add] at hright
    apply le_of_tendsto_of_tendsto (hnz.comp hms.tendsto_atTop) hright
    apply Eventually.of_forall
    intro ν
    let k := ns (ms ν)
    let v : Index 1 → ℂ := fun j => (d.polynomial k j).eval z
    have hα : (v ᵥ* (scalarTargetUnitary α : Matrix (Index 1) (Index 1) ℂ)) 0 ≠ 0 := by
      rw [← polynomialMatrixGauge_eval_vecMul]
      exact hαz k
    have hβ : (v ᵥ* (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)) 0 ≠ 0 := by
      rw [← polynomialMatrixGauge_eval_vecMul]
      exact hβz k
    have hv : v ≠ 0 := by
      intro hz
      apply hα
      rw [hz, Matrix.zero_vecMul]
      rfl
    have hh := normalized_log_le_pair_max (euclideanNorm_pos hv)
      (norm_pos_iff.mpr hα) (norm_pos_iff.mpr hβ) hC (d.scale_pos k) (hbound v)
    simpa only [v, k, Function.comp_def, ← polynomialMatrixGauge_eval_vecMul] using hh
  have heq : (fun z => (d.U z).toReal) =ᵐ[volume.restrict (ball (0 : ℂ) 4)]
      (fun z => max (eα.u z).toReal (eβ.u z).toReal) := by
    filter_upwards [hle, ae_restrict_mem measurableSet_ball] with z hz hzball
    exact le_antisymm hz (max_le (eα.bounds z hzball).2 (eβ.bounds z hzball).2)
  exact Measure.eqOn_open_of_ae_eq heq isOpen_ball d.norm_limit_continuous.2
    (eα.regular.2.continuousOn.sup eβ.regular.2.continuousOn)

/-- Once one target has exponent -U at a positive point, every distinct
target whose actual logarithmic limit exists has exponent +U there. -/
theorem ScalarTargetLogLimitData.eq_norm_of_other_neg
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {α β : WithTop ℂ} (eα : ScalarTargetLogLimitData d α) (eβ : ScalarTargetLogLimitData d β)
    (hab : α ≠ β) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) (hpos : 0 < (d.U z).toReal)
    (hneg : (eα.u z).toReal = -(d.U z).toReal) : (eβ.u z).toReal = (d.U z).toReal := by
  have he := eα.norm_eq_max eβ hab hz
  change (d.U z).toReal = max (eα.u z).toReal (eβ.u z).toReal at he
  rw [hneg] at he
  rcases le_total (-(d.U z).toReal) (eβ.u z).toReal with h | h
  · rw [max_eq_right h] at he
    exact he.symm
  · rw [max_eq_left h] at he
    linarith

end ModifiedCartan
#print axioms ModifiedCartan.ScalarTargetLogLimitData.norm_eq_max
#print axioms ModifiedCartan.ScalarTargetLogLimitData.eq_norm_of_other_neg
