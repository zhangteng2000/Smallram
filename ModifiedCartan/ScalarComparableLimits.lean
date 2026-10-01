import ModifiedCartan.VariableDilation
import ModifiedCartan.VariableScaling
import ModifiedCartan.Indices
import ModifiedCartan.Homogeneity
import ModifiedCartan.LocalMeasureUniqueness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual physical potentials at comparable radii have the same limit after
normalization. The proof uses variable dilation, proved regular variation and
homogeneity, without choosing a phase at individual radii. Auxiliary to thm:A (b). -/
theorem ArbitraryRadiusLimitData.scalar_comparable_potential_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) (hc₀ : c₀ ∈ Icc (1 : ℝ) 2)
    (hclim : Tendsto c atTop (𝓝 c₀)) :
    LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν => scalarNormalizedSpherePotential f (c ν * r (d.subseq ν)))
      (fun z => 2 * (d.U z).toReal) := by
  have hcp : 0 < c₀ := by linarith [hc₀.1]
  have ht : Tendsto (fun ν => r (d.subseq ν)) atTop atTop := by
    simpa only [Function.comp_def] using hr.comp d.strictMono.tendsto_atTop
  have hbase := (d.scalar_spherical_potential_localL1 hlin htrans hsmall hρ hl hu hr).inMeasure
    (by norm_num)
  have hv := hbase.variable_dilate
    (continuousOn_const.mul d.norm_limit_continuous.2) hc hc₀ hclim
  have hreg := Paper.prop_regular_variation f htrans hlin hsmall
    (positive_index_order_admissible f hlin htrans hsmall hρ hl.le hu.ge) hl hu
  have hratio := regularlyVarying_tendsto_variable_multiplier hreg isCompact_Icc
    (show Icc (1 : ℝ) 2 ⊆ Ioi 0 from fun x hx => by change 0 < x; linarith [hx.1]) hc hcp hclim ht
  have hratioinv : Tendsto
      (fun ν => characteristic f (r (d.subseq ν)) /
        characteristic f (c ν * r (d.subseq ν))) atTop (𝓝 ((c₀ ^ ρ)⁻¹)) := by
    simpa only [Function.comp_def, inv_div] using hratio.inv₀ (Real.rpow_pos_of_pos hcp ρ).ne'
  have hprod := hv.variable_const_mul
    (fun K _ _ ν => ((scalarNormalizedSpherePotential_measurable f (r (d.subseq ν))).comp
      (measurable_const.mul measurable_id)).aestronglyMeasurable) hratioinv
  have hphysical := hprod.congr_ae (by
    filter_upwards [ht.eventually_gt_atTop 0] with ν htν
    apply Eventually.of_forall
    intro z
    exact (scalarNormalizedSpherePotential_dilate f
      (characteristic_pos_of_transcendental f htrans htν).ne'
      (characteristic_pos_of_transcendental f htrans
        (mul_pos (by linarith [(hc ν).1]) htν)).ne' z).symm)
  apply hphysical.congr_limit_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hz2 : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
  have hcz2 : (c₀ : ℂ) * z ∈ ball (0 : ℂ) 2 := by
    have hn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcp.le]
    calc
      c₀ * ‖z‖ < c₀ * 1 := mul_lt_mul_of_pos_left hn hcp
      _ ≤ 2 := by simpa using hc₀.2
  have hhom := congrArg EReal.toReal (Paper.prop_homogeneity hρ d hcp hz2 hcz2)
  simp only [EReal.toReal_mul, EReal.toReal_coe] at hhom
  rw [hhom]
  field_simp

/-- Equality on the unit disk determines two actual homogeneous norm limits
throughout their common radius-two domain. -/
theorem ArbitraryRadiusLimitData.norm_limits_eqOn_of_unit_disk
    {f : Curve 1} {r s : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (e : ArbitraryRadiusLimitData f s ρ)
    (hρ : 0 < ρ)
    (heq : EqOn (fun z => (e.U z).toReal) (fun z => (d.U z).toReal) (ball (0 : ℂ) 1)) :
    EqOn (fun z => (e.U z).toReal) (fun z => (d.U z).toReal) (ball (0 : ℂ) 2) := by
  intro z hz
  have hh : ((1 / 2 : ℝ) : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    have hn : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
    rw [mem_ball, dist_zero_right, norm_mul]
    norm_num
    linarith
  have hh2 : ((1 / 2 : ℝ) : ℂ) * z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hh
  have hd := congrArg EReal.toReal (Paper.prop_homogeneity hρ d (by norm_num : (0 : ℝ) < 1/2) hz hh2)
  have he := congrArg EReal.toReal (Paper.prop_homogeneity hρ e (by norm_num : (0 : ℝ) < 1/2) hz hh2)
  simp only [EReal.toReal_mul, EReal.toReal_coe] at hd he
  have h := heq hh
  dsimp only at h ⊢
  rw [hd, he] at h
  exact (mul_left_cancel₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) ρ).ne') h

/-- Subsequential norm limits constructed at radii c_n r_n, with c_n in [1,2],
agree with the original actual limit. This is the phase-compatibility step,
expressed without an arbitrary choice of angular representatives. -/
theorem ArbitraryRadiusLimitData.scalar_comparable_norm_limits
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) (hc₀ : c₀ ∈ Icc (1 : ℝ) 2)
    (hclim : Tendsto c atTop (𝓝 c₀))
    (e : ArbitraryRadiusLimitData f (fun ν => c ν * r (d.subseq ν)) ρ) :
    EqOn (fun z => (e.U z).toReal) (fun z => (d.U z).toReal) (ball (0 : ℂ) 2) := by
  have ht : Tendsto (fun ν => r (d.subseq ν)) atTop atTop := by
    simpa only [Function.comp_def] using hr.comp d.strictMono.tendsto_atTop
  have hs : Tendsto (fun ν => c ν * r (d.subseq ν)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ ht
    filter_upwards [ht.eventually_ge_atTop 0] with ν htν
    nlinarith [(hc ν).1]
  have hd := (d.scalar_comparable_potential_limit hlin htrans hsmall hρ hl hu hr hc hc₀ hclim).comp
    e.strictMono.tendsto_atTop
  have he := ((e.scalar_spherical_potential_localL1 hlin htrans hsmall hρ hl hu hs).inMeasure
    (by norm_num)).mono (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 4))
  have hae := LocalMeasureConvergence.ae_unique isOpen_ball he hd
  have hunit := Measure.eqOn_open_of_ae_eq hae isOpen_ball
    (continuousOn_const.mul (e.norm_limit_continuous.2.mono (ball_subset_ball (by norm_num))))
    (continuousOn_const.mul (d.norm_limit_continuous.2.mono (ball_subset_ball (by norm_num))))
  apply d.norm_limits_eqOn_of_unit_disk e hρ
  intro z hz
  have hh := hunit hz
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_comparable_potential_limit
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.norm_limits_eqOn_of_unit_disk
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_comparable_norm_limits

