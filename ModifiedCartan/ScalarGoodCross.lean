import ModifiedCartan.ScalarDominantComponent
import ModifiedCartan.ScalarNormSmooth
import ModifiedCartan.PolynomialVerticalLine
import ModifiedCartan.PolynomialGaugeLower

open scoped Topology ENNReal ContDiff
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem scaled_log_lower_of_error {s δ u L : ℝ} (hs : 0 < s)
    (hu : 2 * δ ≤ u) (he : |s⁻¹ * L - u| < δ) : δ * s ≤ L := by
  have hh : δ ≤ s⁻¹ * L := by have h := (abs_lt.mp he).1; linarith
  calc
    δ * s ≤ (s⁻¹ * L) * s := mul_le_mul_of_nonneg_right hh hs.le
    _ = L := by field_simp

/-- Intersecting good lines for an actual unitary component. All gradients
and all physical speed estimates are derived in the proof. -/
theorem ArbitraryRadiusLimitData.scalar_component_good_cross
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop)
    {ns : ℕ → ℕ} (hns : StrictMono ns)
    (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) (j : Index 1)
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hΩ : Ω ⊆ ball (0 : ℂ) 2) (hpos : ∀ z ∈ Ω, 0 < (d.U z).toReal)
    (hP : ∀ ν, polynomialMatrixGauge (d.polynomial (ns ν))
      (V ν : Matrix (Index 1) (Index 1) ℂ) j ≠ 0)
    (hlog : LocalLpConvergence 1 Ω
      (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
        Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖)
      (fun z => (d.U z).toReal))
    {a b c e δ : ℝ} (hab : a < b) (hce : c < e)
    (hK : complexClosedRectangle a b c e ⊆ Ω) (hδ : 0 < δ)
    (hUδ : ∀ z ∈ complexClosedRectangle a b c e, 2 * δ ≤ (d.U z).toReal) :
    ∀ᶠ ν in atTop, ∃ x ∈ Icc a b, ∃ y ∈ Icc c e,
      (∀ t ∈ Icc a b,
        r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord
          ((r (d.subseq (ns ν)) : ℂ) * (⟨t, y⟩ : ℂ)) ≤
            Real.exp (-(δ / 2) * characteristic f (r (d.subseq (ns ν))))) ∧
      (∀ t ∈ Icc c e,
        r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord
          ((r (d.subseq (ns ν)) : ℂ) * (⟨x, t⟩ : ℂ)) ≤
            Real.exp (-(δ / 2) * characteristic f (r (d.subseq (ns ν))))) := by
  have hs := d.scale_tendsto.comp hns.tendsto_atTop
  have hg := d.scalar_norm_hasWeakComplexGradient_of_pos hρ hΩopen hΩ hpos
  have hdiff (z : ℂ) (hz : z ∈ Ω) : DifferentiableAt ℝ (fun w => (d.U w).toReal) z :=
    (d.scalar_norm_contDiffAt_of_pos hρ (hΩ hz) (hpos z hz)).differentiableAt (by simp)
  have hH := hlog.polynomial_good_horizontal_lines hΩopen hΩconn hP hs hg hab hce hK
    (fun y hy x hx => hasDerivAt_horizontal_of_differentiableAt (hdiff _ (hK ⟨hx, hy⟩))) hδ
  have hV := hlog.polynomial_good_vertical_lines hΩopen hΩconn hP hs hg hce hab hK
    (fun x hx y hy => hasDerivAt_vertical_of_differentiableAt (hdiff _ (hK ⟨hx, hy⟩))) hδ
  have hspeed := hns.tendsto_atTop.eventually
    (d.scalar_speed_decay_of_polynomial_component hlin htrans hsmall
      (lt_of_lt_of_le zero_lt_one hρ) hl hu hr hδ)
  filter_upwards [hH, hV, hspeed] with ν hHν hVν hspeedν
  obtain ⟨y, hy, _, hyl⟩ := hHν
  obtain ⟨x, hx, _, hxl⟩ := hVν
  have hpoint (z : ℂ) (hz : z ∈ complexClosedRectangle a b c e)
      (he : |polynomialLogError (polynomialMatrixGauge (d.polynomial (ns ν))
        (V ν : Matrix (Index 1) (Index 1) ℂ) j)
        (characteristic f (r (d.subseq (ns ν)))) (fun w => (d.U w).toReal) z| < δ) :
      r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord ((r (d.subseq (ns ν)) : ℂ) * z) ≤
        Real.exp (-(δ / 2) * characteristic f (r (d.subseq (ns ν)))) := by
    apply hspeedν (V ν) j z ((ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)) (hΩ (hK hz)))
    exact scaled_log_lower_of_error (d.scale_pos (ns ν)) (hUδ z hz) he
  exact ⟨x, hx, y, hy, fun t ht => hpoint _ ⟨ht, hy⟩ (hyl t ht),
    fun t ht => hpoint _ ⟨hx, ht⟩ (hxl t ht)⟩

/-- Actual good crosses follow from the original curve hypotheses at a positive
good center; the component, subsequence and neighborhood are all constructed.
Auxiliary to LaTeX `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_good_cross_near_good_center
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop)
    {z₀ : ℂ} (hz₀ : z₀ ∈ d.good_centers.centers) (hpos : 0 < (d.U z₀).toReal) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧ ∃ R : ℝ, 0 < R ∧
      ball z₀ R ⊆ ball (0 : ℂ) 2 ∧
      (∀ z ∈ ball z₀ R, 0 < (d.U z).toReal) ∧
      ∀ a b c e δ : ℝ, a < b → c < e → complexClosedRectangle a b c e ⊆ ball z₀ R →
        0 < δ → (∀ z ∈ complexClosedRectangle a b c e, 2 * δ ≤ (d.U z).toReal) →
        ∀ᶠ ν in atTop, ∃ x ∈ Icc a b, ∃ y ∈ Icc c e,
          (∀ t ∈ Icc a b, r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord
            ((r (d.subseq (ns ν)) : ℂ) * (⟨t, y⟩ : ℂ)) ≤
              Real.exp (-(δ / 2) * characteristic f (r (d.subseq (ns ν))))) ∧
          (∀ t ∈ Icc c e, r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord
            ((r (d.subseq (ns ν)) : ℂ) * (⟨x, t⟩ : ℂ)) ≤
              Real.exp (-(δ / 2) * characteristic f (r (d.subseq (ns ν))))) := by
  obtain ⟨ns, hns, V, j, R, hR, hR2, hp, hP, hlog⟩ :=
    d.scalar_exists_dominant_component_near_good_center hz₀ hpos
  refine ⟨ns, hns, R, hR, hR2, hp, ?_⟩
  intro a b c e δ hab hce hK hδ hUδ
  exact d.scalar_component_good_cross hlin htrans hsmall hρ hl hu hr hns V j
    isOpen_ball (convex_ball z₀ R).isPreconnected hR2 hp hP hlog hab hce hK hδ hUδ

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_component_good_cross
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_good_cross_near_good_center
