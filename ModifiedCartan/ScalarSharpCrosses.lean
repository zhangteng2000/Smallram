import ModifiedCartan.ScalarSharpSpeed
import ModifiedCartan.ScalarGoodCross

open scoped Topology ENNReal ContDiff
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem scaled_log_lower_of_error_margin {s β ε u L : ℝ} (hs : 0 < s)
    (hu : β + ε ≤ u) (he : |s⁻¹ * L - u| < ε) : β * s ≤ L := by
  have hh : β ≤ s⁻¹ * L := by have h := (abs_lt.mp he).1; linarith
  calc
    β * s ≤ (s⁻¹ * L) * s := mul_le_mul_of_nonneg_right hh hs.le
    _ = L := by field_simp

/-- Every rate strictly below twice the actual norm limit lower bound is
attained on constructed horizontal and vertical lines. This sharp coefficient
is required for exact proximity asymptotics in LaTeX thm:A (b). -/
theorem ArbitraryRadiusLimitData.scalar_component_good_cross_sharp
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
    {a b c e ℓ κ : ℝ} (hab : a < b) (hce : c < e)
    (hK : complexClosedRectangle a b c e ⊆ Ω) (hκ : 0 < κ) (hκℓ : κ < 2 * ℓ)
    (hUℓ : ∀ z ∈ complexClosedRectangle a b c e, ℓ ≤ (d.U z).toReal) :
    ∀ᶠ ν in atTop, ∃ x ∈ Icc a b, ∃ y ∈ Icc c e,
      (∀ t ∈ Icc a b,
        r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord
          ((r (d.subseq (ns ν)) : ℂ) * (⟨t, y⟩ : ℂ)) ≤
            Real.exp (-κ * characteristic f (r (d.subseq (ns ν))))) ∧
      (∀ t ∈ Icc c e,
        r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord
          ((r (d.subseq (ns ν)) : ℂ) * (⟨x, t⟩ : ℂ)) ≤
            Real.exp (-κ * characteristic f (r (d.subseq (ns ν))))) := by
  let α := (ℓ + κ / 2) / 2
  let β := (ℓ + α) / 2
  let ε := ℓ - β
  let η := 2 * α - κ
  have hα : 0 < α := by dsimp only [α]; linarith
  have hαβ : α < β := by dsimp only [β, α]; linarith
  have hε : 0 < ε := by dsimp only [ε, β, α]; linarith
  have hη : 0 < η := by dsimp only [η, α]; linarith
  have hs := d.scale_tendsto.comp hns.tendsto_atTop
  have hg := d.scalar_norm_hasWeakComplexGradient_of_pos hρ hΩopen hΩ hpos
  have hdiff (z : ℂ) (hz : z ∈ Ω) : DifferentiableAt ℝ (fun w => (d.U w).toReal) z :=
    (d.scalar_norm_contDiffAt_of_pos hρ (hΩ hz) (hpos z hz)).differentiableAt (by simp)
  have hH := hlog.polynomial_good_horizontal_lines hΩopen hΩconn hP hs hg hab hce hK
    (fun y hy x hx => hasDerivAt_horizontal_of_differentiableAt (hdiff _ (hK ⟨hx, hy⟩))) hε
  have hV := hlog.polynomial_good_vertical_lines hΩopen hΩconn hP hs hg hce hab hK
    (fun x hx y hy => hasDerivAt_vertical_of_differentiableAt (hdiff _ (hK ⟨hx, hy⟩))) hε
  have hspeed := hns.tendsto_atTop.eventually
    (d.scalar_speed_decay_of_polynomial_component_margin hlin htrans hsmall
      (lt_of_lt_of_le zero_lt_one hρ) hl hu hr hα hαβ hη)
  filter_upwards [hH, hV, hspeed] with ν hHν hVν hspeedν
  obtain ⟨y, hy, _, hyl⟩ := hHν
  obtain ⟨x, hx, _, hxl⟩ := hVν
  have hpoint (z : ℂ) (hz : z ∈ complexClosedRectangle a b c e)
      (he : |polynomialLogError (polynomialMatrixGauge (d.polynomial (ns ν))
        (V ν : Matrix (Index 1) (Index 1) ℂ) j)
        (characteristic f (r (d.subseq (ns ν)))) (fun w => (d.U w).toReal) z| < ε) :
      r (d.subseq (ns ν)) * scalarSphericalSpeed f.coord ((r (d.subseq (ns ν)) : ℂ) * z) ≤
        Real.exp (-κ * characteristic f (r (d.subseq (ns ν)))) := by
    have hb : β * characteristic f (r (d.subseq (ns ν))) ≤
        Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖ :=
      scaled_log_lower_of_error_margin (d.scale_pos (ns ν))
        (show β + ε ≤ (d.U z).toReal by dsimp only [ε]; linarith [hUℓ z hz]) he
    have hh := hspeedν (V ν) j z
      ((ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)) (hΩ (hK hz))) hb
    convert hh using 1
    congr 1
    dsimp only [η]
    ring
  exact ⟨x, hx, y, hy, fun t ht => hpoint _ ⟨ht, hy⟩ (hyl t ht),
    fun t ht => hpoint _ ⟨hx, ht⟩ (hxl t ht)⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_component_good_cross_sharp