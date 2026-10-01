import ModifiedCartan.ScalarNormSquare
import ModifiedCartan.ClassicalWeakGradient
import ModifiedCartan.LogNormPathDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Topology ContDiff
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Branch-free square-root formula for the actual scalar norm limit,
including the origin. Auxiliary to LaTeX `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_norm_eq_sqrt
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2) :
    (d.U z).toReal = Real.sqrt
      ((‖-(d.coefficient 0 z * (z * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)‖ +
        (-(d.coefficient 0 z * (z * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)).re) / 2) := by
  by_cases hzero : z = 0
  · subst z
    simp only [d.origin_zero, EReal.toReal_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, neg_zero, norm_zero, Complex.zero_re, add_zero, zero_div, Real.sqrt_zero]
  · rw [← d.scalar_norm_square hρ hzero (by simpa only [mem_ball, dist_zero_right] using hz)]
    exact (Real.sqrt_sq (EReal.toReal_nonneg
      (d.nonneg z ((ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)) hz)))).symm

/-- The actual limit is smooth wherever it is positive. No sector regularity
or nonvanishing coefficient is added as a hypothesis. -/
theorem ArbitraryRadiusLimitData.scalar_norm_contDiffAt_of_pos
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ∈ ball (0 : ℂ) 2)
    (hpos : 0 < (d.U a).toReal) :
    ContDiffAt ℝ ∞ (fun z => (d.U z).toReal) a := by
  let Q : ℂ → ℂ := fun z => -(d.coefficient 0 z * (z * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)
  have ha0 : a ≠ 0 := by
    intro he
    simpa only [he, d.origin_zero, EReal.toReal_zero, lt_self_iff_false] using hpos
  have hs : (d.U a).toReal ^ 2 = (‖Q a‖ + (Q a).re) / 2 :=
    d.scalar_norm_square hρ ha0 (by simpa only [mem_ball, dist_zero_right] using ha)
  have hQ0 : Q a ≠ 0 := by
    intro he
    rw [he, norm_zero, Complex.zero_re, add_zero, zero_div] at hs
    nlinarith
  have hQ : ContDiffAt ℝ ∞ Q a := by
    have hc : ContDiffAt ℝ ∞ (d.coefficient 0) a :=
      ((d.coefficient_analytic 0 a (mem_univ a)).contDiffAt).restrict_scalars ℝ
    exact (hc.mul ((contDiffAt_id.mul contDiffAt_const).pow 2)).neg
  have hS : ContDiffAt ℝ ∞ (fun z => (‖Q z‖ + (Q z).re) / 2) a :=
    ((hQ.norm ℂ hQ0).add (Complex.reCLM.contDiff.contDiffAt.comp a hQ)).div_const 2
  have hn : (‖Q a‖ + (Q a).re) / 2 ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hpos.ne'
  apply (hS.sqrt hn).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds ha] with z hz
  exact d.scalar_norm_eq_sqrt hρ hz

theorem ArbitraryRadiusLimitData.scalar_norm_contDiffOn_of_pos
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {Ω : Set ℂ} (hΩ : Ω ⊆ ball (0 : ℂ) 2)
    (hpos : ∀ z ∈ Ω, 0 < (d.U z).toReal) :
    ContDiffOn ℝ ∞ (fun z => (d.U z).toReal) Ω :=
  fun z hz => (d.scalar_norm_contDiffAt_of_pos hρ (hΩ hz) (hpos z hz)).contDiffWithinAt

/-- The weak gradient used in the good-line construction is derived from
the actual scalar limit, on any open part of its positive region. -/
theorem ArbitraryRadiusLimitData.scalar_norm_hasWeakComplexGradient_of_pos
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ ball (0 : ℂ) 2)
    (hpos : ∀ z ∈ Ω, 0 < (d.U z).toReal) :
    HasWeakComplexGradient Ω (fun z => (d.U z).toReal)
      (classicalComplexGradient (fun z => (d.U z).toReal)) :=
  contDiffOn_hasWeakComplexGradient hΩopen
    ((d.scalar_norm_contDiffOn_of_pos hρ hΩ hpos).of_le (by norm_num))

theorem hasDerivAt_horizontal_of_differentiableAt
    {u : ℂ → ℝ} {x y : ℝ} (hu : DifferentiableAt ℝ u (⟨x, y⟩ : ℂ)) :
    HasDerivAt (fun t : ℝ => u (⟨t, y⟩ : ℂ))
      (classicalComplexGradient u (⟨x, y⟩ : ℂ)).re x := by
  rw [classicalComplexGradient_re]
  exact hu.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horizontal_complex x y)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_contDiffAt_of_pos
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_hasWeakComplexGradient_of_pos
