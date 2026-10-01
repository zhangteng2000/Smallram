import ModifiedCartan.SharpnessCombinations
import ModifiedCartan.RaySolutionExpansion
import ModifiedCartan.RayPrimitives

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem rayCompanion_solution_unique {q : ℕ} {ρ β T : ℝ}
    (hρ : ρ ≠ 0) (hT : 0 < T) (δ η : ℂ) {X Y : ℝ → Fin q → ℂ}
    (hX : ∀ t, T ≤ t → HasDerivAt X
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (X t)) t)
    (hY : ∀ t, T ≤ t → HasDerivAt Y
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (Y t)) t)
    (he : X T = Y T) : ∀ t, T ≤ t → X t = Y t := by
  have hB := rayCompanionCLM_continuousOn (q := q) hρ β δ η hT
  exact linearODE_unique_halfLine
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hB) hX hY he

/-- Every actual ray mode is realized by a constant combination of the original
prescribed entire solutions. This derives the needed change of basis from W=1. -/
theorem IsSharpnessSystem.realizes_ray_solution {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1)
    {ρ β T : ℝ} (hρ : 0 < ρ) (hT : 0 < T)
    (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k) {δ η : ℂ}
    (hδ : δ ≠ 0) (hphase : δ ^ q = η ^ k) (X : ℝ → Fin q → ℂ)
    (hX : ∀ t, T ≤ t → HasDerivAt X
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (X t)) t) :
    ∃ c : Index n → ℂ, ∀ t, T ≤ t →
      rayDerivativeJet q ρ β δ η (iteratedDeriv (n + 1 - q) (sharpnessCombination g c)) t = X t := by
  obtain ⟨c, hc⟩ := h.combination_with_derivative_jet_exists hq hqn
    (rayPoint ρ η T) (rayScale ρ β δ T) (X T)
  let w := sharpnessCombination g c
  let y := iteratedDeriv (n + 1 - q) w
  have hw : Differentiable ℂ w := h.combination_differentiable c
  have hy : Differentiable ℂ y := entire_iteratedDeriv hw _
  have heq : ∀ z, iteratedDeriv q y z = z ^ k * y z :=
    scalar_equation_of_iterated_primitive hqn (h.combination_equation c)
  have hinit : rayDerivativeJet q ρ β δ η y T = X T := by
    funext i
    change iteratedDeriv i.val y (rayPoint ρ η T) / rayScale ρ β δ T ^ i.val = X T i
    rw [hc i]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (rayScale_ne_zero hρ hT β hδ))
  refine ⟨c, ?_⟩
  exact rayCompanion_solution_unique hρ.ne' hT δ η
    (fun t ht => rayDerivativeJet_companion_hasDerivAt hρ (lt_of_lt_of_le hT ht)
      hρβ hβ hδ hphase hy heq) hX hinit

/-- A positive-rate mode supplies an actual scalar combination of the prescribed
solutions with the full nonzero primitive asymptotic. -/
theorem IsSharpnessSystem.realizes_positive_ray_mode {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1)
    {ρ β T : ℝ} (hρ : 0 < ρ) (hT : 0 < T)
    (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k) {δ η : ℂ}
    (hδ : δ ≠ 0) (hη : η ≠ 0) (hphase : δ ^ q = η ^ k)
    (X : ℝ → Fin q → ℂ) (j : Fin q)
    (hX : ∀ t, T ≤ t → HasDerivAt X
      ((rayCompanionCoefficient q ρ β δ η t).mulVec (X t)) t)
    (hl : Tendsto (fun t : ℝ => t ^ (-rayDiagonalPower q ρ β) •
        (Complex.exp (-raySpectralValues q δ η j * (t : ℂ)) • X t))
      atTop (𝓝 (fun i : Fin q => sharpnessRoot q j ^ i.val)))
    (hpos : 0 < (raySpectralValues q δ η j).re) :
    ∃ c : Index n → ℂ, ∃ d : ℂ, d ≠ 0 ∧
      Tendsto (fun t => sharpnessCombination g c (rayPoint ρ η t) /
        powerExpProfile (raySpectralValues q δ η j)
          (rayDiagonalPower q ρ β + ((n + 1 - q : ℕ) : ℝ) * rayPrimitivePower ρ) t)
        atTop (𝓝 d) := by
  obtain ⟨c, hc⟩ := h.realizes_ray_solution hq hqn hρ hT hρβ hβ hδ hphase X hX
  let i0 : Fin q := ⟨0, by omega⟩
  have hfirst := (continuous_apply i0).tendsto _ |>.comp hl
  change Tendsto (fun t : ℝ => (t ^ (-rayDiagonalPower q ρ β) •
    (Complex.exp (-raySpectralValues q δ η j * (t : ℂ)) • X t)) i0)
    atTop (𝓝 (sharpnessRoot q j ^ i0.val)) at hfirst
  simp only [Pi.smul_apply, i0, pow_zero] at hfirst
  have hy : Tendsto (fun t => iteratedDeriv (n + 1 - q) (sharpnessCombination g c)
      (rayPoint ρ η t) / powerExpProfile (raySpectralValues q δ η j)
        (rayDiagonalPower q ρ β) t) atTop (𝓝 1) := by
    apply hfirst.congr'
    filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (0 : ℝ)] with t ht htp
    have he := congrFun (hc t ht) i0
    have he' : iteratedDeriv (n + 1 - q) (sharpnessCombination g c) (rayPoint ρ η t) = X t i0 := by
      simpa only [rayDerivativeJet, rayDerivativeCoordinate, i0, iteratedDeriv_zero, pow_zero, div_one] using he
    rw [← he']
    exact powerExpProfile_normalization htp _ _ _
  obtain ⟨d, hd, hdl⟩ := ray_iteratedPrimitive_ratio_limit hρ hη (n + 1 - q)
    (h.combination_differentiable c) hpos one_ne_zero hy
  exact ⟨c, d, hd, hdl⟩

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.realizes_ray_solution
#print axioms ModifiedCartan.IsSharpnessSystem.realizes_positive_ray_mode
