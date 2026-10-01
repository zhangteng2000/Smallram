import ModifiedCartan.RaySolutionExpansion
import ModifiedCartan.ExponentialUpperRate
import ModifiedCartan.RayUpperPrimitives
import ModifiedCartan.SharpnessCombinations

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Upper ray growth of an actual scalar solution follows from the constructed
fundamental system and its proved constant-coefficient expansion. -/
theorem scalar_ray_upper_rate {q k : ℕ} (hq : 1 ≤ q) {ρ β H : ℝ}
    (hρ : 0 < ρ) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k) {δ η : ℂ}
    (hδ : δ ≠ 0) (hη : η ≠ 0) (hphase : δ ^ q = η ^ k)
    (hH : ∀ j : Fin q, (raySpectralValues q δ η j).re ≤ H)
    {y : ℂ → ℂ} (hy : Differentiable ℂ y)
    (heq : ∀ z, iteratedDeriv q y z = z ^ k * y z) :
    HasExponentialUpperRate H (fun t => y (rayPoint ρ η t)) := by
  obtain ⟨T, _hT, X, _hd, _hli, hl, hspan⟩ :=
    scalar_ray_fundamental_expansion hq hρ hρβ hβ hδ hη hphase
  obtain ⟨c, hc⟩ := hspan y hy heq
  let i0 : Fin q := ⟨0, by omega⟩
  have hbasis (j : Fin q) : HasExponentialUpperRate H (fun t => X j t i0) := by
    have hfirst := (continuous_apply i0).tendsto _ |>.comp (hl j)
    change Tendsto (fun t : ℝ => (t ^ (-rayDiagonalPower q ρ β) •
      (Complex.exp (-raySpectralValues q δ η j * (t : ℂ)) • X j t)) i0)
      atTop (𝓝 (sharpnessRoot q j ^ i0.val)) at hfirst
    simp only [Pi.smul_apply, i0, pow_zero] at hfirst
    exact HasExponentialUpperRate.of_normalized_limit (hH j) hfirst
  have hsum := HasExponentialUpperRate.sum (Finset.univ : Finset (Fin q))
    (fun j _ => (hbasis j).const_mul (c j))
  apply hsum.congr
  filter_upwards [eventually_ge_atTop T] with t ht
  have he := congrFun (hc t ht) i0
  simpa only [rayDerivativeJet, rayDerivativeCoordinate, i0, iteratedDeriv_zero,
    pow_zero, div_one, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he.symm

/-- Every coordinate of the actual prescribed system has at most the maximal
root rate; all intervening primitives are handled by proved upper-rate lemmas. -/
theorem IsSharpnessSystem.coordinate_ray_upper_rate {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1)
    {ρ β H : ℝ} (hρ : 0 < ρ) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k)
    {δ η : ℂ} (hδ : δ ≠ 0) (hη : η ≠ 0) (hphase : δ ^ q = η ^ k)
    (hH : 0 ≤ H) (hbound : ∀ j : Fin q, (raySpectralValues q δ η j).re ≤ H)
    (j : Index n) : HasExponentialUpperRate H (fun t => g j (rayPoint ρ η t)) := by
  have hy := entire_iteratedDeriv (h.1 j) (n + 1 - q)
  have heq := scalar_equation_of_iterated_primitive hqn (h.2.2 j)
  have hu := scalar_ray_upper_rate (by omega : 1 ≤ q) hρ hρβ hβ hδ hη hphase hbound hy heq
  exact ray_iteratedPrimitive_upper_rate hρ hH η (n + 1 - q) (h.1 j) hu

end ModifiedCartan
#print axioms ModifiedCartan.scalar_ray_upper_rate
#print axioms ModifiedCartan.IsSharpnessSystem.coordinate_ray_upper_rate
