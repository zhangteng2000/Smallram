import ModifiedCartan.DichotomyOperator
import Mathlib.Topology.MetricSpace.Contracting

open scoped Topology BoundedContinuousFunction
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {ι : Type*} [Fintype ι]

theorem dichotomyOperator_contracting (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ)
    (hsmall : (∫ s in Ici T, ‖A s‖) < 1) :
    ContractingWith ⟨∫ s in Ici T, ‖A s‖, integral_nonneg (fun s => norm_nonneg (A s))⟩
      (dichotomyOperator a hA hAi v) := by
  constructor
  · exact hsmall
  · apply LipschitzWith.of_dist_le_mul
    intro u w
    simpa only [dist_eq_norm, NNReal.coe_mk] using! dichotomyOperator_sub_norm_le a hA hAi v u w

theorem dichotomy_fixedPoint_deriv (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ) {u : ℝ →ᵇ (ι → ℂ)}
    (hu : Function.IsFixedPt (dichotomyOperator a hA hAi v) u)
    {t : ℝ} (ht : T ≤ t) :
    HasDerivWithinAt (fun s => u s)
      (fun i => a i * u t i + A t (v + u t) i) (Ici T) t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  have he (s : ℝ) (hs : s ∈ Ici T) :
      u s i = dichotomyIntegral (a i) T (fun x => A x (v + u x) i) s := by
    have h := congrArg (fun w : ℝ →ᵇ (ι → ℂ) => w s i) hu.eq
    simpa only [dichotomyOperator_apply, max_eq_right (show T ≤ s from hs)] using h.symm
  have hd := dichotomyIntegral_hasDerivWithinAt (a i)
    (perturbationInput_integrable hA hAi v u i) (perturbationInput_continuous hA v u i) ht
  rw [← he t ht] at hd
  exact hd.congr_of_mem he ht

theorem dichotomy_fixedPoint_tendsto_zero (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ) {u : ℝ →ᵇ (ι → ℂ)}
    (hu : Function.IsFixedPt (dichotomyOperator a hA hAi v) u) :
    Tendsto (fun t => u t) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hmax : Tendsto (fun t : ℝ => max T t) atTop atTop :=
    tendsto_atTop_mono (fun t => le_max_right T t) tendsto_id
  have hi := (dichotomyIntegral_tendsto_zero (a i)
    (perturbationInput_integrable hA hAi v u i)).comp hmax
  apply hi.congr'
  apply Eventually.of_forall
  intro t
  exact congrArg (fun w : ℝ →ᵇ (ι → ℂ) => w t i) hu.eq

/-- Actual bounded normalized solutions from Banach's theorem; no solution
existence or asymptotic property is assumed. Used by `lem:integrable-system`. -/
theorem dichotomy_tail_solution_exists (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ)
    (hsmall : (∫ s in Ici T, ‖A s‖) < 1) :
    ∃ u : ℝ →ᵇ (ι → ℂ),
      (∀ t ∈ Ici T, HasDerivWithinAt (fun s => u s)
        (fun i => a i * u t i + A t (v + u t) i) (Ici T) t) ∧
      Tendsto (fun t => u t) atTop (𝓝 0) := by
  have hc := dichotomyOperator_contracting a hA hAi v hsmall
  let u := hc.fixedPoint (dichotomyOperator a hA hAi v)
  have hu : Function.IsFixedPt (dichotomyOperator a hA hAi v) u := hc.fixedPoint_isFixedPt
  exact ⟨u, (fun t ht => dichotomy_fixedPoint_deriv a hA hAi v hu ht),
    dichotomy_fixedPoint_tendsto_zero a hA hAi v hu⟩

end ModifiedCartan
#print axioms ModifiedCartan.dichotomy_tail_solution_exists

