import ModifiedCartan.DichotomyPrimitive
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.Deriv.Prod

open scoped Topology BoundedContinuousFunction
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {ι : Type*} [Fintype ι]

theorem perturbationInput_continuous
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (v : ι → ℂ) (u : ℝ →ᵇ (ι → ℂ)) (i : ι) :
    Continuous (fun s => A s (v + u s) i) :=
  (continuous_apply i).comp (hA.clm_apply (continuous_const.add u.continuous))

theorem perturbationInput_norm_le
    (A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)) (v : ι → ℂ)
    (u : ℝ →ᵇ (ι → ℂ)) (s : ℝ) (i : ι) :
    ‖A s (v + u s) i‖ ≤ ‖A s‖ * (‖v‖ + ‖u‖) := by
  calc
    ‖A s (v + u s) i‖ ≤ ‖A s (v + u s)‖ := norm_le_pi_norm _ i
    _ ≤ ‖A s‖ * ‖v + u s‖ := (A s).le_opNorm _
    _ ≤ ‖A s‖ * (‖v‖ + ‖u‖) := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add le_rfl (u.norm_coe_le_norm s))) (norm_nonneg _)

theorem perturbationInput_integrable
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A) {T : ℝ}
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ) (u : ℝ →ᵇ (ι → ℂ)) (i : ι) :
    IntegrableOn (fun s => A s (v + u s) i) (Ici T) := by
  apply Integrable.mono' (hAi.norm.mul_const (‖v‖ + ‖u‖))
    (perturbationInput_continuous hA v u i).aestronglyMeasurable
  exact Eventually.of_forall (fun s => perturbationInput_norm_le A v u s i)

theorem dichotomyIntegral_norm_le_majorant (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    {H : ℝ → ℝ} (hH : IntegrableOn H (Ici T))
    (hb : ∀ s ∈ Ici T, ‖f s‖ ≤ H s) (t : ℝ) :
    ‖dichotomyIntegral a T f t‖ ≤ ∫ s in Ici T, H s := by
  apply norm_integral_le_of_norm_le hH
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  calc
    ‖dichotomyKernel a t s * f s‖ = ‖dichotomyKernel a t s‖ * ‖f s‖ := norm_mul _ _
    _ ≤ ‖f s‖ := mul_le_of_le_one_left (norm_nonneg _) (dichotomyKernel_norm_le_one a t s)
    _ ≤ H s := hb s hs

noncomputable def dichotomyMapFun (a : ι → ℂ) (T : ℝ)
    (A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)) (v : ι → ℂ)
    (u : ℝ →ᵇ (ι → ℂ)) (t : ℝ) (i : ι) : ℂ :=
  dichotomyIntegral (a i) T (fun s => A s (v + u s) i) (max T t)

theorem dichotomyMapFun_continuous (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ) (u : ℝ →ᵇ (ι → ℂ)) :
    Continuous (dichotomyMapFun a T A v u) := by
  apply continuous_pi
  intro i
  exact (dichotomyIntegral_continuousOn (a i) (perturbationInput_integrable hA hAi v u i)
    (perturbationInput_continuous hA v u i)).comp_continuous
      (continuous_const.max continuous_id) (fun t => le_max_left T t)

theorem dichotomyMapFun_norm_le (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hAi : IntegrableOn A (Ici T))
    (v : ι → ℂ) (u : ℝ →ᵇ (ι → ℂ)) (t : ℝ) :
    ‖dichotomyMapFun a T A v u t‖ ≤ (∫ s in Ici T, ‖A s‖) * (‖v‖ + ‖u‖) := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (integral_nonneg (fun s => norm_nonneg (A s)))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr
  intro i
  calc
    ‖dichotomyMapFun a T A v u t i‖ ≤ ∫ s in Ici T, ‖A s‖ * (‖v‖ + ‖u‖) :=
      dichotomyIntegral_norm_le_majorant (a i) (hAi.norm.mul_const (‖v‖ + ‖u‖))
        (fun s _ => perturbationInput_norm_le A v u s i) (max T t)
    _ = _ := integral_mul_const _ _

noncomputable def dichotomyOperator (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ)
    (u : ℝ →ᵇ (ι → ℂ)) : ℝ →ᵇ (ι → ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (dichotomyMapFun a T A v u)
    (dichotomyMapFun_continuous a hA hAi v u)
    ((∫ s in Ici T, ‖A s‖) * (‖v‖ + ‖u‖)) (dichotomyMapFun_norm_le a hAi v u)

theorem dichotomyOperator_apply (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ)
    (u : ℝ →ᵇ (ι → ℂ)) (t : ℝ) (i : ι) :
    dichotomyOperator a hA hAi v u t i =
      dichotomyIntegral (a i) T (fun s => A s (v + u s) i) (max T t) := rfl

theorem dichotomyOperator_sub_norm_le (a : ι → ℂ) {T : ℝ}
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A)
    (hAi : IntegrableOn A (Ici T)) (v : ι → ℂ) (u w : ℝ →ᵇ (ι → ℂ)) :
    ‖dichotomyOperator a hA hAi v u - dichotomyOperator a hA hAi v w‖ ≤
      (∫ s in Ici T, ‖A s‖) * ‖u - w‖ := by
  have hnonneg : 0 ≤ (∫ s in Ici T, ‖A s‖) * ‖u - w‖ :=
    mul_nonneg (integral_nonneg (fun s => norm_nonneg (A s))) (norm_nonneg _)
  apply (BoundedContinuousFunction.norm_le hnonneg).mpr
  intro t
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro i
  change ‖dichotomyIntegral (a i) T (fun s => A s (v + u s) i) (max T t) -
    dichotomyIntegral (a i) T (fun s => A s (v + w s) i) (max T t)‖ ≤ _
  rw [← dichotomyIntegral_sub (a i) (perturbationInput_integrable hA hAi v u i)
    (perturbationInput_integrable hA hAi v w i)]
  calc
    _ ≤ ∫ s in Ici T, ‖A s‖ * ‖u - w‖ := by
      apply dichotomyIntegral_norm_le_majorant (a i) (hAi.norm.mul_const ‖u - w‖)
      intro s _
      have he : A s (v + u s) - A s (v + w s) = A s (u s - w s) := by
        rw [← map_sub]
        congr 1
        abel
      change ‖(A s (v + u s) - A s (v + w s)) i‖ ≤ _
      rw [he]
      calc
        _ ≤ ‖A s (u s - w s)‖ := norm_le_pi_norm _ i
        _ ≤ ‖A s‖ * ‖u s - w s‖ := (A s).le_opNorm _
        _ ≤ ‖A s‖ * ‖u - w‖ :=
          mul_le_mul_of_nonneg_left ((u - w).norm_coe_le_norm s) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

end ModifiedCartan
#print axioms ModifiedCartan.dichotomyMapFun_norm_le
#print axioms ModifiedCartan.dichotomyOperator_sub_norm_le


