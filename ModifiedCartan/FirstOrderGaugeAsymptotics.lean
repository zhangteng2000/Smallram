import ModifiedCartan.FirstOrderGaugeSolutions

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [CompleteSpace V]

theorem linearGauge_apply_tendsto (C : V →L[ℂ] V) {X : ℝ → V} {v : V}
    (hX : Tendsto X atTop (𝓝 v)) :
    Tendsto (fun t => linearGauge C t (X t)) atTop (𝓝 v) := by
  have hC := (C.continuous.tendsto v).comp hX
  have hh := hX.add ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul hC)
  simpa only [zero_smul, add_zero, linearGauge, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, Function.comp_apply] using! hh

theorem powerLinearGauge_normalization (C : V →L[ℂ] V) (b : ℝ)
    (X : ℝ → V) (lam : ℂ) {t : ℝ} (ht : 0 < t) :
    t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • powerLinearGauge C b X t) =
      linearGauge C t (Complex.exp (-lam * (t : ℂ)) • X t) := by
  rw [powerLinearGauge, smul_comm (Complex.exp (-lam * (t : ℂ))) (t ^ b),
    smul_smul, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, one_smul]
  exact ((linearGauge C t).map_smul _ _).symm

theorem powerLinearGauge_normalized_tendsto (C : V →L[ℂ] V) (b : ℝ)
    {X : ℝ → V} {lam : ℂ} {v : V}
    (hX : Tendsto (fun t : ℝ => Complex.exp (-lam * (t : ℂ)) • X t) atTop (𝓝 v)) :
    Tendsto (fun t : ℝ => t ^ (-b) •
      (Complex.exp (-lam * (t : ℂ)) • powerLinearGauge C b X t)) atTop (𝓝 v) := by
  apply (linearGauge_apply_tendsto C hX).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (powerLinearGauge_normalization C b X lam ht).symm

theorem powerLinearGauge_linearIndependent {ι : Type*} (C : V →L[ℂ] V) (b : ℝ)
    (X : ι → ℝ → V) {t : ℝ} (ht : 0 < t) (hu : IsUnit (linearGauge C t))
    (hX : LinearIndependent ℂ (fun j => X j t)) :
    LinearIndependent ℂ (fun j => powerLinearGauge C b (X j) t) := by
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have hm := hX.map' (linearGauge C t).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)
  let w : ι → ℂˣ := fun _ => Units.mk0 ((t ^ b : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht b).ne')
  have hh := hm.units_smul w
  change LinearIndependent ℂ (fun j => ((t ^ b : ℝ) : ℂ) • linearGauge C t (X j t)) at hh
  have hs (a : ℝ) (v : V) : (a : ℂ) • v = a • v := IsScalarTower.algebraMap_smul ℂ a v
  simpa only [hs, powerLinearGauge] using! hh

end ModifiedCartan
#print axioms ModifiedCartan.powerLinearGauge_normalized_tendsto
#print axioms ModifiedCartan.powerLinearGauge_linearIndependent

