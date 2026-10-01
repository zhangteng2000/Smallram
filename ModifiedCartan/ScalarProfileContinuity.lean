import ModifiedCartan.ScalarProfileUniqueness
import Mathlib.Topology.UniformSpace.HeineCantor

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A convergent coefficient on a fixed circle gives uniform convergence of
its continuous profiles on every compact set. -/
theorem scalarQuadraticProfile_uniform_of_tendsto (m : ℕ)
    {R : ℝ} {C : ℕ → ℂ} {C₀ : ℂ} (hC : ∀ ν, ‖C ν‖ = R) (hC₀ : ‖C₀‖ = R)
    (hlim : Tendsto C atTop (𝓝 C₀)) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ν => scalarQuadraticProfile m (C ν))
      (scalarQuadraticProfile m C₀) atTop K := by
  have hsource : ∀ ν, C ν ∈ sphere (0 : ℂ) R := by
    intro ν
    simpa only [mem_sphere, dist_zero_right] using hC ν
  have htarget : C₀ ∈ sphere (0 : ℂ) R := by
    simpa only [mem_sphere, dist_zero_right] using hC₀
  have huni := UniformContinuousOn.tendstoUniformlyOn (F := scalarQuadraticProfile m)
    (((isCompact_sphere (0 : ℂ) R).prod hK).uniformContinuousOn_of_continuous
      (continuous_scalarQuadraticProfile m).continuousOn) htarget
  have hwithin : Tendsto C atTop (𝓝[sphere (0 : ℂ) R] C₀) := by
    simpa only [nhdsWithin, inf_idem] using hlim.inf
      (show Tendsto C atTop (𝓟 (sphere (0 : ℂ) R)) from
        tendsto_principal.mpr (Eventually.of_forall hsource))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact hwithin.eventually (Metric.tendstoUniformlyOn_iff.mp huni ε hε)

/-- On the compact coefficient circle, convergence of profiles in local
measure forces ordinary convergence of the coefficient. -/
theorem scalarQuadraticProfile_parameter_tendsto {m : ℕ} (hm : m ≠ 0)
    {R : ℝ} {C : ℕ → ℂ} {C₀ : ℂ} (hC : ∀ ν, ‖C ν‖ = R) (hC₀ : ‖C₀‖ = R)
    (hlim : LocalMeasureConvergence (ball (0 : ℂ) 1)
      (fun ν => scalarQuadraticProfile m (C ν)) (scalarQuadraticProfile m C₀)) :
    Tendsto C atTop (𝓝 C₀) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨D, hD, ms, hms, hconv⟩ := (isCompact_sphere (0 : ℂ) R).tendsto_subseq
    (fun ν => show C (ns ν) ∈ sphere (0 : ℂ) R from by
      simpa only [mem_sphere, dist_zero_right] using hC (ns ν))
  have hDn : ‖D‖ = R := by simpa only [mem_sphere, dist_zero_right] using hD
  have hconv' : Tendsto (fun ν => C (ns (ms ν))) atTop (𝓝 D) := by
    simpa only [Function.comp_def] using hconv
  have huni := scalarQuadraticProfile_uniform_of_tendsto m (fun ν => hC (ns (ms ν))) hDn hconv'
    (isCompact_closedBall (0 : ℂ) 1)
  have hM := uniformlyOn_localMeasureConvergence huni ball_subset_closedBall
  have hfirst := (hlim.comp hns).comp hms.tendsto_atTop
  have heq := scalarQuadraticProfile_injective_of_ae_eq hm (hC₀.trans hDn.symm)
    (LocalMeasureConvergence.ae_unique isOpen_ball hfirst hM)
  exact ⟨ms, heq.symm ▸ hconv'⟩

/-- The compact-family coefficient of an actual scalar limit is unique. -/
theorem ArbitraryRadiusLimitData.scalar_existsUnique_quadratic_profile
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop) {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    ∃! C : ℂ, ‖C‖ = (Real.pi / 2) ^ 2 ∧
      EqOn (fun z => 2 * (d.U z).toReal) (scalarQuadraticProfile m C) (ball (0 : ℂ) 2) := by
  obtain ⟨C, hC, hprofile⟩ := d.scalar_exists_quadratic_profile hρ hr hm
  refine ⟨C, ⟨hC, hprofile⟩, ?_⟩
  rintro D ⟨hD, hDprofile⟩
  apply scalarQuadraticProfile_injective_of_norm_eq (m := m) (by
    intro hm0
    rw [hm0, Nat.cast_zero, zero_div] at hm
    linarith) (hD.trans hC.symm)
  intro z hz
  have hz2 : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
  exact (hDprofile hz2).symm.trans (hprofile hz2)

end ModifiedCartan
#print axioms ModifiedCartan.scalarQuadraticProfile_parameter_tendsto
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_existsUnique_quadratic_profile

