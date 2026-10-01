import ModifiedCartan.WeakGradientCalculus

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def phaseIndicator (g : ℂ → ℂ) (a : ℂ) : ℂ → ℝ :=
  {z | g z = a}.indicator (fun _ => 1)

theorem phaseIndicator_eq_ite (g : ℂ → ℂ) (a z : ℂ) :
    phaseIndicator g a z = if g z = a then 1 else 0 := by
  classical
  rfl

theorem phaseIndicator_nonneg (g : ℂ → ℂ) (a z : ℂ) : 0 ≤ phaseIndicator g a z := by
  rw [phaseIndicator_eq_ite]
  split_ifs <;> norm_num

theorem norm_phaseIndicator_le_one (g : ℂ → ℂ) (a z : ℂ) : ‖phaseIndicator g a z‖ ≤ 1 := by
  rw [phaseIndicator_eq_ite]
  split_ifs <;> norm_num

theorem integrableOn_phaseIndicator {K : Set ℂ} (hK : IsCompact K)
    {g : ℂ → ℂ} (hg : IntegrableOn g K) (a : ℂ) : IntegrableOn (phaseIndicator g a) K := by
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hm : AEStronglyMeasurable g (volume.restrict K) := hg.aestronglyMeasurable
  have hs : NullMeasurableSet {z | g z = a} (volume.restrict K) :=
    hm.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton a)
  exact (integrable_const (1 : ℝ)).indicator₀ hs

noncomputable def phaseCutoff (K : Set ℂ) (g : ℂ → ℂ) (a : ℂ) : ℂ → ℝ :=
  K.indicator (phaseIndicator g a)

theorem phaseCutoff_eq {K : Set ℂ} {g : ℂ → ℂ} {a z : ℂ} (hz : z ∈ K) :
    phaseCutoff K g a z = phaseIndicator g a z := indicator_of_mem hz _

theorem integrable_phaseCutoff {K : Set ℂ} (hK : IsCompact K)
    {g : ℂ → ℂ} (hg : IntegrableOn g K) (a : ℂ) : Integrable (phaseCutoff K g a) :=
  (integrableOn_phaseIndicator hK hg a).integrable_indicator hK.measurableSet

theorem phaseCutoff_nonneg (K : Set ℂ) (g : ℂ → ℂ) (a z : ℂ) : 0 ≤ phaseCutoff K g a z := by
  classical
  by_cases hz : z ∈ K
  · rw [phaseCutoff_eq hz]
    exact phaseIndicator_nonneg g a z
  · simp only [phaseCutoff, indicator_of_notMem hz, le_refl]

theorem norm_phaseCutoff_le_one (K : Set ℂ) (g : ℂ → ℂ) (a z : ℂ) : ‖phaseCutoff K g a z‖ ≤ 1 := by
  classical
  by_cases hz : z ∈ K
  · rw [phaseCutoff_eq hz]
    exact norm_phaseIndicator_le_one g a z
  · simp only [phaseCutoff, indicator_of_notMem hz, norm_zero, zero_le_one]

end ModifiedCartan
#print axioms ModifiedCartan.integrable_phaseCutoff
