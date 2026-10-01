import ModifiedCartan.DiskAverages
import ModifiedCartan.LocalSubsequence
import ModifiedCartan.LocalConvergenceAlgebra

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- One common AE set satisfies every disk mean inequality, obtained from a pointwise
subsequence. No uncountable intersection of full-measure sets is used. -/
theorem ae_le_diskAverage_of_subharmonic_limit {U : Set ℂ} (hU : IsOpen U)
    {u : ℕ → ℂ → EReal} (hu : ∀ n, IsSubharmonicOn U (u n))
    (hfinite : ∀ n, ∀ᵐ z ∂volume.restrict U, u n z ≠ ⊥ ∧ u n z ≠ ⊤)
    {f : ℂ → ℝ} (hconv : LocalLpConvergence 1 U (fun n z => (u n z).toReal) f) :
    ∀ᵐ z ∂volume.restrict U, ∀ r : ℝ, 0 < r → closedBall z r ⊆ U →
      f z ≤ diskAverage r f z := by
  obtain ⟨ns, hns, hpoint⟩ := hconv.exists_seq_tendsto_ae (by norm_num) hU
  have hsub := hconv.comp_strictMono hns
  filter_upwards [hpoint, ae_all_iff.mpr hfinite] with z hz hzfinite
  intro r hr hball
  have havg := hsub.diskAverage_tendstoUniformlyOn (isCompact_closedBall z r) hball hr
    (K := {z}) (fun w hw => by
      have : w = z := mem_singleton_iff.mp hw
      subst w
      exact ball_subset_closedBall)
  have havgz := havg.tendsto_at (mem_singleton z)
  apply le_of_tendsto_of_tendsto hz havgz
  apply Eventually.of_forall
  intro n
  have hle := (hu (ns n)).le_diskAverage_value hr hball
  rw [← EReal.coe_toReal (hzfinite (ns n)).2 (hzfinite (ns n)).1, EReal.coe_le_coe_iff] at hle
  exact hle


end ModifiedCartan
