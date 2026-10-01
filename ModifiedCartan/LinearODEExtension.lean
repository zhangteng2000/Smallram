import ModifiedCartan.LinearODECompact

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Extend an actual tail solution to the original starting time. The two
solutions agree on a whole overlap by proved linear ODE uniqueness. -/
theorem linearODE_extend_from_tail {B : ℝ → V →L[ℝ] V} {a T : ℝ}
    (haT : a ≤ T) (hB : ContinuousOn B (Ici a)) {f : ℝ → V}
    (hf : ∀ t, T ≤ t → HasDerivWithinAt f (B t (f t)) (Ici T) t) :
    ∃ g : ℝ → V,
      (∀ t, a ≤ t → HasDerivAt g (B t (g t)) t) ∧
      (∀ t, T + 1 ≤ t → g t = f t) := by
  have hBcompact : ContinuousOn B (Icc a (T + 1)) := hB.mono Icc_subset_Ici_self
  obtain ⟨u, hub, huc, hud⟩ := continuousOn_linearODE_solution_exists
    (show a ≤ T + 1 by linarith) hBcompact (T + 1) (f (T + 1))
  have hfc : ContinuousOn f (Icc T (T + 1)) := fun t ht =>
    (hf t ht.1).continuousWithinAt.mono Icc_subset_Ici_self
  have heq : EqOn u f (Icc T (T + 1)) := by
    apply continuousOn_linearODE_unique_left
      (hB.mono (fun t ht => haT.trans ht.1)) huc.continuousOn hfc _ _ hub
    · intro t ht
      exact hud t ⟨haT.trans ht.1.le, ht.2⟩
    · intro t ht
      exact (hf t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  let c : ℝ := T + 1 / 2
  have hTc : T < c := by dsimp [c]; linarith
  have hcb : c < T + 1 := by dsimp [c]; linarith
  let g : ℝ → V := fun t => if t ≤ c then u t else f t
  refine ⟨g, ?_, ?_⟩
  · intro t hat
    rcases lt_trichotomy t c with htc | rfl | hct
    · have hg : g =ᶠ[𝓝 t] u := by
        filter_upwards [gt_mem_nhds htc] with s hs
        simp only [g, ite_eq_left hs.le]
      have hd := (hud t ⟨hat, (htc.trans hcb).le⟩).congr_of_eventuallyEq hg
      simpa only [g, ite_eq_left htc.le] using hd
    · have hg : g =ᶠ[𝓝 c] u := by
        filter_upwards [Ioo_mem_nhds hTc hcb] with s hs
        dsimp [g]
        split_ifs with hsc
        · rfl
        · exact (heq ⟨hs.1.le, hs.2.le⟩).symm
      have hd := (hud c ⟨haT.trans hTc.le, hcb.le⟩).congr_of_eventuallyEq hg
      simpa only [g, ite_eq_left le_rfl] using hd
    · have hg : g =ᶠ[𝓝 t] f := by
        filter_upwards [lt_mem_nhds hct] with s hs
        simp only [g, ite_eq_right (not_le.mpr hs)]
      have hd := ((hf t (hTc.trans hct).le).hasDerivAt
        (Ici_mem_nhds (hTc.trans hct))).congr_of_eventuallyEq hg
      simpa only [g, ite_eq_right (not_le.mpr hct)] using hd
  · intro t ht
    exact ite_eq_right (not_le.mpr (hcb.trans_le ht))

end ModifiedCartan
#print axioms ModifiedCartan.linearODE_extend_from_tail
