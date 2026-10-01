import ModifiedCartan.SubharmonicRepresentative

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A continuous real almost-everywhere representative agrees everywhere
with the given subharmonic representative on the open domain. -/
theorem IsSubharmonicOn.eqOn_of_ae_eq_continuous {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → EReal} {v : ℂ → ℝ} (hu : IsSubharmonicOn U u)
    (hv : ContinuousOn v U)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal))) :
    EqOn u (fun z => (v z : EReal)) U := by
  have hvc : ContinuousOn (fun z => (v z : EReal)) U :=
    continuous_coe_real_ereal.comp_continuousOn hv
  have hupper := hu.le_of_ae_le_upperSemicontinuous hvc.upperSemicontinuousOn hU
    (hrep.mono (fun _ hz => hz.le))
  intro x hx
  apply le_antisymm (hupper x hx)
  by_contra hnot
  obtain ⟨M, huM, hMv⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  have hsmall : ∀ᶠ z in 𝓝 x, u z < (M : EReal) := by
    simpa only [hU.nhdsWithin_eq hx] using hu.upperSemicontinuousOn x hx (M : EReal) huM
  have hlarge : ∀ᶠ z in 𝓝 x, (M : EReal) < (v z : EReal) :=
    (hvc.continuousAt (hU.mem_nhds hx)).eventually (lt_mem_nhds hMv)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hsmall hlarge) (hU.mem_nhds hx))
  have hball : ball x r ⊆ U := hsub.trans inter_subset_right
  have hre := hrep.filter_mono (ae_mono (Measure.restrict_mono_set _ hball))
  obtain ⟨z, hz, he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hr)) hre
  have hzsmall : u z < (M : EReal) := (hsub hz).1.1
  have hzlarge : (M : EReal) < (v z : EReal) := (hsub hz).1.2
  rw [he] at hzsmall
  exact (not_lt_of_ge hzsmall.le) hzlarge

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.eqOn_of_ae_eq_continuous
