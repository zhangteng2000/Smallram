import ModifiedCartan.ScalarHorizontalSelection

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Limit targets constructed on overlapping domains agree when their actual
physical sequences agree. The selections of good lines may be different. -/
theorem ScalarHorizontalSelection.target_eq_of_overlap
    {f : Curve 1} {r s : ℕ → ℝ} {Ω₁ Ω₂ : Set ℂ}
    (q₁ : ScalarHorizontalSelection f r s Ω₁) (q₂ : ScalarHorizontalSelection f r s Ω₂)
    (hcross : HasSmallRectangleCrosses f r s Ω₁)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hΩ₁ : IsOpen Ω₁) (hΩ₂ : IsOpen Ω₂) (hov : (Ω₁ ∩ Ω₂).Nonempty)
    {b₁ b₂ : WithTop ℂ}
    (ht₁ : ∀ R : {R : ComplexRect // R.closed ⊆ Ω₁},
      Tendsto (q₁.anchor R) atTop (𝓝 (scalarSphereValue b₁)))
    (ht₂ : ∀ R : {R : ComplexRect // R.closed ⊆ Ω₂},
      Tendsto (q₂.anchor R) atTop (𝓝 (scalarSphereValue b₂))) : b₁ = b₂ := by
  obtain ⟨z, hz⟩ := hov
  obtain ⟨a, b, c, d, hab, hcd, _, hR⟩ :=
    exists_closed_rectangle_neighborhood (hΩ₁.inter hΩ₂) hz
  let R : ComplexRect := ⟨a, b, c, d, hab, hcd⟩
  have hR₁ : R.closed ⊆ Ω₁ := fun w hw => (hR hw).1
  have hR₂ : R.closed ⊆ Ω₂ := fun w hw => (hR hw).2
  have hRR : R.Overlaps R := by
    obtain ⟨w, hw⟩ := R.openSet_nonempty
    exact ⟨w, hw, hw⟩
  have hd : Tendsto (fun ν => ‖q₁.anchor ⟨R, hR₁⟩ ν - q₂.anchor ⟨R, hR₂⟩ ν‖)
      atTop (𝓝 0) :=
    hcross.adjacent_horizontal_anchors hr hs hR₁ hR₁ hRR
      (q₁.rate_pos ⟨R, hR₁⟩) (q₂.rate_pos ⟨R, hR₂⟩)
      (q₁.good ⟨R, hR₁⟩) (q₂.good ⟨R, hR₂⟩)
  have hz : Tendsto (fun ν => q₁.anchor ⟨R, hR₁⟩ ν - q₂.anchor ⟨R, hR₂⟩ ν)
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hd
  have htarget := (ht₁ ⟨R, hR₁⟩).sub (ht₂ ⟨R, hR₂⟩)
  have he : scalarSphereValue b₁ - scalarSphereValue b₂ = 0 := tendsto_nhds_unique htarget hz
  exact scalarSphereValue_injective (sub_eq_zero.mp he)

end ModifiedCartan
#print axioms ModifiedCartan.ScalarHorizontalSelection.target_eq_of_overlap
