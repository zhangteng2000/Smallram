import ModifiedCartan.ArbitraryRadiusReindex
import ModifiedCartan.ScalarChartDominance
import ModifiedCartan.ScalarSectorGeometry
import ModifiedCartan.ScalarFiniteTargets

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Cross estimates on finitely many actual full peak charts are extracted on
one subsequence while preserving the actual norm and coefficient limits. -/
theorem ArbitraryRadiusLimitData.scalar_finite_peak_crosses
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {N : ℕ} (a : Fin N → ℂ)
    (ha : ∀ j, ‖a j‖ = 1)
    (hroot : ∀ j, (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic (a j)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ j,
      HasSmallRectangleCrosses f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν)))) (scalarFullSector (a j) ρ) := by
  let P : Fin N → (ℕ → ℕ) → Prop := fun j τ =>
    HasSmallRectangleCrosses f (fun ν => r (d.subseq (τ ν)))
      (fun ν => characteristic f (r (d.subseq (τ ν)))) (scalarFullSector (a j) ρ)
  apply finite_subsequence_extraction N P
  · intro j τ hτ
    let e := d.reindex τ hτ
    have haj : a j ≠ 0 := norm_ne_zero_iff.mp (by rw [ha j]; norm_num)
    have haj2 : ‖a j‖ < 2 := by rw [ha j]; norm_num
    have hρpos := lt_of_lt_of_le zero_lt_one hρ
    have hbpos : 0 < (((Real.pi / 2 : ℝ) : ℂ)).re := half_pos Real.pi_pos
    obtain ⟨σ, hσ, V, i, hP, hlog⟩ := e.scalar_exists_component_on_chart hρ haj haj2
      (((Real.pi / 2 : ℝ) : ℂ)) (hroot j) hbpos
    have hcross := e.scalar_component_small_rectangle_crosses hlin htrans hsmall hρ hl hu hr
      hσ V i (scalarPositiveChart_isOpen haj hρpos _) (scalarPositiveChart_isPreconnected _ hρpos _)
      (scalarPositiveChart_subset haj hρpos)
      (e.scalar_norm_positiveChart_pos hρ haj _ (hroot j)) hP hlog
    have he : scalarFullSector (a j) ρ = scalarPositiveChart (a j) ρ (((Real.pi / 2 : ℝ) : ℂ)) :=
      scalarFullSector_eq_positive (half_pos Real.pi_pos)
    rw [← he] at hcross
    exact ⟨σ, hσ, hcross⟩
  · intro j τ σ hP hσ
    exact hP.comp hσ.tendsto_atTop

/-- One physical subsequence supplies all targets and all actual line bounds
on a finite family of full peak charts. Auxiliary to thm:A (b). -/
theorem ArbitraryRadiusLimitData.scalar_finite_peak_targets
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {N : ℕ} (a : Fin N → ℂ)
    (ha : ∀ j, ‖a j‖ = 1)
    (hroot : ∀ j, (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic (a j)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ β : Fin N → WithTop ℂ,
      ∃ q : (j : Fin N) → ScalarHorizontalSelection f (fun ν => r (d.subseq (ns ν)))
        (fun ν => characteristic f (r (d.subseq (ns ν)))) (scalarFullSector (a j) ρ),
        ∀ j, HasSmallRectangleCrosses f (fun ν => r (d.subseq (ns ν)))
          (fun ν => characteristic f (r (d.subseq (ns ν)))) (scalarFullSector (a j) ρ) ∧
          ∀ R : {R : ComplexRect // R.closed ⊆ scalarFullSector (a j) ρ},
            Tendsto ((q j).anchor R) atTop (𝓝 (scalarSphereValue (β j))) ∧
            ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
              ‖scalarCurveSphere f ((r (d.subseq (ns ν)) : ℂ) * (⟨t, (q j).height R ν⟩ : ℂ)) -
                scalarSphereValue (β j)‖ < ε := by
  obtain ⟨ns₁, hns₁, hcross⟩ := d.scalar_finite_peak_crosses hlin htrans hsmall hρ hl hu hr a ha hroot
  have hr₁ := (hr.comp d.strictMono.tendsto_atTop).comp hns₁.tendsto_atTop
  have hs₁ := d.scale_tendsto.comp hns₁.tendsto_atTop
  have haj (j : Fin N) : a j ≠ 0 := norm_ne_zero_iff.mp (by rw [ha j]; norm_num)
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  obtain ⟨ns₂, hns₂, β, q, ht⟩ := scalar_finite_common_line_targets
    (fun j => scalarFullSector (a j) ρ) hcross hr₁ hs₁
    (fun j => scalarFullSector_isOpen (haj j) hρpos)
    (fun j => scalarFullSector_isConnected (haj j) (by rw [ha j]; norm_num) hρpos)
  exact ⟨ns₁ ∘ ns₂, hns₁.comp hns₂, β, q, ht⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_finite_peak_crosses
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_finite_peak_targets
