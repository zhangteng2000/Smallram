import ModifiedCartan.ScalarSectorComponent
import ModifiedCartan.ScalarPositiveCenters

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- An arbitrary geometric center is allowed: the actual good center used for
the basis is chosen inside its positive chart. Auxiliary to thm:A (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_component_on_chart
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2))
    (hbpos : 0 < b.re) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      ∃ (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) (j : Index 1),
        (∀ ν, polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j ≠ 0) ∧
        LocalLpConvergence 1 (scalarPositiveChart a ρ b)
          (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
            Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
              (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖)
          (fun z => (d.U z).toReal) := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have h24 : ball (0 : ℂ) 2 ⊆ ball (0 : ℂ) 4 := ball_subset_ball (by norm_num)
  have hΩo := scalarPositiveChart_isOpen ha hr b
  have hΩ2 : scalarPositiveChart a ρ b ⊆ ball (0 : ℂ) 2 := scalarPositiveChart_subset ha hr
  obtain ⟨z₀, hz₀Ω, hz₀g⟩ := d.good_centers.exists_mem_of_isOpen hΩo
    ⟨a, self_mem_scalarPositiveChart ha ha2 hr hbpos⟩ hΩ2
  have hz₀4 := h24 (hΩ2 hz₀Ω)
  obtain ⟨ns, hns, V, u, v, hu, hmax, _, _⟩ := Paper.lem_basis_at_point d z₀ hz₀g
  have hreg (j : Index 1) := d.unitary_component_regular hns V j
    (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hm (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) :
      (d.U z).toReal = max (u 0 z).toReal (u 1 z).toReal := by
    have he : d.U z = ((max (u 0 z).toReal (u 1 z).toReal : ℝ) : EReal) := by
      rw [hmax hz]
      have hf : (fun j => u j z) = (fun j => ((u j z).toReal : EReal)) :=
        funext (fun j => (hreg j).1 z hz)
      change Finset.univ.sup (fun j => u j z) = _
      rw [hf]
      simpa only using! ereal_fin_two_sup_coe (fun j => (u j z).toReal)
    rw [he, EReal.toReal_coe]
  have hex : ∃ j : Index 1, (u j z₀).toReal = (d.U z₀).toReal := by
    rw [hm z₀ hz₀4]
    rcases le_total (u 0 z₀).toReal (u 1 z₀).toReal with hle | hle
    · exact ⟨1, (max_eq_right hle).symm⟩
    · exact ⟨0, (max_eq_left hle).symm⟩
  obtain ⟨j, hj⟩ := hex
  have hle (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) : (u j z).toReal ≤ (d.U z).toReal := by
    rw [hm z hz]
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hnorm := d.scalar_norm_positiveChart_pullback hρ ha b hb
  have hconv := d.unitary_component_powerChart_convex hρ ha (by linarith : ‖a‖ < 4)
    hns V j (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hsub : positivePowerChartDomain a ρ b ⊆ powerChartDomain a ρ :=
    fun _ hw => powerChartInnerDomain_subset hr.le hw.1
  obtain ⟨w₀, hw₀, hw₀z⟩ := hz₀Ω
  have heq : EqOn (fun w => (u j (powerChart a ρ w)).toReal) (fun w => (b * w).re)
      (positivePowerChartDomain a ρ b) := by
    have hpoint : (u j (powerChart a ρ w₀)).toReal = 0 + (b * w₀).re := by
      have hn := hnorm hw₀
      dsimp only at hn
      rw [hw₀z] at hn
      simpa only [zero_add, hw₀z] using hj.trans hn
    have hupper : ∀ w ∈ positivePowerChartDomain a ρ b,
        (u j (powerChart a ρ w)).toReal ≤ 0 + (b * w).re := by
      intro w hw
      have hn := hnorm hw
      dsimp only at hn
      simpa only [zero_add, hn] using
        hle (powerChart a ρ w) (h24 (powerChartInnerDomain_mapsTo ha hr hw.1))
    simpa only [zero_add] using
      convex_eq_affine_of_le_of_eq (k := 0) (positivePowerChartDomain_isOpen a ρ b)
        (hconv.subset hsub (positivePowerChartDomain_convex a ρ b)) hw₀ hpoint hupper
  have heqU : EqOn (fun z => (u j z).toReal) (fun z => (d.U z).toReal)
      (scalarPositiveChart a ρ b) := by
    rintro z ⟨w, hw, rfl⟩
    exact (heq hw).trans (hnorm hw).symm
  have hΩ4 : scalarPositiveChart a ρ b ⊆ ball (0 : ℂ) 4 := hΩ2.trans h24
  refine ⟨ns, hns, V, j, ?_, ?_⟩
  · intro ν hzero
    obtain ⟨z, _, hn⟩ := (hu j).2.2.2.normalizedLog_nontrivial isOpen_ball
      ⟨z₀, hz₀4⟩ (d.scale_pos (ns ν))
    rw [hzero, Polynomial.eval_zero] at hn
    exact hn rfl
  · apply ((hu j).2.2.2.normalizedLog_real.restrict hΩ4).congr_ae (fun _ => EventuallyEq.rfl)
    have hrep := (hu j).2.2.1.filter_mono (ae_mono (Measure.restrict_mono_set _ hΩ4))
    filter_upwards [hrep, ae_restrict_mem hΩo.measurableSet] with z hz hzΩ
    have he : (u j z).toReal = v j z := by rw [hz, EReal.toReal_coe]
    exact he.symm.trans (heqU hzΩ)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_component_on_chart
