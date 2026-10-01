import ModifiedCartan.ScalarPositiveChart
import ModifiedCartan.ScalarDominantComponent
import ModifiedCartan.ScalarPowerChartProfile
import ModifiedCartan.ConvexAffineContact
import ModifiedCartan.UnitaryPowerConvexity

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A positive choice of the actual central quadratic root. -/
theorem ArbitraryRadiusLimitData.scalar_exists_positive_root
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha2 : ‖a‖ < 2)
    (hpos : 0 < (d.U a).toReal) :
    ∃ b : ℂ, b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      b.re = (d.U a).toReal ∧ 0 < b.re := by
  obtain ⟨q, hq, hU⟩ := d.scalar_norm_value_root hρ ha ha2
  by_cases hp : 0 ≤ q.re
  · have he : q.re = (d.U a).toReal := by rw [hU, abs_of_nonneg hp]
    exact ⟨q, hq, he, he.symm ▸ hpos⟩
  · have he : (-q).re = (d.U a).toReal := by rw [Complex.neg_re, hU, abs_of_neg (lt_of_not_ge hp)]
    exact ⟨-q, by simpa only [neg_sq] using hq, he, he.symm ▸ hpos⟩

theorem ArbitraryRadiusLimitData.scalar_norm_positiveChart_pullback
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)) :
    EqOn (fun w => (d.U (powerChart a ρ w)).toReal) (fun w => (b * w).re)
      (positivePowerChartDomain a ρ b) := by
  intro w hw
  dsimp only
  have hr := lt_of_lt_of_le zero_lt_one hρ
  rw [d.scalar_norm_powerChart_profile hρ ha b hb
    (powerChartInnerDomain_subset hr.le hw.1)
    (by simpa only [mem_ball, dist_zero_right] using powerChartInnerDomain_mapsTo ha hr hw.1)]
  exact abs_of_pos hw.2

theorem ArbitraryRadiusLimitData.scalar_norm_positiveChart_pos
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)) :
    ∀ z ∈ scalarPositiveChart a ρ b, 0 < (d.U z).toReal := by
  rintro z ⟨w, hw, rfl⟩
  have he := d.scalar_norm_positiveChart_pullback hρ ha b hb hw
  dsimp only at he
  rw [he]
  exact hw.2

/-- The selected actual component equals the norm limit throughout the positive
chart region. Its existence follows from point balance and proved convexity;
no sector dominance is imposed. Auxiliary to LaTeX `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_component_on_positive_chart
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ∈ d.good_centers.centers)
    (hpos : 0 < (d.U a).toReal) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      ∃ (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) (j : Index 1) (b : ℂ),
        b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
        b.re = (d.U a).toReal ∧ 0 < b.re ∧
        (∀ ν, polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j ≠ 0) ∧
        LocalLpConvergence 1 (scalarPositiveChart a ρ b)
          (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
            Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
              (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖)
          (fun z => (d.U z).toReal) := by
  have ha2 : a ∈ ball (0 : ℂ) 2 := (d.good_centers.subset ha).1
  have ha0 : a ≠ 0 := by simpa only [mem_singleton_iff] using (d.good_centers.subset ha).2
  have haNorm : ‖a‖ < 2 := by simpa only [mem_ball, dist_zero_right] using ha2
  have h24 : ball (0 : ℂ) 2 ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have ha4 := h24 ha2
  have hr := lt_of_lt_of_le zero_lt_one hρ
  obtain ⟨b, hb, hbRe, hbpos⟩ := d.scalar_exists_positive_root hρ ha0 haNorm hpos
  obtain ⟨ns, hns, V, u, v, hu, hmax, _, hsum⟩ := Paper.lem_basis_at_point d a ha
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
  have hs : (u 0 a).toReal + (u 1 a).toReal = 0 := by
    change (∑ j : Fin 2, u j a) = 0 at hsum
    rw [Fin.sum_univ_two, (hreg 0).1 a ha4, (hreg 1).1 a ha4, ← EReal.coe_add] at hsum
    exact EReal.coe_eq_zero.mp hsum
  have hc (j : Index 1) : ContinuousAt (fun z => (u j z).toReal) a :=
    (hreg j).2.continuousOn.continuousAt (isOpen_ball.mem_nhds ha4)
  obtain ⟨j, hj⟩ := balanced_max_eventually_eq_component hc hs (by rwa [← hm a ha4])
  have hja : (u j a).toReal = (d.U a).toReal :=
    (mem_of_mem_nhds hj).1.symm.trans (hm a ha4).symm
  have hle (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) : (u j z).toReal ≤ (d.U z).toReal := by
    rw [hm z hz]
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hnorm := d.scalar_norm_positiveChart_pullback hρ ha0 b hb
  have hconv := d.unitary_component_powerChart_convex hρ ha0 (by linarith : ‖a‖ < 4)
    hns V j (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hsub : positivePowerChartDomain a ρ b ⊆ powerChartDomain a ρ :=
    fun _ hw => powerChartInnerDomain_subset hr.le hw.1
  have heq : EqOn (fun w => (u j (powerChart a ρ w)).toReal) (fun w => (b * w).re)
      (positivePowerChartDomain a ρ b) := by
    have hpoint : (u j (powerChart a ρ 1)).toReal = 0 + (b * 1).re := by
      simpa only [powerChart_one, mul_one, zero_add] using hja.trans hbRe.symm
    have hupper : ∀ w ∈ positivePowerChartDomain a ρ b,
        (u j (powerChart a ρ w)).toReal ≤ 0 + (b * w).re := by
      intro w hw
      have hn := hnorm hw
      dsimp only at hn
      simpa only [zero_add, hn] using
        hle (powerChart a ρ w) (h24 (powerChartInnerDomain_mapsTo ha0 hr hw.1))
    simpa only [zero_add] using
      convex_eq_affine_of_le_of_eq (k := 0) (positivePowerChartDomain_isOpen a ρ b)
        (hconv.subset hsub (positivePowerChartDomain_convex a ρ b))
        (positivePowerChartDomain_one_mem ha0 haNorm hr hbpos) hpoint hupper
  have heqU : EqOn (fun z => (u j z).toReal) (fun z => (d.U z).toReal)
      (scalarPositiveChart a ρ b) := by
    rintro z ⟨w, hw, rfl⟩
    exact (heq hw).trans (hnorm hw).symm
  have hΩ4 : scalarPositiveChart a ρ b ⊆ ball (0 : ℂ) 4 :=
    (scalarPositiveChart_subset ha0 hr).trans h24
  refine ⟨ns, hns, V, j, b, hb, hbRe, hbpos, ?_, ?_⟩
  · intro ν hzero
    obtain ⟨z, _, hn⟩ := (hu j).2.2.2.normalizedLog_nontrivial isOpen_ball
      ⟨a, ha4⟩ (d.scale_pos (ns ν))
    rw [hzero, Polynomial.eval_zero] at hn
    exact hn rfl
  · apply ((hu j).2.2.2.normalizedLog_real.restrict hΩ4).congr_ae (fun _ => EventuallyEq.rfl)
    have hrep := (hu j).2.2.1.filter_mono (ae_mono (Measure.restrict_mono_set _ hΩ4))
    filter_upwards [hrep, ae_restrict_mem (scalarPositiveChart_isOpen ha0 hr b).measurableSet] with z hz hzΩ
    have he : (u j z).toReal = v j z := by rw [hz, EReal.toReal_coe]
    exact he.symm.trans (heqU hzΩ)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_component_on_positive_chart
