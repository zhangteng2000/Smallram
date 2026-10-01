import ModifiedCartan.ScalarNormTwoPhase
import ModifiedCartan.LocalConvergenceAlgebra

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem balanced_max_eventually_eq_component
    {w : Fin 2 → ℂ → ℝ} {a : ℂ}
    (hc : ∀ j, ContinuousAt (w j) a)
    (hsum : w 0 a + w 1 a = 0) (hpos : 0 < max (w 0 a) (w 1 a)) :
    ∃ j : Fin 2, ∀ᶠ z in 𝓝 a, max (w 0 z) (w 1 z) = w j z ∧ 0 < w j z := by
  by_cases h01 : w 0 a < w 1 a
  · have hp : 0 < w 1 a := by simpa only [max_eq_right h01.le] using hpos
    refine ⟨1, ?_⟩
    filter_upwards [(hc 0).eventually_lt (hc 1) h01,
      continuousAt_const.eventually_lt (hc 1) hp] with z hz hpz
    exact ⟨max_eq_right hz.le, hpz⟩
  · have hp : 0 < w 0 a := by simpa only [max_eq_left (le_of_not_gt h01)] using hpos
    have h10 : w 1 a < w 0 a := by linarith
    refine ⟨0, ?_⟩
    filter_upwards [(hc 1).eventually_lt (hc 0) h10,
      continuousAt_const.eventually_lt (hc 0) hp] with z hz hpz
    exact ⟨max_eq_left hz.le, hpz⟩

/-- An actual polynomial component converges to the norm limit on a positive
neighborhood of every positive balanced good center. Auxiliary to `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_dominant_component_near_good_center
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {a : ℂ} (ha : a ∈ d.good_centers.centers) (hpos : 0 < (d.U a).toReal) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      ∃ (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) (j : Index 1) (R : ℝ),
        0 < R ∧ ball a R ⊆ ball (0 : ℂ) 2 ∧
        (∀ z ∈ ball a R, 0 < (d.U z).toReal) ∧
        (∀ ν, polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j ≠ 0) ∧
        LocalLpConvergence 1 (ball a R)
          (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
            Real.log ‖(polynomialMatrixGauge (d.polynomial (ns ν))
              (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z‖)
          (fun z => (d.U z).toReal) := by
  obtain ⟨ns, hns, V, u, v, hu, hmax, _, hsum⟩ := Paper.lem_basis_at_point d a ha
  have ha2 : a ∈ ball (0 : ℂ) 2 := (d.good_centers.subset ha).1
  have h24 : ball (0 : ℂ) 2 ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have ha4 := h24 ha2
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
  have hnear : ∀ᶠ z in 𝓝 a,
      z ∈ ball (0 : ℂ) 2 ∧ (d.U z).toReal = (u j z).toReal ∧ 0 < (d.U z).toReal := by
    filter_upwards [isOpen_ball.mem_nhds ha2, hj] with z hz hjz
    have he := (hm z (h24 hz)).trans hjz.1
    exact ⟨hz, he, he.symm ▸ hjz.2⟩
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp hnear
  have hR4 : ball a R ⊆ ball (0 : ℂ) 4 := fun z hz => h24 (hRU hz).1
  refine ⟨ns, hns, V, j, R, hR, fun z hz => (hRU hz).1,
    fun z hz => (hRU hz).2.2, ?_, ?_⟩
  · intro ν hzero
    obtain ⟨z, _, hn⟩ := (hu j).2.2.2.normalizedLog_nontrivial isOpen_ball
      ⟨a, ha4⟩ (d.scale_pos (ns ν))
    rw [hzero, Polynomial.eval_zero] at hn
    exact hn rfl
  · apply ((hu j).2.2.2.normalizedLog_real.restrict hR4).congr_ae
      (fun _ => EventuallyEq.rfl)
    have hrep := (hu j).2.2.1.filter_mono (ae_mono (Measure.restrict_mono_set _ hR4))
    filter_upwards [hrep, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzR
    have he : (u j z).toReal = v j z := by rw [hz, EReal.toReal_coe]
    exact he.symm.trans (hRU hzR).2.1.symm

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_dominant_component_near_good_center
