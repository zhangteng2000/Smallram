import ModifiedCartan.SubharmonicAveragingApproximation
import ModifiedCartan.AveragedL1Compactness
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem tendsto_eLpNorm_of_toL1 {μ : Measure ℂ} {f : ℕ → ℂ → ℝ}
    (hf : ∀ n, Integrable (f n) μ) {v : Lp ℝ 1 μ}
    (h : Tendsto (fun n => (hf n).toL1 (f n)) atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (f n - (v : ℂ → ℝ)) 1 μ) atTop (𝓝 0) := by
  have heq : ∀ n, edist ((hf n).toL1 (f n)) v = eLpNorm (f n - (v : ℂ → ℝ)) 1 μ := by
    intro n
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hf n).coeFn_toL1.sub (ae_eq_refl _))
  simpa only [heq, edist_self] using h.edist (tendsto_const_nhds (x := v))

/-- Compactness on one disk, derived from the submean definition and a larger-disk L1 bound. -/
theorem subharmonic_l1_subsequence_on_disk
    {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → EReal}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hfinite : ∀ n, ∀ᵐ z ∂volume.restrict U, u n z ≠ ⊥ ∧ u n z ≠ ⊤)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hball : closedBall c (4 * R) ⊆ U)
    {B : ℝ}
    (hint : ∀ n, IntegrableOn (fun z => (u n z).toReal) (closedBall c (4 * R)))
    (hbound : ∀ n, (∫ z in closedBall c (4 * R), ‖(u n z).toReal‖) ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ v : ℂ → ℝ,
      IntegrableOn v (closedBall c R) ∧
      Tendsto (fun n => eLpNorm ((fun z => (u (ns n) z).toReal) - v) 1
        (volume.restrict (closedBall c R))) atTop (𝓝 0) := by
  classical
  let K := closedBall c R
  let T := closedBall c (4 * R)
  let f : ℕ → ℂ → ℝ := fun n z => (u n z).toReal
  have hKT : K ⊆ T := closedBall_subset_closedBall (by linarith)
  have hfK : ∀ n, IntegrableOn (f n) K volume := fun n => (hint n).mono_set hKT
  let F : ℕ → Lp ℝ 1 (volume.restrict K) := fun n => (hfK n).toL1 (f n)
  let fT : ℕ → ℂ → ℝ := fun n => T.indicator (f n)
  have hfT : ∀ n, Integrable (fT n) :=
    fun n => (hint n).integrable_indicator isClosed_closedBall.measurableSet
  have hB : 0 ≤ B := (integral_nonneg (fun z => norm_nonneg _)).trans (hbound 0)
  have hnorm : ∀ n, (∫ z, ‖fT n z‖) ≤ B := by
    intro n
    simpa only [fT, T, f, norm_indicator_eq_indicator_norm,
      integral_indicator isClosed_closedBall.measurableSet] using hbound n
  obtain ⟨L, happrox⟩ := subharmonic_uniform_averaging_approximation_on_disk
    hU hu hfinite hR hball hint hbound
  have htotal : TotallyBounded (range F) := by
    apply totallyBounded_range_of_uniform_approximation
    intro ε hε
    obtain ⟨ρ, hρ, hρε⟩ := exists_pos_mul_lt hε (2 * (L : ℝ) * B)
    let r := min ρ (R / 2)
    have hr : 0 < r := lt_min hρ (by positivity)
    have hrρ : r ≤ ρ := min_le_left _ _
    have hrR : r ≤ R / 2 := min_le_right _ _
    let G : ℕ → ℂ → ℝ := fun n => diskAverage r (diskAverage r (fT n))
    have hG : ∀ n, IntegrableOn (G n) K volume := fun n =>
      (diskAverage_integrable hr.le (diskAverage_integrable hr.le (hfT n))).integrableOn
    refine ⟨fun n => (hG n).toL1 (G n), ?_, ?_⟩
    · exact totallyBounded_l1_range_diskAverage_twice (isCompact_closedBall c R) hfT hnorm hr
    · intro n
      change dist ((hfK n).toL1 (f n)) ((hG n).toL1 (G n)) ≤ ε
      rw [dist_toL1_eq_integral_norm (hfK n) (hG n)]
      have herr := happrox n r hr hrR
      have herr' : (∫ z in K, ‖f n z - G n z‖) ≤ 2 * (L : ℝ) * r * B := by
        simpa only [f, G, fT, T, K, norm_sub_rev] using herr
      refine herr'.trans ?_
      calc
        _ = (2 * (L : ℝ) * B) * r := by ring
        _ ≤ (2 * (L : ℝ) * B) * ρ := mul_le_mul_of_nonneg_left hrρ (by positivity)
        _ ≤ ε := hρε.le
  have hcompact := htotal.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨v, _, ns, hns, hconv⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨ns, hns, v, L1.integrable_coeFn v, ?_⟩
  exact tendsto_eLpNorm_of_toL1 (fun n => hfK (ns n)) hconv


end ModifiedCartan
