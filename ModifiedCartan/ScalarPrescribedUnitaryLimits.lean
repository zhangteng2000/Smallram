import ModifiedCartan.ScalarUnitaryJetLower
import ModifiedCartan.JetLowerCompactness
import ModifiedCartan.PointwiseUnitaryBalance

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Nontrivial logarithmic limits are constructed for every prescribed actual
unitary basis. Both components lie between -U and U. In particular, the basis
may be the fixed one determined by a scalar target. Auxiliary to `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_exists_prescribed_unitary_log_limits
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ (u : Index 1 → ℂ → EReal) (v : Index 1 → ℂ → ℝ),
        (∀ j, IsSubharmonicOn (ball (0 : ℂ) 4) (u j) ∧
          (∃ z ∈ ball (0 : ℂ) 4, u j z ≠ ⊥) ∧
          u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)) ∧
          LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
            (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
              (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
                (V (ns ν) : Matrix (Index 1) (Index 1) ℂ) j).eval z)) (v j)) ∧
        EqOn d.U (fun z => Finset.univ.sup (fun j => u j z)) (ball (0 : ℂ) 4) ∧
        (∀ j z, z ∈ ball (0 : ℂ) 4 →
          -(d.U z).toReal ≤ (u j z).toReal ∧ (u j z).toReal ≤ (d.U z).toReal) := by
  obtain ⟨a, _, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 2)))
    d.good_centers.full_measure
  obtain ⟨B, _, hlower⟩ := d.scalar_unitary_jet_exp_lower ha V
  have hupper := unitary_polynomial_coordinate_eventual_bound d.scale_tendsto
    (d.replacement.polynomial_coordinate_bound d.C_pos d.A_pos d.scale_tendsto) V
  let F : ℕ → Index 1 → ℂ → ℂ := fun ν j z =>
    (polynomialMatrixGauge (d.polynomial ν) (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z
  have hd : ∀ᶠ ν in atTop, ∀ j,
      AnalyticOnNhd ℂ (F ν j) (ball 0 4) ∧
        Real.exp (-B * characteristic f (r (d.subseq ν))) ≤
          scaledJetLength 1 (characteristic f (r (d.subseq ν))) (F ν j) a ∧
          ∀ z ∈ ball (0 : ℂ) 4, ‖F ν j z‖ ≤
            Real.exp (((5 * d.C + 2) + 1) * characteristic f (r (d.subseq ν))) := by
    filter_upwards [hlower, hupper] with ν hlν huν j
    exact ⟨(AnalyticOnNhd.eval_polynomial (polynomialMatrixGauge (d.polynomial ν)
      (V ν : Matrix (Index 1) (Index 1) ℂ) j)).mono (subset_univ _), hlν j, huν j⟩
  obtain ⟨ns, hns, _, u, v, hu⟩ := exists_common_jet_lower_log_limits
    (d.good_centers.subset ha).1 d.scale_tendsto hd
  have hb := d.unitary_norm_and_sum_limits a ha hns (V ∘ ns)
    (fun j => (hu j).1) (fun j => (hu j).2.2.1) (fun j => (hu j).2.2.2)
  have hreg (j : Index 1) := d.unitary_component_regular hns (V ∘ ns) j
    (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hsum := d.unitary_component_sum_nonneg hns (V ∘ ns)
    (fun j => (hu j).1) (fun j => (hu j).2.2.1) (fun j => (hu j).2.2.2) hb.2
  have hle (j : Index 1) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) :
      (u j z).toReal ≤ (d.U z).toReal := by
    have hh : u j z ≤ d.U z := by
      rw [hb.1 hz]
      exact Finset.le_sup (f := fun k => u k z) (Finset.mem_univ j)
    rw [(hreg j).1 z hz, d.norm_limit_continuous.1 z hz] at hh
    exact_mod_cast hh
  refine ⟨ns, hns, u, v, hu, hb.1, ?_⟩
  intro j z hz
  have hs : 0 ≤ (u 0 z).toReal + (u 1 z).toReal := by
    have hh := hsum z hz
    change 0 ≤ ∑ j : Fin 2, (u j z).toReal at hh
    simpa only [Fin.sum_univ_two] using hh
  have h₀ := hle 0 z hz
  have h₁ := hle 1 z hz
  fin_cases j
  · change -(d.U z).toReal ≤ (u 0 z).toReal ∧ (u 0 z).toReal ≤ (d.U z).toReal
    constructor <;> linarith
  · change -(d.U z).toReal ≤ (u 1 z).toReal ∧ (u 1 z).toReal ≤ (d.U z).toReal
    constructor <;> linarith

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_prescribed_unitary_log_limits
