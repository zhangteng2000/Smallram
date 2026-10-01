import ModifiedCartan.ArbitraryRadiusData
import ModifiedCartan.PointValueUpper
import ModifiedCartan.PointValueLower
import ModifiedCartan.PointInitialCoarse

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The center value equals the finite singular exponent, for the actual
polynomial basis change at any of the constructed good centers. -/
theorem ArbitraryRadiusLimitData.unitary_component_value_at_good_center
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (a : ℂ) (ha : a ∈ d.good_centers.centers) {ns : ℕ → ℕ} (hns : StrictMono ns)
    (V : ℕ → Matrix.unitaryGroup (Index n) ℂ) (j : Index n)
    {u : ℂ → EReal} {v : ℂ → ℝ} {ell : ℝ}
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hconv : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) v)
    (hj : ∀ ν, 0 < scaledJetLength n (characteristic f (r (d.subseq (ns ν))))
      (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
        (V ν : Matrix (Index n) (Index n) ℂ) j).eval z) a)
    (hlim : Tendsto (fun ν => Real.log (scaledJetLength n (characteristic f (r (d.subseq (ns ν))))
      (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
        (V ν : Matrix (Index n) (Index n) ℂ) j).eval z) a) /
          characteristic f (r (d.subseq (ns ν)))) atTop (𝓝 ell)) : u a = (ell : EReal) := by
  let s : ℕ → ℝ := fun ν => characteristic f (r (d.subseq (ns ν)))
  let F : ℕ → ℂ → ℂ := fun ν z => (polynomialMatrixGauge (d.polynomial (ns ν))
    (V ν : Matrix (Index n) (Index n) ℂ) j).eval z
  have hspos (ν : ℕ) : 0 < s ν := d.scale_pos (ns ν)
  have hs : Tendsto s atTop atTop := d.scale_tendsto.comp hns.tendsto_atTop
  have ha2 := (d.good_centers.subset ha).1
  have ha4 := (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)) ha2
  apply le_antisymm
  · obtain ⟨C, _, hroot⟩ := d.good_centers.root_sum_bound a ha
    apply log_limit_value_le_singular_exponent (n := n) ha2 (D := (n + 1 : ℝ)) (by positivity)
      hspos hs hj hlim (hns.tendsto_atTop.eventually hroot) _ hu hrep hconv
    filter_upwards [hns.tendsto_atTop.eventually d.replacement.root_factorization,
      hs.eventually_ge_atTop 1] with ν hW hsν z hz
    have hz' : ‖z - a‖ ≤ 1 :=
      (show ‖z - a‖ < 1 by simpa only [mem_ball, dist_eq_norm] using hz).le
    have hh := polynomial_matrix_initial_value_coarse_bound hsν (d.polynomial (ns ν))
      (V ν : Matrix (Index n) (Index n) ℂ) (d.roots (ns ν)) hW a
      (d.good_centers.wronskian_ne_zero a ha (ns ν)) j hz'
    have he : a + (z - a) = z := by ring
    simpa only [he, reciprocalDistanceSum, F, s] using hh
  · apply jet_exponent_le_log_limit_value ha4 hspos hs _ _ hu hrep hconv
      (Eventually.of_forall hj) hlim
    · intro ν
      exact (AnalyticOnNhd.eval_polynomial (polynomialMatrixGauge (d.polynomial (ns ν))
        (V ν : Matrix (Index n) (Index n) ℂ) j)).mono (subset_univ _)
    · intro ν
      exact hconv.normalizedLog_nontrivial isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩ (hspos ν)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_value_at_good_center
