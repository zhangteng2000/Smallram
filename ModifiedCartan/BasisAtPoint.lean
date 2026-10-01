import ModifiedCartan.GoodCenterComponentValue
import ModifiedCartan.UnitaryLogBalance
import ModifiedCartan.PointSingularExponents
import ModifiedCartan.JetAnchoredCompactness
import ModifiedCartan.ReplacementNormProperties

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan.Paper

/-- LaTeX `lem:basis-at-point`, including the exact `eq:point-balance`.
For every constructed good center, actual constant unitary matrices and
a common further subsequence give nontrivial subharmonic component limits.
Their maximum is the already fixed U and their actual values sum to zero
at the prescribed center. -/
theorem lem_basis_at_point {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (a : ℂ) (ha : a ∈ d.good_centers.centers) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
        (u : Index n → ℂ → EReal) (v : Index n → ℂ → ℝ),
        (∀ j, IsSubharmonicOn (ball (0 : ℂ) 4) (u j) ∧
          (∃ z ∈ ball (0 : ℂ) 4, u j z ≠ ⊥) ∧
          u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)) ∧
          LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
            (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
              (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
                (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) (v j)) ∧
        EqOn d.U (fun z => Finset.univ.sup (fun j => u j z)) (ball (0 : ℂ) 4) ∧
        (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, u j z) ∧
        ∑ j, u j a = 0 := by
  classical
  obtain ⟨ι, hι, V, σ, ell, hσ, hσnorm, _, hσlim, hell⟩ := d.exists_singular_exponents a ha
  let s : ℕ → ℝ := fun ν => characteristic f (r (d.subseq (ι ν)))
  let F : ℕ → Index n → ℂ → ℂ := fun ν j z =>
    (polynomialMatrixGauge (d.polynomial (ι ν)) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z
  have hs : Tendsto s atTop atTop := d.scale_tendsto.comp hι.tendsto_atTop
  have hb := unitary_polynomial_coordinate_eventual_bound hs
    (hι.tendsto_atTop.eventually
      (d.replacement.polynomial_coordinate_bound d.C_pos d.A_pos d.scale_tendsto)) V
  have hd : ∀ᶠ ν in atTop, ∀ j,
      AnalyticOnNhd ℂ (F ν j) (ball 0 4) ∧ 0 < scaledJetLength n (s ν) (F ν j) a ∧
      ∀ z ∈ ball (0 : ℂ) 4, ‖F ν j z‖ ≤ Real.exp (((5 * d.C + 2) + 1) * s ν) := by
    filter_upwards [hb] with ν hν j
    refine ⟨(AnalyticOnNhd.eval_polynomial (polynomialMatrixGauge (d.polynomial (ι ν))
      (V ν : Matrix (Index n) (Index n) ℂ) j)).mono (subset_univ _), ?_, hν j⟩
    rw [← hσnorm ν j]
    exact hσ ν j
  have hjetlim (j : Index n) : Tendsto
      (fun ν => Real.log (scaledJetLength n (s ν) (F ν j) a) / s ν) atTop (𝓝 (ell j)) := by
    simpa only [hσnorm, s, F] using hσlim j
  obtain ⟨ns, hns, _, u, v, hv⟩ := exists_common_jet_anchored_log_limits
    (d.good_centers.subset ha).1 hs hd hjetlim
  let τ : ℕ → ℕ := ι ∘ ns
  have hτ : StrictMono τ := hι.comp hns
  have hpoint (j : Index n) : u j a = (ell j : EReal) := by
    apply d.unitary_component_value_at_good_center a ha hτ (V ∘ ns) j
      (hv j).1 (hv j).2.2.1 (hv j).2.2.2
    · intro ν
      dsimp only [τ, Function.comp_apply]
      rw [← hσnorm (ns ν) j]
      exact hσ (ns ν) j
    · exact (hjetlim j).comp hns.tendsto_atTop
  have hbalance := d.unitary_norm_and_sum_limits a ha hτ (V ∘ ns)
    (fun j => (hv j).1) (fun j => (hv j).2.2.1) (fun j => (hv j).2.2.2)
  refine ⟨τ, hτ, V ∘ ns, u, v, hv, hbalance.1, hbalance.2, ?_⟩
  calc
    (∑ j, u j a) = ∑ j, (ell j : EReal) := Finset.sum_congr rfl (fun j _ => hpoint j)
    _ = ((∑ j, ell j : ℝ) : EReal) := (ereal_coe_finset_sum Finset.univ ell).symm
    _ = 0 := by rw [hell, EReal.coe_zero]

end ModifiedCartan.Paper
#print axioms ModifiedCartan.Paper.lem_basis_at_point
