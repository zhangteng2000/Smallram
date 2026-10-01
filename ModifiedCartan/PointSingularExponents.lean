import ModifiedCartan.ArbitraryRadiusData
import ModifiedCartan.PointJetUpper
import ModifiedCartan.SingularExponentLimits
import ModifiedCartan.ReplacementNormProperties

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:singular-exponents`, for every good center of the actual
arbitrary-radius construction. The unitary matrices and finite exponents
are constructed, and the limit of their sum is proved to be zero. -/
theorem ArbitraryRadiusLimitData.exists_singular_exponents {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (a : ℂ) (ha : a ∈ d.good_centers.centers) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ (V : ℕ → Matrix.unitaryGroup (Index n) ℂ) (σ : ℕ → Index n → ℝ) (ell : Index n → ℝ),
        (∀ ν j, 0 < σ ν j) ∧
        (∀ ν j, σ ν j = scaledJetLength n (characteristic f (r (d.subseq (ns ν))))
          (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
            (V ν : Matrix (Index n) (Index n) ℂ) j).eval z) a) ∧
        (∀ ν, (∏ j, σ ν j) = (characteristic f (r (d.subseq (ns ν))))⁻¹ ^
          (∑ i : Index n, i.val) * ‖(FewInflection.polynomialWronskian (d.polynomial (ns ν))).eval a‖) ∧
        (∀ j, Tendsto (fun ν => Real.log (σ ν j) / characteristic f (r (d.subseq (ns ν))))
          atTop (𝓝 (ell j))) ∧ ∑ j, ell j = 0 := by
  classical
  let s : ℕ → ℝ := fun ν => characteristic f (r (d.subseq ν))
  have hex (ν : ℕ) := exists_polynomial_unitary_jet_lengths (d.scale_pos ν) (d.polynomial ν) a
    (d.good_centers.wronskian_ne_zero a ha ν)
  choose V σ hpos hnorm hprod using hex
  have hjet (ν : ℕ) (j : Index n) : σ ν j = scaledJetLength n (s ν)
      (fun z => (polynomialMatrixGauge (d.polynomial ν) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z) a :=
    hnorm ν j
  have hupper := unitary_polynomial_jet_eventual_bound d.scale_tendsto
    (d.replacement.polynomial_coordinate_bound d.C_pos d.A_pos d.scale_tendsto) V
      (d.good_centers.subset ha).1
  have hlogupper : ∀ᶠ ν in atTop, ∀ j,
      Real.log (σ ν j) / s ν ≤ (5 * d.C + 2) + 2 := by
    filter_upwards [hupper] with ν hν j
    apply (div_le_iff₀ (d.scale_pos ν)).mpr
    have hh : σ ν j ≤ Real.exp (((5 * d.C + 2) + 2) * s ν) := by
      rw [hjet]
      exact hν j
    simpa only [Real.log_exp] using Real.log_le_log (hpos ν j) hh
  have hsum := singular_log_sum_tendsto_zero (∑ i : Index n, i.val)
    d.scale_pos d.scale_tendsto
    (fun ν => norm_pos_iff.mpr (d.good_centers.wronskian_ne_zero a ha ν))
    hpos hprod (d.good_centers.log_wronskian a ha)
  obtain ⟨ns, hns, ell, hell, hzero⟩ := exists_balanced_finite_limit
    (show 0 ≤ (5 * d.C + 2) + 2 by linarith [d.C_pos]) hlogupper hsum
  exact ⟨ns, hns, V ∘ ns, σ ∘ ns, ell, fun ν => hpos (ns ν),
    fun ν => hjet (ns ν), fun ν => hprod (ns ν), hell, hzero⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.exists_singular_exponents
