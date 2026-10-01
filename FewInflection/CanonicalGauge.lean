import FewInflection.ScalarWronskian
import FewInflection.FundamentalAnalytic

open scoped BigOperators Topology
open Filter Asymptotics
namespace FewInflection
noncomputable section

/-- The coefficient of the top lower derivative changes by the logarithmic
    derivative of a scalar gauge. -/
theorem fundamental_last_coefficient_scalarGauge
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g)
    {z : ℂ} (hW : wronskian n f.coord z ≠ 0) :
    fundamentalCoefficients n (f.scalarGauge g hg hgd).coord z
        ⟨n, Nat.lt_succ_self n⟩ =
      fundamentalCoefficients n f.coord z ⟨n, Nat.lt_succ_self n⟩ -
        (n + 1 : ℂ) * deriv g z / g z := by
  have hAf : ∀ j : Index n, AnalyticAt ℂ (f.coord j) z := by
    intro j
    have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (f.holomorphic j)
    exact hA z (Set.mem_univ z)
  have hAg : AnalyticAt ℂ g z := by
    have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hgd
    exact hA z (Set.mem_univ z)
  have hWg : wronskian n (f.scalarGauge g hg hgd).coord z ≠ 0 := by
    rw [Curve.scalarGauge_wronskian]
    exact mul_ne_zero (pow_ne_zero _ (hg z)) hW
  have hbase := fundamental_last_coefficient_eq_neg_deriv_div hAf hW
  have hscaled := fundamental_last_coefficient_eq_neg_deriv_div
    (fun j => by
      have hAj := hAf j
      exact hAg.mul hAj) hWg
  have hWfun :
      (fun w => wronskian n (f.scalarGauge g hg hgd).coord w) =
        (fun w => g w ^ (n + 1) * wronskian n f.coord w) := by
    funext w
    exact Curve.scalarGauge_wronskian f g hg hgd w
  have hWdiff : DifferentiableAt ℂ (fun w => wronskian n f.coord w) z :=
    (differentiable_wronskian f).differentiableAt
  have hpow :
      deriv (fun w => g w ^ (n + 1)) z =
        (n + 1 : ℂ) * g z ^ n * deriv g z := by
    have hp := (hAg.differentiableAt.hasDerivAt).pow (n + 1)
    have hfun : (g ^ (n + 1) : ℂ → ℂ) = (fun w => g w ^ (n + 1)) := by
      funext w
      rfl
    rw [← hfun]
    simpa [Nat.add_sub_cancel] using hp.deriv
  have hprod :
      deriv (fun w => g w ^ (n + 1) * wronskian n f.coord w) z =
        ((n + 1 : ℂ) * g z ^ n * deriv g z) *
            wronskian n f.coord z +
          g z ^ (n + 1) * deriv (fun w => wronskian n f.coord w) z := by
    have hp := (hAg.differentiableAt.hasDerivAt).pow (n + 1)
    have hw := hWdiff.hasDerivAt
    have hmul := hp.mul hw
    have hfunprod :
        (g ^ (n + 1) * (fun w => wronskian n f.coord w) : ℂ → ℂ) =
          (fun w => g w ^ (n + 1) * wronskian n f.coord w) := by
      funext w
      rfl
    rw [← hfunprod]
    simpa [Nat.add_sub_cancel] using hmul.deriv
  rw [hWfun] at hscaled
  have hWz := Curve.scalarGauge_wronskian f g hg hgd z
  rw [hWz] at hscaled
  rw [hscaled, hbase, hprod]
  field_simp [hW, hg z]
  ring

end
end FewInflection
