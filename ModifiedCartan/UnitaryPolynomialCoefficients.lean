import ModifiedCartan.ArbitraryPolynomialCoefficients
import ModifiedCartan.ScaledPolynomialJets
import ModifiedCartan.CanonicalGauge

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem polynomialMatrixGauge_fundamentalCoefficients {n : ℕ}
    (p : Index n → Polynomial ℂ) (B : Matrix (Index n) (Index n) ℂ)
    (hB : B.det ≠ 0) {z : ℂ} (hW : (FewInflection.polynomialWronskian p).eval z ≠ 0) :
    FewInflection.fundamentalCoefficients n (fun j w => (polynomialMatrixGauge p B j).eval w) z =
      FewInflection.fundamentalCoefficients n (fun j w => (p j).eval w) z := by
  have he : (fun j w => (polynomialMatrixGauge p B j).eval w) =
      (fun j w => ∑ k, (p k).eval w * B k j) := by
    funext j w
    simp only [polynomialMatrixGauge, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
  rw [he]
  apply fundamentalCoefficients_matrix (fun j => (AnalyticOnNhd.eval_polynomial (p j)) z (mem_univ z)) B hB
  rwa [← polynomialWronskian_eval_eq_wronskian]

theorem ArbitraryRadiusLimitData.unitary_polynomial_wronskian_ae {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ) :
    ∀ᶠ ν in atTop, ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4),
      FewInflection.wronskian n
        (fun j w => (polynomialMatrixGauge (d.polynomial (ns ν)) (V ν : Matrix (Index n) (Index n) ℂ) j).eval w) z ≠ 0 := by
  filter_upwards [hns.tendsto_atTop.eventually d.replacement.wronskian_nonzero] with ν hν
  filter_upwards [ae_restrict_of_ae (polynomial_eval_ne_zero_ae _ hν)] with z hz
  apply norm_ne_zero_iff.mp
  rw [← polynomialWronskian_eval_eq_wronskian, polynomialMatrixGauge_unitary_wronskian_norm]
  exact norm_ne_zero_iff.mpr hz

/-- Constant unitary changes preserve the actual coefficients used in
`eq:normalized-polynomial-equation`, hence their already constructed limits. -/
theorem ArbitraryRadiusLimitData.unitary_polynomial_coefficient_limit {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ) (i : Index n) :
    LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n
        (fun j w => (polynomialMatrixGauge (d.polynomial (ns ν)) (V ν : Matrix (Index n) (Index n) ℂ) j).eval w) z i /
          (characteristic f (r (d.subseq (ns ν))) : ℂ) ^ (n + 1 - i.val)) (d.fullCoefficient i) := by
  intro K hK hKU
  apply ((d.polynomial_coefficient_limit i).comp hns.tendsto_atTop K hK hKU).congr' _ EventuallyEq.rfl
  filter_upwards [hns.tendsto_atTop.eventually d.replacement.wronskian_nonzero] with ν hν
  filter_upwards [ae_restrict_of_ae (polynomial_eval_ne_zero_ae _ hν)] with z hz
  change FewInflection.fundamentalCoefficients n (fun j w => (d.polynomial (ns ν) j).eval w) z i / _ = _
  rw [polynomialMatrixGauge_fundamentalCoefficients (d.polynomial (ns ν))
    (V ν : Matrix (Index n) (Index n) ℂ) ((Matrix.UnitaryGroup.det_isUnit (V ν)).ne_zero) hz]

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_polynomial_coefficient_limit
