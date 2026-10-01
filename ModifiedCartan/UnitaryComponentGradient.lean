import ModifiedCartan.UnitaryPolynomialCoefficients
import ModifiedCartan.NormalizedGradientEquation
import ModifiedCartan.PolynomialGradientRegularity

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual component limits from `lem:basis-at-point` satisfy the monic
weak-gradient equation in Step 1 of `prop:homogeneity`. -/
theorem ArbitraryRadiusLimitData.unitary_component_gradient_equation {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
    (j : Index n) {v : ℂ → ℝ}
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) v) :
    ∃ g : ℂ → ℂ, HasWeakComplexGradient (ball (0 : ℂ) 4) v g ∧
      ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4),
        g z ^ (n + 1) + ∑ i : Index n, d.fullCoefficient i z * g z ^ i.val = 0 := by
  let F : ℕ → Index n → ℂ → ℂ := fun ν k z =>
    (polynomialMatrixGauge (d.polynomial (ns ν)) (V ν : Matrix (Index n) (Index n) ℂ) k).eval z
  let s : ℕ → ℝ := fun ν => characteristic f (r (d.subseq (ns ν)))
  have hf (ν : ℕ) (k : Index n) : AnalyticOnNhd ℂ (F ν k) (ball 0 4) :=
    (AnalyticOnNhd.eval_polynomial (polynomialMatrixGauge (d.polynomial (ns ν))
      (V ν : Matrix (Index n) (Index n) ℂ) k)).mono (subset_univ _)
  have hn (ν : ℕ) : ∃ z ∈ ball (0 : ℂ) 4, F ν j z ≠ 0 :=
    hlim.normalizedLog_nontrivial isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩ (d.scale_pos (ns ν))
  have hs : Tendsto s atTop atTop := d.scale_tendsto.comp hns.tendsto_atTop
  have hreal := hlim.normalizedLog_real
  obtain ⟨g, hg, _⟩ := hreal.log_limit_weak_gradient isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
    (fun ν => hf ν j) hn hs
  exact ⟨g, hg, normalized_ode_weak_gradient_polynomial isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
    hf (d.unitary_polynomial_wronskian_ae hns V) hs j hn hreal hg
    (d.unitary_polynomial_coefficient_limit hns V)⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_gradient_equation
