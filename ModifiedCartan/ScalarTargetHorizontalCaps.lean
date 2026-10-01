import ModifiedCartan.ScalarTargetPolynomialBounds
import ModifiedCartan.ScalarPeakDisks

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Convert whole physical target segments to polynomial log caps with any
positive exponent margin. The rectangle is proved to fit the norm-control disk. -/
theorem PolynomialReplacementData.scalar_target_horizontal_caps
    {f : Curve 1} {r s : ℕ → ℝ} {C₀ A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index 1 → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f r s C₀ A L H p a η)
    (β : WithTop ℂ) {z : ℂ} {δ ε M κ C θ : ℝ} {y : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (hC : 0 ≤ C) (hε : 0 < ε) (hθ : 0 < θ)
    (hεδ : 3 * ε ≤ δ) (hK : closedBall z δ ⊆ ball (0 : ℂ) 4) (hA : κ - M ≤ A)
    (hN : ∀ᶠ ν in atTop, ∀ w ∈ closedBall z δ,
      euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j w) ≤ Real.exp (M * s ν))
    (hD : ∀ᶠ ν in atTop, y ν ∈ Icc (z.im - 2 * ε) (z.im + 2 * ε) ∧
      ∀ t ∈ Icc (z.re - ε) (z.re + ε),
        ‖scalarCurveSphere f ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) - scalarSphereValue β‖ ≤
          C * Real.exp (-κ * s ν)) :
    ∀ᶠ ν in atTop, y ν ∈ Icc (z.im - 2 * ε) (z.im + 2 * ε) ∧
      ∀ t ∈ Icc (z.re - ε) (z.re + ε),
        ‖(polynomialMatrixGauge (p ν) (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval
          (⟨t, y ν⟩ : ℂ)‖ ≤ Real.exp ((M - κ + θ) * s ν) := by
  have hβ := scalarTargetLinearSize_pos β
  have habs := constant_mul_exp_neg_le_eventually hs
    (show -(M - κ + θ) < -(M - κ) by linarith)
    (show 0 ≤ 2 * scalarTargetLinearSize β * C + scalarTargetLinearSize β by positivity)
  filter_upwards [h.jet_error, hN, hD, habs, hs.eventually_ge_atTop 0] with ν he hNν hDν haν hsν
  refine ⟨hDν.1, ?_⟩
  intro t ht
  have hzK : (⟨t, y ν⟩ : ℂ) ∈ closedBall z δ := by
    have hh := ComplexRect.box_closed_subset_closedBall z hε
      (show 0 < 2 * ε by positivity) (show (⟨t, y ν⟩ : ℂ) ∈
        (ComplexRect.box z ε (2 * ε) hε (by positivity)).closed from ⟨ht, hDν.1⟩)
    exact (closedBall_subset_closedBall (by linarith : ε + 2 * ε ≤ δ)) hh
  have herr : ∀ j, ‖(p ν j).eval (⟨t, y ν⟩ : ℂ) -
      rescaledRepresentation f (r ν) (H ν) j (⟨t, y ν⟩ : ℂ)‖ ≤ Real.exp (-A * s ν) := by
    intro j
    simpa only [iteratedDeriv_zero] using he j 0 (by omega) (⟨t, y ν⟩ : ℂ)
      ((closedBall_subset_closedBall (by norm_num : (4 : ℝ) ≤ 16)) (ball_subset_closedBall (hK hzK)))
  exact (scalarTargetPolynomial_exp_bound f β hsν hA herr (hNν _ hzK) (hDν.2 t ht)).trans
    (by simpa only [neg_neg] using haν)

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.scalar_target_horizontal_caps
