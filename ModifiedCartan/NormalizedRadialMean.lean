import ModifiedCartan.ReplacementSubsequence

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:radial-mean`: the same scalar error works simultaneously
for every radius in the representation disk. -/
theorem PolynomialReplacementData.normalized_radial_mean {n : ℕ} {f : Curve n}
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ ν in atTop,
      ∀ R : ℝ, 0 < R → R < 64 →
        Real.circleAverage (fun z => (s ν)⁻¹ * Real.log (euclideanNorm
          (fun j => rescaledRepresentation f (t ν) (H ν) j z))) 0 R =
            characteristic f (R * t ν) / s ν + e ν := by
  obtain ⟨c, hc, hm⟩ := h.mean_identity
  refine ⟨fun ν => c ν / s ν, hc, ?_⟩
  filter_upwards [hm] with ν hν
  intro R hR hR64
  rw [show (fun z => (s ν)⁻¹ * Real.log (euclideanNorm
      (fun j => rescaledRepresentation f (t ν) (H ν) j z))) =
      (fun z => (s ν)⁻¹ • Real.log (euclideanNorm
      (fun j => rescaledRepresentation f (t ν) (H ν) j z))) from rfl,
    Real.circleAverage_fun_smul, hν R hR hR64, smul_eq_mul]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.normalized_radial_mean
