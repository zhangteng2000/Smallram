import ModifiedCartan.EventualCoefficientComparison
import ModifiedCartan.RescaledGauge

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The polynomial coefficients and the canonical coefficients are compared
using the same Taylor vectors; LaTeX `eq:polynomial-coefficients`. -/
theorem replacement_coefficient_canonical_comparison {n : ℕ} (C : ℝ)
    (g : ℕ → Index n → ℂ → ℂ) (p : ℕ → Index n → Polynomial ℂ)
    (s : ℕ → ℝ) (P : ℕ → Polynomial ℂ)
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (hd : ∀ᶠ ν in atTop,
      (∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32)) ∧ (P ν).Monic ∧
      (∀ z ∈ ball (0 : ℂ) 32, FewInflection.wronskian n (g ν) z = (P ν).eval z) ∧
      (∀ z ∈ ball (0 : ℂ) 32, euclideanNorm (fun j => g ν j z) ≤ Real.exp (C * s ν)))
    (hc : ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 12)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i -
        FewInflection.fundamentalCoefficients n (g ν) z i) (fun _ => 0)) :
    ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i /
        (s ν : ℂ) ^ (n + 1 - i.val) - canonicalCoefficient n (g ν) i z /
        (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0) := by
  have hgauge := Paper.eq_gaugecomparison_eventual C g s P hs hm hd
  intro i
  have hp := ((hc i).mono (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 12))).div_pow_scale_zero hs
    (n + 1 - i.val)
  have he := hp.add (hgauge i).neg_zero
  convert! he using 1
  · funext ν z
    ring
  · funext z
    simp

/-- The first fundamental coefficient divided by s tends to zero because
the first canonical coefficient vanishes identically. -/
theorem replacement_first_coefficient_small {n : ℕ}
    (g : ℕ → Index n → ℂ → ℂ) (p : ℕ → Index n → Polynomial ℂ) (s : ℕ → ℝ)
    (hg : ∀ᶠ ν in atTop, ∀ j, AnalyticOnNhd ℂ (g ν j) (ball 0 32))
    (hc : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z (Fin.last n) /
        (s ν : ℂ) ^ (n + 1 - (Fin.last n).val) - canonicalCoefficient n (g ν) (Fin.last n) z /
        (s ν : ℂ) ^ (n + 1 - (Fin.last n).val)) (fun _ => 0)) :
    LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z (Fin.last n) /
        (s ν : ℂ)) (fun _ => 0) := by
  intro K hK hKU
  apply (hc K hK hKU).congr' _ EventuallyEq.rfl
  filter_upwards [hg] with ν hν
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have hz32 : z ∈ ball (0 : ℂ) 32 := (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 32)) (hKU hz)
  rw [canonicalCoefficient_last_eq_zero (fun j => hν j z hz32)]
  simp

/-- Exact rescaling converts the local canonical comparison into the fixed
curve's coefficients `(t/s)^q Q_q(tz)`, as required in replacement. -/
theorem replacement_scaled_coefficient_comparison {n : ℕ} (f : Curve n)
    (p : ℕ → Index n → Polynomial ℂ) {t s : ℕ → ℝ} {H : ℕ → ℂ → ℂ}
    (ht : Tendsto t atTop atTop)
    (hH : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64))
    (hc : ∀ i, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i /
        (s ν : ℂ) ^ (n + 1 - i.val) -
          canonicalCoefficient n (rescaledRepresentation f (t ν) (H ν)) i z /
            (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0)) :
    ∀ i : Fin n, LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => FewInflection.fundamentalCoefficients n (fun j w => (p ν j).eval w) z i.castSucc /
        (s ν : ℂ) ^ (n + 1 - i.val) -
          ((t ν / s ν : ℝ) : ℂ) ^ (n + 1 - i.val) *
            canonicalCoefficient n f.coord i.castSucc ((t ν : ℂ) * z)) (fun _ => 0) := by
  intro i K hK hKU
  apply (hc i.castSucc K hK hKU).congr' _ EventuallyEq.rfl
  filter_upwards [hH, ht.eventually_gt_atTop 0] with ν hHν htν
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have hz64 : z ∈ ball (0 : ℂ) 64 := (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) (hKU hz)
  rw [Paper.eq_canonical_coefficient_identification f htν (hHν z hz64) i.castSucc]
  simp only [Fin.val_castSucc, Complex.ofReal_div, div_pow]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.replacement_scaled_coefficient_comparison
