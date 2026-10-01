import ModifiedCartan.ArbitraryEntireModels
import ModifiedCartan.GlobalMeasureModels
import ModifiedCartan.TwoPowerDiskBound

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem measurable_canonicalCoefficient {n : ℕ} (f : Curve n) (i : Index n) :
    Measurable (canonicalCoefficient n f.coord i) := by
  have hm : Meromorphic (canonicalCoefficient n f.coord i) :=
    fun z => meromorphicAt_canonicalCoefficient (fun j => (f.holomorphic j).analyticAt z) i
  exact hm.measurable

namespace Paper

/-- LaTeX `eq:arbitrary-coefficients`, together with its exact monomial
description `eq:monomial-coefficients`. The convergence is on all of C,
and the common bound holds on closed disks for every admissible epsilon. -/
theorem eq_arbitrary_coefficients {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ ι : ℕ → ℕ, StrictMono ι ∧ ∃ a : Fin n → ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (a i) univ ∧
        LocalMeasureConvergence univ
          (fun ν z => (((r (ι ν) / characteristic f (r (ι ν))) : ℝ) : ℂ) ^
            (n + 1 - i.val) * canonicalCoefficient n f.coord i.castSucc ((r (ι ν) : ℂ) * z)) (a i) ∧
        IsWeightedMonomial ((n + 1 - i.val : ℕ) * (ρ - 1)) (a i)) ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ K : ℝ, 0 < K ∧
        ∀ R : ℝ, 0 < R → ∀ i : Fin n, ∀ z ∈ closedBall (0 : ℂ) R,
          ‖a i z‖ ≤ K * max
            (R ^ ((n + 1 - i.val : ℕ) * (ρ - 1 - ε)))
            (R ^ ((n + 1 - i.val : ℕ) * (ρ - 1 + ε))) := by
  obtain ⟨ι, hι, a, ha, hmodels⟩ :=
    arbitrary_coefficient_entire_models f hlin htrans hsmall hρ hl hu hr
  refine ⟨ι, hι, a, ?_, ?_⟩
  · intro i
    refine ⟨(ha i).1, ?_, (ha i).2.2⟩
    apply global_localMeasureConvergence_of_scale_models (ha i).1 (ha i).2.1
    intro R hR ns hns
    obtain ⟨_, _, hc⟩ := arbitrary_coefficient_relative_compactness f hlin htrans hsmall
      hρ (ε := ρ / 2) (by positivity) (by linarith) hl hu hr
    obtain ⟨σ, hσ, b, hb⟩ := hc R hR (ι ∘ ns) (hι.comp hns)
    let B : ℕ → ℂ → ℂ := fun ν z =>
      (((R * r (ι (ns (σ ν))) /
        (arbitraryScaleWeight ρ (ρ / 2) R * characteristic f (r (ι (ns (σ ν)))))) : ℝ) : ℂ) ^
          (n + 1 - i.val) * canonicalCoefficient n f.coord i.castSucc
            (((R * r (ι (ns (σ ν)))) : ℂ) * z)
    refine ⟨σ, hσ, B, b i,
      ((arbitraryScaleWeight ρ (ρ / 2) R / R : ℝ) : ℂ) ^ (n + 1 - i.val),
      ?_, (hb i).1, (hb i).2.1, ?_⟩
    · intro ν
      exact measurable_const.mul ((measurable_canonicalCoefficient f i.castSucc).comp
        (measurable_const.mul measurable_id))
    · intro ν z
      simpa only [B, Complex.ofReal_mul] using
        arbitrary_rescaling_relation (canonicalCoefficient n f.coord i.castSucc)
          (r := r (ι (ns (σ ν)))) (S := characteristic f (r (ι (ns (σ ν)))))
          hR (arbitraryScaleWeight_pos ρ (ρ / 2) hR) (n + 1 - i.val) z
  · intro ε hε hερ
    obtain ⟨K, hK, hb⟩ := hmodels ε hε hερ
    refine ⟨K, hK, ?_⟩
    intro R hR i
    obtain ⟨b, hba, hbb, hbe⟩ := hb R hR i
    exact two_power_closed_disk_bound_of_model hR (n + 1 - i.val) hba hbb hbe

/-- LaTeX `eq:monomial-coefficients`: every entire limit of the actual
scaled coefficients has the stated natural-degree monomial form. -/
theorem eq_monomial_coefficients {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {a : Fin n → ℂ → ℂ}
    (ha : ∀ i, AnalyticOnNhd ℂ (a i) univ)
    (hlim : ∀ i, LocalMeasureConvergence univ
      (fun ν z => (((r ν / characteristic f (r ν)) : ℝ) : ℂ) ^ (n + 1 - i.val) *
        canonicalCoefficient n f.coord i.castSucc ((r ν : ℂ) * z)) (a i)) :
    ∀ i, IsWeightedMonomial ((n + 1 - i.val : ℕ) * (ρ - 1)) (a i) := by
  obtain ⟨ι, hι, b, hb, _⟩ := eq_arbitrary_coefficients f hlin htrans hsmall hρ hl hu hr
  intro i
  have hae := ((hlim i).comp hι.tendsto_atTop).ae_unique isOpen_univ (hb i).2.1
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_univ (ha i).continuousOn (hb i).1.continuousOn
  have hab : a i = b i := funext (fun z => heq (mem_univ z))
  rw [hab]
  exact (hb i).2.2

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_arbitrary_coefficients
#print axioms ModifiedCartan.Paper.eq_monomial_coefficients
