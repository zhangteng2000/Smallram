import ModifiedCartan.CanonicalCoefficients
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped Topology
open Filter MeasureTheory Set
set_option autoImplicit false
namespace ModifiedCartan

theorem fundamentalCoefficient_aestronglyMeasurable {n : ℕ} {U K : Set ℂ}
    {g : Index n → ℂ → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hK : MeasurableSet K) (hKU : K ⊆ U) (i : Index n) :
    AEStronglyMeasurable (fun z => FewInflection.fundamentalCoefficients n g z i)
      (volume.restrict K) := by
  have hN : AnalyticOnNhd ℂ (FewInflection.fundamentalNumerator n g i) U :=
    fun z hz => FewInflection.analyticAt_fundamentalNumerator (fun j => hg j z hz) i
  have hW : AnalyticOnNhd ℂ (fun z => FewInflection.wronskian n g z) U :=
    fun z hz => FewInflection.analyticAt_wronskian (fun j => hg j z hz)
  simp_rw [FewInflection.fundamentalCoefficients_eq_quotient]
  exact (((hN.continuousOn.mono hKU).aestronglyMeasurable hK).aemeasurable.div
    ((hW.continuousOn.mono hKU).aestronglyMeasurable hK).aemeasurable).aestronglyMeasurable

theorem canonicalLogDerivative_aestronglyMeasurable {n : ℕ} {U K : Set ℂ}
    {g : Index n → ℂ → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hK : MeasurableSet K) (hKU : K ⊆ U) :
    AEStronglyMeasurable (canonicalLogDerivative n g) (volume.restrict K) := by
  have hW : AnalyticOnNhd ℂ (fun z => FewInflection.wronskian n g z) U :=
    fun z hz => FewInflection.analyticAt_wronskian (fun j => hg j z hz)
  have hWm : AEMeasurable (fun z => FewInflection.wronskian n g z) (volume.restrict K) :=
    ((hW.continuousOn.mono hKU).aestronglyMeasurable hK).aemeasurable
  have hd := aemeasurable_deriv (fun w => FewInflection.wronskian n g w) (volume.restrict K)
  exact (hd.neg.div (hWm.const_mul (n + 1 : ℂ))).aestronglyMeasurable

theorem logarithmicJet_aestronglyMeasurable {a : ℂ → ℂ} {μ : Measure ℂ}
    (ha : AEStronglyMeasurable a μ) (k : ℕ) :
    AEStronglyMeasurable (logarithmicJet a k) μ := by
  induction k with
  | zero => exact aestronglyMeasurable_const
  | succ k ih =>
    exact (aestronglyMeasurable_deriv (logarithmicJet a k) μ).add (ha.mul ih)

end ModifiedCartan
#print axioms ModifiedCartan.fundamentalCoefficient_aestronglyMeasurable
#print axioms ModifiedCartan.logarithmicJet_aestronglyMeasurable
