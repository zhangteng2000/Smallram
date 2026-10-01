import ModifiedCartan.LogDerivativeLimit
import ModifiedCartan.CoefficientMeasurability
import ModifiedCartan.LocalMeasureUniqueness

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:normalized-peak-equation`. Total field division makes this
identity valid even at a zero of the chosen coordinate. -/
theorem normalized_fundamental_equation {n : ℕ} {f : Index n → ℂ → ℂ}
    {z : ℂ} (hW : FewInflection.wronskian n f z ≠ 0) (s : ℂ) (j : Index n) :
    iteratedDeriv (n + 1) (f j) z / (s ^ (n + 1) * f j z) +
      ∑ i : Index n, (FewInflection.fundamentalCoefficients n f z i / s ^ (n + 1 - i.val)) *
        (iteratedDeriv i.val (f j) z / (s ^ i.val * f j z)) = 0 := by
  have hterm (i : Index n) :
      (FewInflection.fundamentalCoefficients n f z i / s ^ (n + 1 - i.val)) *
        (iteratedDeriv i.val (f j) z / (s ^ i.val * f j z)) =
      (FewInflection.fundamentalCoefficients n f z i * iteratedDeriv i.val (f j) z) /
        (s ^ (n + 1) * f j z) := by
    rw [div_mul_div_comm, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.isLt)]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← add_div, FewInflection.fundamentalCoefficients_spec hW j, zero_div]

theorem normalized_iteratedDeriv_aestronglyMeasurable {U K : Set ℂ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (s : ℂ) (k : ℕ) :
    AEStronglyMeasurable (fun z => iteratedDeriv k f z / (s ^ k * f z)) (volume.restrict K) := by
  have hD : AEStronglyMeasurable (iteratedDeriv k f) (volume.restrict K) := ((analyticOnNhd_iteratedDeriv hf k).continuousOn.mono hKU).aestronglyMeasurable hK
  have hf' : AEStronglyMeasurable f (volume.restrict K) := (hf.continuousOn.mono hKU).aestronglyMeasurable hK
  exact (hD.aemeasurable.div (hf'.aemeasurable.const_mul _)).aestronglyMeasurable

/-- Passage to the limit in `eq:normalized-peak-equation`: vanishing
normalized fundamental coefficients force the logarithm limit's gradient
to vanish. The actual representation supplies the coefficient limits. -/
theorem normalized_ode_weak_gradient_zero {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → Index n → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) U)
    (hW : ∀ᶠ ν in atTop, ∀ᵐ z ∂volume.restrict U, FewInflection.wronskian n (f ν) z ≠ 0)
    (hs : Tendsto s atTop atTop) (j : Index n)
    (hne : ∀ ν, ∃ b ∈ U, f ν j b ≠ 0)
    (hu : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) u)
    (hg : HasWeakComplexGradient U u g)
    (hcoeff : ∀ i : Index n, LocalMeasureConvergence U
      (fun ν z => FewInflection.fundamentalCoefficients n (f ν) z i /
        (s ν : ℂ) ^ (n + 1 - i.val)) (fun _ => 0)) :
    g =ᵐ[volume.restrict U] (fun _ => 0) := by
  let A := fun (i : Index n) ν z => FewInflection.fundamentalCoefficients n (f ν) z i /
    (s ν : ℂ) ^ (n + 1 - i.val)
  let D := fun (k : ℕ) ν z => iteratedDeriv k (f ν j) z / ((s ν : ℂ) ^ k * f ν j z)
  have hD (k : ℕ) : LocalMeasureConvergence U (D k) (fun z => g z ^ k) :=
    hu.iteratedDeriv_div_localMeasure hU hUc (fun ν => hf ν j) hne hs hg k
  have hsum : LocalMeasureConvergence U
      (fun ν z => ∑ i : Index n, A i ν z * D i.val ν z) (fun _ => 0) := by
    intro K hK hKU
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    have hAm (i : Index n) (ν : ℕ) : AEStronglyMeasurable (A i ν) (volume.restrict K) :=
      ((fundamentalCoefficient_aestronglyMeasurable (hf ν) hK.measurableSet hKU i).aemeasurable.div_const _).aestronglyMeasurable
    have hDm (k ν : ℕ) : AEStronglyMeasurable (D k ν) (volume.restrict K) :=
      normalized_iteratedDeriv_aestronglyMeasurable (hf ν j) hK.measurableSet hKU (s ν) k
    have hprod (i : Index n) : TendstoInMeasure (volume.restrict K)
        (fun ν z => A i ν z * D i.val ν z) atTop (fun _ => 0) := by
      simpa only [zero_mul] using tendstoInMeasure_continuous_map₂ (hAm i) (hDm i.val)
        (hcoeff i K hK hKU) (hD i.val K hK hKU)
        (Φ := fun x : ℂ × ℂ => x.1 * x.2) (by fun_prop)
    simpa only [Finset.sum_const_zero, Pi.mul_apply] using! tendstoInMeasure_finsetSum Finset.univ
      (fun i _ ν => (hAm i ν).mul (hDm i.val ν)) (fun i _ => hprod i)
  have hDz : LocalMeasureConvergence U (D (n + 1)) (fun _ => 0) := by
    intro K hK hKU
    apply (hsum.neg_zero K hK hKU).congr' _ EventuallyEq.rfl
    filter_upwards [hW] with ν hν
    have hν' := hν.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU))
    filter_upwards [hν'] with z hz
    have he := normalized_fundamental_equation hz (s ν) j
    dsimp only [A, D]
    linear_combination -he
  have hpow := (hD (n + 1)).ae_unique hU hDz
  filter_upwards [hpow] with z hz
  exact eq_zero_of_pow_eq_zero hz

end ModifiedCartan
#print axioms ModifiedCartan.normalized_ode_weak_gradient_zero
