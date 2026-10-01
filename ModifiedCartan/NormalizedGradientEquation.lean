import ModifiedCartan.NormalizedFundamentalODE

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The limit passage in manuscript `eq:normalized-polynomial-equation`
with arbitrary limiting coefficients. No polynomial equation is assumed for
the limit gradient. -/
theorem normalized_ode_weak_gradient_polynomial {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → Index n → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    {a : Index n → ℂ → ℂ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) U)
    (hW : ∀ᶠ ν in atTop, ∀ᵐ z ∂volume.restrict U, FewInflection.wronskian n (f ν) z ≠ 0)
    (hs : Tendsto s atTop atTop) (j : Index n)
    (hne : ∀ ν, ∃ b ∈ U, f ν j b ≠ 0)
    (hu : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) u)
    (hg : HasWeakComplexGradient U u g)
    (hcoeff : ∀ i : Index n, LocalMeasureConvergence U
      (fun ν z => FewInflection.fundamentalCoefficients n (f ν) z i /
        (s ν : ℂ) ^ (n + 1 - i.val)) (a i)) :
    ∀ᵐ z ∂volume.restrict U, g z ^ (n + 1) + ∑ i : Index n, a i z * g z ^ i.val = 0 := by
  let A := fun (i : Index n) ν z => FewInflection.fundamentalCoefficients n (f ν) z i /
    (s ν : ℂ) ^ (n + 1 - i.val)
  let D := fun (k : ℕ) ν z => iteratedDeriv k (f ν j) z / ((s ν : ℂ) ^ k * f ν j z)
  let Q := fun ν z => D (n + 1) ν z + ∑ i : Index n, A i ν z * D i.val ν z
  have hD (k : ℕ) : LocalMeasureConvergence U (D k) (fun z => g z ^ k) :=
    hu.iteratedDeriv_div_localMeasure hU hUc (fun ν => hf ν j) hne hs hg k
  have hQ : LocalMeasureConvergence U Q
      (fun z => g z ^ (n + 1) + ∑ i : Index n, a i z * g z ^ i.val) := by
    intro K hK hKU
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    have hAm (i : Index n) (ν : ℕ) : AEStronglyMeasurable (A i ν) (volume.restrict K) :=
      ((fundamentalCoefficient_aestronglyMeasurable (hf ν) hK.measurableSet hKU i).aemeasurable.div_const _).aestronglyMeasurable
    have hDm (k ν : ℕ) : AEStronglyMeasurable (D k ν) (volume.restrict K) :=
      normalized_iteratedDeriv_aestronglyMeasurable (hf ν j) hK.measurableSet hKU (s ν) k
    have hprod (i : Index n) : TendstoInMeasure (volume.restrict K)
        (fun ν z => A i ν z * D i.val ν z) atTop (fun z => a i z * g z ^ i.val) :=
      tendstoInMeasure_continuous_map₂ (hAm i) (hDm i.val)
        (hcoeff i K hK hKU) (hD i.val K hK hKU)
        (Φ := fun x : ℂ × ℂ => x.1 * x.2) (by fun_prop)
    have hsum := tendstoInMeasure_finsetSum Finset.univ
      (fun i _ ν => (hAm i ν).mul (hDm i.val ν)) (fun i _ => hprod i)
    exact tendstoInMeasure_continuous_map₂ (hDm (n + 1))
      (fun ν => Finset.univ.aestronglyMeasurable_fun_sum (fun i _ => (hAm i ν).mul (hDm i.val ν)))
      (hD (n + 1) K hK hKU) hsum (Φ := fun x : ℂ × ℂ => x.1 + x.2) (by fun_prop)
  have hzero : LocalMeasureConvergence U Q (fun _ => 0) := by
    intro K hK hKU
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    have hz : TendstoInMeasure (volume.restrict K) (fun (_ : ℕ) (_ : ℂ) => (0 : ℂ)) atTop (fun _ => 0) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
        (Eventually.of_forall (fun _ => tendsto_const_nhds))
    apply hz.congr' _ EventuallyEq.rfl
    filter_upwards [hW] with ν hν
    filter_upwards [hν.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU))] with z hz
    exact (normalized_fundamental_equation hz (s ν) j).symm
  exact hQ.ae_unique hU hzero

end ModifiedCartan
#print axioms ModifiedCartan.normalized_ode_weak_gradient_polynomial

