import FewInflection.ScalarGauge
import FewInflection.ScalarWronskian
import FewInflection.WronskianRegularity

open scoped BigOperators Topology
open Filter Asymptotics MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set Topology
namespace FewInflection
noncomputable section

theorem Curve.scalarGauge_ramification_eq
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) :
    ramification (f.scalarGauge g hg hgd) = ramification f := by
  let W : ℂ → ℂ := fun z => wronskian n f.coord z
  let P : ℂ → ℂ := fun z => g z ^ (n + 1)
  have hWdiff : Differentiable ℂ W := by
    simpa [W] using differentiable_wronskian f
  have hWmer : MeromorphicOn W Set.univ := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hWdiff).meromorphicOn
  have hPdiff : Differentiable ℂ P := by
    fun_prop
  have hPmer : MeromorphicOn P Set.univ := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hPdiff).meromorphicOn
  let hPA : AnalyticOnNhd ℂ P Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hPdiff
  have hPfinite : ∀ z, meromorphicOrderAt P z ≠ (⊤ : WithTop ℤ) := by
    intro z
    have hAz : AnalyticAt ℂ P z :=
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hPdiff) z (Set.mem_univ _)
    have hPz : P z ≠ 0 := by
      dsimp [P]
      exact pow_ne_zero _ (hg z)
    have ho : analyticOrderAt P z = 0 := hAz.analyticOrderAt_eq_zero.mpr hPz
    rw [hAz.meromorphicOrderAt_eq, ho]
    norm_num
  by_cases hWzero : ∀ z, W z = 0
  · have hscalarzero : ∀ z, wronskian n (f.scalarGauge g hg hgd).coord z = 0 := by
      intro z
      rw [Curve.scalarGauge_wronskian f g hg hgd z]
      simp [W, hWzero z]
    unfold ramification
    have hWfun : W = 0 := by
      funext z; exact hWzero z
    have hscalarfun : (fun z => wronskian n (f.scalarGauge g hg hgd).coord z) = 0 := by
      funext z; exact hscalarzero z
    simp [W, hWfun, hscalarfun]
  · obtain ⟨z₀, hz₀⟩ := not_forall.mp hWzero
    have hWfinite₀ : meromorphicOrderAt W z₀ ≠ (⊤ : WithTop ℤ) := by
      have hAz : AnalyticAt ℂ W z₀ :=
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr hWdiff) z₀ (Set.mem_univ _)
      have ho : analyticOrderAt W z₀ = 0 := hAz.analyticOrderAt_eq_zero.mpr hz₀
      rw [hAz.meromorphicOrderAt_eq, ho]
      norm_num
    have hWfinite : ∀ z, meromorphicOrderAt W z ≠ (⊤ : WithTop ℤ) := by
      intro z

      exact hWmer.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hWfinite₀
    have hmul : MeromorphicOn (fun z => P z * W z) Set.univ := by
      exact hPmer.mul hWmer
    have hdivmul :
        MeromorphicOn.divisor (fun z => P z * W z) Set.univ =
          MeromorphicOn.divisor P Set.univ + MeromorphicOn.divisor W Set.univ := by
      exact divisor_fun_mul hPmer hWmer
        (fun z hz => hPfinite z) (fun z hz => hWfinite z)
    have hdivP : MeromorphicOn.divisor P Set.univ = 0 := by
      ext z
      rw [hPA.divisor_apply (Set.mem_univ _)]
      have hAz : AnalyticAt ℂ P z := hPA z (Set.mem_univ _)
      have hPz : P z ≠ 0 := by
        dsimp [P]
        exact pow_ne_zero _ (hg z)
      simp [(hAz.analyticOrderAt_eq_zero.mpr hPz)]
    have hwr :
        (fun z => wronskian n (f.scalarGauge g hg hgd).coord z) =
          (fun z => P z * W z) := by
      funext z
      rw [Curve.scalarGauge_wronskian f g hg hgd z]
    unfold ramification
    rw [hwr, ValueDistribution.logCounting_zero, ValueDistribution.logCounting_zero]
    rw [hdivmul, hdivP, zero_add]

theorem Curve.scalarGauge_smallRamification_iff
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) :
    SmallRamification (f.scalarGauge g hg hgd) ↔ SmallRamification f := by
  have hram : ramification (f.scalarGauge g hg hgd) =ᶠ[atTop] ramification f :=
    Eventually.of_forall (fun r => congrFun
      (Curve.scalarGauge_ramification_eq f g hg hgd) r)
  have hchar := characteristic_scalarGauge_eventuallyEq f g hg hgd
  exact isLittleO_congr hram hchar

/-- A constant invertible matrix gauge preserves the zero divisor of the
Wronskian, and therefore preserves the ramification counting function. -/
theorem Curve.matrixGauge_ramification_eq
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) :
    ramification (f.matrixGauge A hA) = ramification f := by
  let W : ℂ → ℂ := fun z => wronskian n f.coord z
  let P : ℂ → ℂ := fun _ => A.det
  have hWdiff : Differentiable ℂ W := by
    simpa [W] using differentiable_wronskian f
  have hWmer : MeromorphicOn W Set.univ := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hWdiff).meromorphicOn
  have hPdiff : Differentiable ℂ P := by
    fun_prop
  have hPmer : MeromorphicOn P Set.univ := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hPdiff).meromorphicOn
  let hPA : AnalyticOnNhd ℂ P Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hPdiff
  have hPfinite : ∀ z, meromorphicOrderAt P z ≠ (⊤ : WithTop ℤ) := by
    intro z
    have hAz : AnalyticAt ℂ P z := hPA z (Set.mem_univ _)
    have hPz : P z ≠ 0 := by
      exact hA.ne_zero
    have ho : analyticOrderAt P z = 0 := hAz.analyticOrderAt_eq_zero.mpr hPz
    rw [hAz.meromorphicOrderAt_eq, ho]
    norm_num
  by_cases hWzero : ∀ z, W z = 0
  · have hscalarzero : ∀ z, wronskian n (f.matrixGauge A hA).coord z = 0 := by
      intro z
      rw [Curve.matrixGauge_wronskian f A hA z]
      simp [W, hWzero z]
    unfold ramification
    have hWfun : W = 0 := by
      funext z; exact hWzero z
    have hscalarfun :
        (fun z => wronskian n (f.matrixGauge A hA).coord z) = 0 := by
      funext z; exact hscalarzero z
    simp [W, hWfun, hscalarfun]
  · obtain ⟨z₀, hz₀⟩ := not_forall.mp hWzero
    have hWfinite₀ : meromorphicOrderAt W z₀ ≠ (⊤ : WithTop ℤ) := by
      have hAz : AnalyticAt ℂ W z₀ :=
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr hWdiff) z₀
          (Set.mem_univ _)
      have ho : analyticOrderAt W z₀ = 0 := hAz.analyticOrderAt_eq_zero.mpr hz₀
      rw [hAz.meromorphicOrderAt_eq, ho]
      norm_num
    have hWfinite : ∀ z, meromorphicOrderAt W z ≠ (⊤ : WithTop ℤ) := by
      intro z
      exact hWmer.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hWfinite₀
    have hdivmul :
        MeromorphicOn.divisor (fun z => P z * W z) Set.univ =
          MeromorphicOn.divisor P Set.univ + MeromorphicOn.divisor W Set.univ := by
      exact divisor_fun_mul hPmer hWmer
        (fun z hz => hPfinite z) (fun z hz => hWfinite z)
    have hdivP : MeromorphicOn.divisor P Set.univ = 0 := by
      ext z
      rw [hPA.divisor_apply (Set.mem_univ _)]
      have hAz : AnalyticAt ℂ P z := hPA z (Set.mem_univ _)
      have hPz : P z ≠ 0 := by
        exact hA.ne_zero
      simp [(hAz.analyticOrderAt_eq_zero.mpr hPz)]
    have hwr :
        (fun z => wronskian n (f.matrixGauge A hA).coord z) =
          (fun z => P z * W z) := by
      funext z
      rw [Curve.matrixGauge_wronskian f A hA z]
      dsimp [P, W]
      ring
    unfold ramification
    rw [hwr, ValueDistribution.logCounting_zero, ValueDistribution.logCounting_zero]
    rw [hdivmul, hdivP, zero_add]

end
end FewInflection
