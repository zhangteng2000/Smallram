import FewInflection.FundamentalAffineDilation
import Mathlib.Analysis.Complex.LocallyUniformLimit

open scoped BigOperators Topology
open Filter

namespace FewInflection
noncomputable section

/-- Locally uniform convergence on an open domain also controls every fixed
derivative on that domain.  The approximating functions need only be
holomorphic there, not on the entire plane. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv_of_differentiableOn
    {ι : Type*} {p : Filter ι} {F : ι → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F G p U)
    (hholF : ∀ᶠ ν in p, DifferentiableOn ℂ (F ν) U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun ν => iteratedDeriv k (F ν))
      (iteratedDeriv k G) p U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ k ih =>
      have hdiff : ∀ᶠ ν in p, DifferentiableOn ℂ (iteratedDeriv k (F ν)) U := by
        filter_upwards [hholF] with ν hν
        rw [iteratedDeriv_eq_iterate]
        exact ((hν.analyticOnNhd hU).iterated_deriv k).differentiableOn
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hdiff hU

/-! A finite Wronskian is continuous under convergence of every derivative jet.
This is the algebraic/local-analytic part of the compactness argument; no
pointwise replacement of convergence notions is used. -/
theorem tendsto_wronskian_of_tendsto_iteratedDeriv
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {F : ι → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ} {z : ℂ}
    (h : ∀ i j : Index n,
      Tendsto (fun ν => iteratedDeriv (i : ℕ) (F ν j) z) p
        (𝓝 (iteratedDeriv (i : ℕ) (G j) z))) :
    Tendsto (fun ν => wronskian n (F ν) z) p
      (𝓝 (wronskian n G z)) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (G j) z
  let Mν : ι → Matrix (Index n) (Index n) ℂ := fun ν i j =>
    iteratedDeriv (i : ℕ) (F ν j) z
  have hM : Tendsto Mν p (𝓝 M) := by
    dsimp [M, Mν]
    exact (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j)
  have hdet : Tendsto (fun ν => (Mν ν).det) p (𝓝 M.det) := by
    exact (Continuous.matrix_det (continuous_id)).continuousAt.tendsto.comp hM
  simpa [M, Mν, wronskian] using hdet

theorem tendsto_iteratedDeriv_of_locallyUniformlyOn_at
    {ι : Type*} {p : Filter ι}
    {F : ι → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hF : TendstoLocallyUniformlyOn F G p U)
    (hholF : ∀ᶠ ν in p, Differentiable ℂ (F ν)) (k : ℕ) :
    Tendsto (fun ν => iteratedDeriv k (F ν) z) p
      (𝓝 (iteratedDeriv k G z)) := by
  have hjet : ∀ m : ℕ,
      TendstoLocallyUniformlyOn
        (fun ν => iteratedDeriv m (F ν))
        (iteratedDeriv m G) p U := by
    intro m
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hF
    | succ m ihm =>
        have hdiffF : ∀ᶠ ν in p,
            DifferentiableOn ℂ (iteratedDeriv m (F ν)) U := by
          filter_upwards [hholF] with ν hν
          exact (hν.contDiff (n := m + 1)).differentiable_iteratedDeriv' m
            |>.differentiableOn
        have hderiv := ihm.deriv hdiffF hU
        simpa [iteratedDeriv_succ, Function.comp_def] using hderiv
  exact (hjet k).tendsto_at hz

/-! Local uniform convergence of holomorphic curves gives convergence of every
finite Wronskian jet at a point.  The derivative iteration is deliberately
spelled out so the required differentiability hypotheses are visible. -/
theorem tendsto_wronskian_of_locallyUniformlyOn
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {F : ι → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hF : ∀ j : Index n,
      TendstoLocallyUniformlyOn (fun ν => F ν j) (G j) p U)
    (hholF : ∀ᶠ ν in p, ∀ j : Index n, Differentiable ℂ (F ν j)) :
    Tendsto (fun ν => wronskian n (F ν) z) p
      (𝓝 (wronskian n G z)) := by
  apply tendsto_wronskian_of_tendsto_iteratedDeriv
  intro i j
  exact tendsto_iteratedDeriv_of_locallyUniformlyOn_at hU hz (hF j)
    (hholF.mono fun ν hν => hν j) (i : ℕ)

end
end FewInflection
