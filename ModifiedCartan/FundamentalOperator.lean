import ModifiedCartan.NormComparison
import FewInflection.FundamentalAnalytic
import FewInflection.CanonicalLocalGauge

open scoped BigOperators Topology
open Filter Set

namespace ModifiedCartan

/-- Monic differential equation, interpreted as an equality of meromorphic
functions. Index `i` is the derivative order; paper index `q` is `n+1-i`. -/
def Annihilates {n : ℕ} (U : Set ℂ) (g : Index n → ℂ → ℂ)
    (b : Index n → ℂ → ℂ) : Prop :=
  ∀ j, (fun z => iteratedDeriv (n + 1) (g j) z +
    ∑ i, b i z * iteratedDeriv (i : ℕ) (g j) z) =ᶠ[codiscreteWithin U] 0

theorem wronskian_nonzero_codiscreteWithin {n : ℕ} {U : Set ℂ}
    (hUc : IsConnected U) {g : Index n → ℂ → ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hW : ∃ z ∈ U, FewInflection.wronskian n g z ≠ 0) :
    ∀ᶠ z in codiscreteWithin U, FewInflection.wronskian n g z ≠ 0 := by
  obtain ⟨z, hz, hWz⟩ := hW
  have hWa : AnalyticOnNhd ℂ (fun z => FewInflection.wronskian n g z) U :=
    fun w hw => FewInflection.analyticAt_wronskian (fun j => hg j w hw)
  exact hWa.preimage_zero_mem_codiscreteWithin hWz hz hUc

theorem fundamentalCoefficients_annihilate {n : ℕ} {U : Set ℂ}
    {g : Index n → ℂ → ℂ}
    (hW : ∀ᶠ z in codiscreteWithin U, FewInflection.wronskian n g z ≠ 0) :
    Annihilates U g (fun i z => FewInflection.fundamentalCoefficients n g z i) := by
  intro j
  filter_upwards [hW] with z hz
  exact FewInflection.fundamentalCoefficients_spec hz j

theorem annihilator_unique_codiscreteWithin {n : ℕ} {U : Set ℂ}
    {g : Index n → ℂ → ℂ} {b : Index n → ℂ → ℂ}
    (hW : ∀ᶠ z in codiscreteWithin U, FewInflection.wronskian n g z ≠ 0)
    (hb : Annihilates U g b) :
    ∀ i, b i =ᶠ[codiscreteWithin U]
      (fun z => FewInflection.fundamentalCoefficients n g z i) := by
  have hall : ∀ᶠ z in codiscreteWithin U, ∀ j,
      iteratedDeriv (n + 1) (g j) z +
        ∑ i, b i z * iteratedDeriv (i : ℕ) (g j) z = 0 :=
    Filter.eventually_all.mpr hb
  intro i
  filter_upwards [hW, hall] with z hWz hz
  exact congrFun (FewInflection.fundamentalCoefficients_unique hWz hz) i

namespace Paper

/-- LaTeX label `lem:fundamental-operator`.
Uniqueness is codiscrete equality, the equality of meromorphic functions;
values arbitrarily assigned at poles are not part of that equality. -/
theorem lem_fundamental_operator {n : ℕ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U) {g : Index n → ℂ → ℂ}
    (hg : ∀ j, DifferentiableOn ℂ (g j) U)
    (hW : ∃ z ∈ U, FewInflection.wronskian n g z ≠ 0) :
    ∃ b : Index n → ℂ → ℂ,
      (∀ i, MeromorphicOn (b i) U) ∧ Annihilates U g b ∧
      (∀ i z, z ∈ U → FewInflection.wronskian n g z ≠ 0 → AnalyticAt ℂ (b i) z) ∧
      (b (Fin.last n) =ᶠ[codiscreteWithin U]
        (fun z => -deriv (fun w => FewInflection.wronskian n g w) z /
          FewInflection.wronskian n g z)) ∧
      ∀ c : Index n → ℂ → ℂ, (∀ i, MeromorphicOn (c i) U) →
        Annihilates U g c → ∀ i, c i =ᶠ[codiscreteWithin U] b i := by
  have hga : ∀ j, AnalyticOnNhd ℂ (g j) U := fun j => (hg j).analyticOnNhd hUo
  have hWc := wronskian_nonzero_codiscreteWithin hUc hga hW
  refine ⟨fun i z => FewInflection.fundamentalCoefficients n g z i,
    ?_, fundamentalCoefficients_annihilate hWc, ?_, ?_, ?_⟩
  · intro i z hz
    exact FewInflection.meromorphicAt_fundamentalCoefficients (fun j => hga j z hz) i
  · intro i z hz hWz
    exact FewInflection.analyticAt_fundamentalCoefficients (fun j => hga j z hz) hWz i
  · filter_upwards [hWc, self_mem_codiscreteWithin U] with z hWz hz
    exact FewInflection.fundamental_last_coefficient_eq_neg_deriv_div
      (fun j => hga j z hz) hWz
  · intro c _ hc
    exact annihilator_unique_codiscreteWithin hWc hc

end Paper

theorem fundamentalCoefficients_congr_nhds {n : ℕ} {g h : Index n → ℂ → ℂ} {z : ℂ}
    (hgh : ∀ j, g j =ᶠ[𝓝 z] h j) :
    FewInflection.fundamentalCoefficients n g z =
      FewInflection.fundamentalCoefficients n h z := by
  have hjet (m : ℕ) (j : Index n) : iteratedDeriv m (g j) z = iteratedDeriv m (h j) z :=
    Filter.EventuallyEq.iteratedDeriv_eq m (hgh j)
  funext i
  simp only [FewInflection.fundamentalCoefficients_eq_quotient,
    FewInflection.fundamentalNumerator, FewInflection.wronskian, hjet]

/-- Branch independence part of LaTeX label `lem:canonical-gauge`.
The remaining global continuation and transformation statements are separate. -/
theorem canonical_gauge_coefficients_independent {n : ℕ} {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : Index n → ℂ → ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) {η₁ η₂ : ℂ → ℂ}
    (hη₁a : AnalyticOnNhd ℂ η₁ U) (hη₂a : AnalyticOnNhd ℂ η₂ U)
    (hη₁0 : ∀ z ∈ U, η₁ z ≠ 0) (hη₂0 : ∀ z ∈ U, η₂ z ≠ 0)
    (h₁ : ∀ z ∈ U, η₁ z ^ (n + 1) * FewInflection.wronskian n g z = 1)
    (h₂ : ∀ z ∈ U, η₂ z ^ (n + 1) * FewInflection.wronskian n g z = 1) :
    ∀ z ∈ U,
      FewInflection.fundamentalCoefficients n (fun j w => η₁ w * g j w) z =
        FewInflection.fundamentalCoefficients n (fun j w => η₂ w * g j w) z := by
  obtain ⟨c, hc, heq⟩ := FewInflection.inverse_root_gauges_agree_up_to_constant
    hUc hUo (Nat.succ_ne_zero n) hη₁a hη₂a hη₁0 hη₂0 h₁ h₂
  have hc0 : c ≠ 0 := by
    intro hc0
    simp [hc0] at hc
  intro z hz
  have hlocal : ∀ j : Index n,
      (fun w => η₁ w * g j w) =ᶠ[𝓝 z] (fun w => c * (η₂ w * g j w)) := by
    intro j
    filter_upwards [hUo.mem_nhds hz] with w hw
    rw [heq w hw, mul_assoc]
  rw [fundamentalCoefficients_congr_nhds hlocal]
  have hW₂ : FewInflection.wronskian n (fun j w => η₂ w * g j w) z ≠ 0 := by
    rw [FewInflection.wronskian_scalar_mul η₂ g z (hη₂a z hz).contDiffAt
      (fun j => (hg j z hz).contDiffAt), h₂ z hz]
    exact one_ne_zero
  exact FewInflection.fundamentalCoefficients_const_mul
    (fun j => (hη₂a z hz).mul (hg j z hz)) hc0 hW₂

end ModifiedCartan

