import FewInflection.AnalyticLogBranch
import FewInflection.ScalarWronskian
import FewInflection.FundamentalAnalytic
import Mathlib.Analysis.Convex.Contractible

/-!
# Canonical gauge on a zero-free domain

The scalar normalizing factor is constructed from an analytic logarithm of
the Wronskian.  All analytic hypotheses and conclusions concern the given
open domain; the factor is not assumed to be entire.
-/

open scoped Topology
open Filter Set

namespace FewInflection

/-- A nowhere-zero analytic function on a simply connected open set has an
analytic inverse `m`th root, for every positive natural `m`. -/
theorem exists_analyticOnNhd_inverse_root
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H U)
    (hH0 : ∀ z ∈ U, H z ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    ∃ η : ℂ → ℂ, AnalyticOnNhd ℂ η U ∧
      (∀ z, η z ≠ 0) ∧ ∀ z ∈ U, η z ^ m * H z = 1 := by
  obtain ⟨L, hLa, hL⟩ := exists_analyticOnNhd_log hUc hUo hH hH0
  refine ⟨fun z => Complex.exp (-L z / (m : ℂ)), ?_, ?_, ?_⟩
  · intro z hz
    exact ((hLa z hz).neg.div_const).cexp
  · intro z
    exact Complex.exp_ne_zero _
  · intro z hz
    rw [← Complex.exp_nat_mul]
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    rw [mul_div_cancel₀ (-L z) hmC, ← hL z hz, ← Complex.exp_add]
    simp

/-- The top fundamental coefficient vanishes when the Wronskian is locally
the constant one.  This applies to local holomorphic frames. -/
theorem fundamental_last_coefficient_eq_zero_of_wronskian_one
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hW : (fun w => wronskian n g w) =ᶠ[𝓝 z] (fun _ => (1 : ℂ))) :
    fundamentalCoefficients n g z ⟨n, Nat.lt_succ_self n⟩ = 0 := by
  have hWz : wronskian n g z = 1 := hW.eq_of_nhds
  rw [fundamental_last_coefficient_eq_neg_deriv_div hg (by simp [hWz]),
    hW.deriv_eq]
  simp

/-- Local canonical scalar gauge: its Wronskian equals one and the
coefficient of derivative order `n` in the fundamental operator is zero. -/
theorem exists_canonical_gauge
    {n : ℕ} {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : Index n → ℂ → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hW : ∀ z ∈ U, wronskian n g z ≠ 0) :
    ∃ η : ℂ → ℂ, AnalyticOnNhd ℂ η U ∧ (∀ z, η z ≠ 0) ∧
      (∀ z ∈ U, η z ^ (n + 1) * wronskian n g z = 1) ∧
      (∀ z ∈ U, wronskian n (fun j w => η w * g j w) z = 1) ∧
      ∀ z ∈ U, fundamentalCoefficients n (fun j w => η w * g j w) z
        ⟨n, Nat.lt_succ_self n⟩ = 0 := by
  have hWa : AnalyticOnNhd ℂ (fun z => wronskian n g z) U :=
    fun z hz => analyticAt_wronskian (fun j => hg j z hz)
  obtain ⟨η, hηa, hη0, hηW⟩ :=
    exists_analyticOnNhd_inverse_root hUc hUo hWa hW (Nat.succ_ne_zero n)
  have hnormalized : ∀ z ∈ U,
      wronskian n (fun j w => η w * g j w) z = 1 := by
    intro z hz
    rw [wronskian_scalar_mul η g z (hηa z hz).contDiffAt
      (fun j => (hg j z hz).contDiffAt)]
    exact hηW z hz
  refine ⟨η, hηa, hη0, hηW, hnormalized, ?_⟩
  intro z hz
  apply fundamental_last_coefficient_eq_zero_of_wronskian_one
    (fun j => (hηa z hz).mul (hg j z hz))
  filter_upwards [hUo.mem_nhds hz] with w hw
  exact hnormalized w hw

/-- Global specialization for a curve whose Wronskian has no zeros. -/
theorem exists_global_canonical_gauge
    {n : ℕ} (f : Curve n)
    (hW : ∀ z, wronskian n f.coord z ≠ 0) :
    ∃ η : ℂ → ℂ, Differentiable ℂ η ∧ (∀ z, η z ≠ 0) ∧
      ∀ z, wronskian n (fun j w => η w * f.coord j w) z = 1 ∧
        fundamentalCoefficients n
          (fun j w => η w * f.coord j w) z
          ⟨n, Nat.lt_succ_self n⟩ = 0 := by
  letI : ContractibleSpace (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
  have hUc : IsSimplyConnected (Set.univ : Set ℂ) :=
    SimplyConnectedSpace.ofContractible _
  have hga : ∀ j : Index n, AnalyticOnNhd ℂ (f.coord j) Set.univ := by
    intro j
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
  obtain ⟨η, hηa, hη0, hηW, hnormalized, hzero⟩ :=
    exists_canonical_gauge hUc isOpen_univ hga (by
      intro z hz
      exact hW z)
  have hηd : Differentiable ℂ η :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp hηa
  refine ⟨η, hηd, hη0, ?_⟩
  intro z
  constructor
  · exact hnormalized z (Set.mem_univ z)
  · exact hzero z (Set.mem_univ z)

/-- Any two analytic inverse-root gauges on a connected zero-free domain differ
by one constant root of unity. -/
theorem inverse_root_gauges_agree_up_to_constant
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {H η₁ η₂ : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0)
    (hη₁a : AnalyticOnNhd ℂ η₁ U) (hη₂a : AnalyticOnNhd ℂ η₂ U)
    (hη₁0 : ∀ z ∈ U, η₁ z ≠ 0) (hη₂0 : ∀ z ∈ U, η₂ z ≠ 0)
    (h₁ : ∀ z ∈ U, η₁ z ^ m * H z = 1)
    (h₂ : ∀ z ∈ U, η₂ z ^ m * H z = 1) :
    ∃ c : ℂ, c ^ m = 1 ∧ ∀ z ∈ U, η₁ z = c * η₂ z := by
  let q : ℂ → ℂ := fun z => η₁ z / η₂ z
  have hq0 : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz
    exact div_ne_zero (hη₁0 z hz) (hη₂0 z hz)
  have hH0 : ∀ z ∈ U, H z ≠ 0 := by
    intro z hz hzero
    have := h₁ z hz
    simp [hzero] at this
  have hqpow : ∀ z ∈ U, q z ^ m = 1 := by
    intro z hz
    have hpow : η₁ z ^ m = η₂ z ^ m :=
      mul_right_cancel₀ (hH0 z hz) ((h₁ z hz).trans (h₂ z hz).symm)
    dsimp [q]
    rw [div_pow, hpow]
    exact (div_self (pow_ne_zero m (hη₂0 z hz)))
  have hqa : AnalyticOnNhd ℂ q U := by
    exact hη₁a.div hη₂a hη₂0
  have hqdiff : DifferentiableOn ℂ q U := hqa.differentiableOn
  have hqderiv_zero : ∀ z ∈ U, deriv q z = 0 := by
    intro z hz
    have hpowder := (hqa z hz).differentiableAt.hasDerivAt.pow m
    have hevent : (fun w => q w ^ m) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
      filter_upwards [hUo.mem_nhds hz] with w hw
      exact hqpow w hw
    have hderzero : deriv (fun w => q w ^ m) z = 0 := by
      rw [hevent.deriv_eq]
      simp
    have hcoeff : (m : ℂ) * q z ^ (m - 1) * deriv q z = 0 := by
      calc
        (m : ℂ) * q z ^ (m - 1) * deriv q z =
            deriv (fun w => q w ^ m) z := hpowder.deriv.symm
        _ = 0 := hderzero
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hfactor : (m : ℂ) * q z ^ (m - 1) ≠ 0 :=
      mul_ne_zero hmC (pow_ne_zero _ (hq0 z hz))
    exact (mul_eq_zero.mp hcoeff).resolve_left hfactor
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  have hpre : IsPreconnected U := hUc.isPathConnected.isConnected.isPreconnected
  have hconstdiff : DifferentiableOn ℂ (fun _ : ℂ => q z₀) U :=
    differentiableOn_const (q z₀)
  have hconst : Set.EqOn q (fun _ => q z₀) U := by
    apply hUo.eqOn_of_deriv_eq hpre hqdiff hconstdiff
    · intro z hz
      simp [hqderiv_zero z hz]
    · exact hz₀
    · rfl
  refine ⟨q z₀, hqpow z₀ hz₀, ?_⟩
  intro z hz
  have hratio := hconst hz
  dsimp [q] at hratio
  exact (div_eq_iff (hη₂0 z hz)).mp hratio

end FewInflection
