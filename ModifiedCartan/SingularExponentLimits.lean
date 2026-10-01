import ModifiedCartan.ExponentialLogComparison
import ModifiedCartan.NormComparison
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- An upper bound for finitely many exponents and a convergent zero sum
give a common subsequence with finite limits whose sum is zero. -/
theorem exists_balanced_finite_limit {n : ℕ} {x : ℕ → Index n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ᶠ ν in atTop, ∀ j, x ν j ≤ C)
    (hsum : Tendsto (fun ν => ∑ j, x ν j) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ ell : Index n → ℝ,
      (∀ j, Tendsto (fun ν => x (ns ν) j) atTop (𝓝 (ell j))) ∧ ∑ j, ell j = 0 := by
  let K : ℝ := (n + 1) * C + 1
  have hK : C ≤ K := by dsimp [K]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : ∀ᶠ ν in atTop, ∀ j, x ν j ∈ Icc (-K) K := by
    filter_upwards [hb, hsum.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))]
      with ν hν hsν j
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Index n)))
      (f := fun k => C - x ν k) (fun k _ => sub_nonneg.mpr (hν k)) (Finset.mem_univ j)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hh
    refine ⟨?_, (hν j).trans hK⟩
    dsimp only [K]
    simp only [Index, FewInflection.Index] at hh
    simp only [Nat.cast_add, Nat.cast_one] at hh
    linarith
  have hcpt : IsCompact {v : Index n → ℝ | ∀ j, v j ∈ Icc (-K) K} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨ell, _, ns, hns, hn⟩ := hcpt.tendsto_subseq' he.frequently
  have hl := tendsto_pi_nhds.mp hn
  refine ⟨ns, hns, ell, hl, ?_⟩
  have ht := tendsto_finsetSum Finset.univ (fun j _ => hl j)
  exact tendsto_nhds_unique ht (hsum.comp hns.tendsto_atTop)

/-- The product formula for positive singular lengths forces the sum
of their normalized logarithms to tend to zero at a good center. -/
theorem singular_log_sum_tendsto_zero {n : ℕ} {s w : ℕ → ℝ}
    {σ : ℕ → Index n → ℝ} (κ : ℕ)
    (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hw : ∀ ν, 0 < w ν) (hσ : ∀ ν j, 0 < σ ν j)
    (hprod : ∀ ν, (∏ j, σ ν j) = (s ν)⁻¹ ^ κ * w ν)
    (hlogw : Tendsto (fun ν => Real.log (w ν) / s ν) atTop (𝓝 0)) :
    Tendsto (fun ν => ∑ j, Real.log (σ ν j) / s ν) atTop (𝓝 0) := by
  have hlogs : Tendsto (fun ν => Real.log (s ν) / s ν) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hs
  have he (ν : ℕ) : (∑ j, Real.log (σ ν j) / s ν) =
      -(κ : ℝ) * (Real.log (s ν) / s ν) + Real.log (w ν) / s ν := by
    rw [← Finset.sum_div, ← Real.log_prod (fun j _ => (hσ ν j).ne'), hprod ν,
      Real.log_mul (pow_ne_zero _ (inv_ne_zero (hspos ν).ne')) (hw ν).ne',
      Real.log_pow, Real.log_inv]
    ring
  simp_rw [he]
  simpa only [mul_zero, zero_add] using (hlogs.const_mul (-(κ : ℝ))).add hlogw

end ModifiedCartan
#print axioms ModifiedCartan.exists_balanced_finite_limit
#print axioms ModifiedCartan.singular_log_sum_tendsto_zero
