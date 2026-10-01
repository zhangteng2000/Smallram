import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual dyadic interval containing a radius at least one. -/
noncomputable def scalarDyadicIndex (r : ℝ) : ℕ :=
  if h : 1 ≤ r then Classical.choose (exists_nat_pow_near h (by norm_num : (1 : ℝ) < 2)) else 0

theorem scalarDyadicIndex_spec {r : ℝ} (hr : 1 ≤ r) :
    (2 : ℝ) ^ scalarDyadicIndex r ≤ r ∧ r < (2 : ℝ) ^ (scalarDyadicIndex r + 1) := by
  unfold scalarDyadicIndex
  rw [dif_pos hr]
  exact Classical.choose_spec (exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2))

theorem scalarDyadicIndex_tendsto : Tendsto scalarDyadicIndex atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro N
  refine ⟨max 1 ((2 : ℝ) ^ N), fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hNr : (2 : ℝ) ^ N ≤ r := (le_max_right _ _).trans hr
  by_contra h
  have hn : scalarDyadicIndex r + 1 ≤ N := by omega
  exact (not_lt_of_ge hNr) ((scalarDyadicIndex_spec hr1).2.trans_le
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn))

noncomputable def scalarDyadicMultiplier (r : ℝ) : ℝ := r / (2 : ℝ) ^ scalarDyadicIndex r

theorem scalarDyadicMultiplier_mem {r : ℝ} (hr : 1 ≤ r) :
    scalarDyadicMultiplier r ∈ Icc (1 : ℝ) 2 := by
  have hp : 0 < (2 : ℝ) ^ scalarDyadicIndex r := pow_pos (by norm_num) _
  have hs := scalarDyadicIndex_spec hr
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using hs.1
  · apply le_of_lt
    apply (div_lt_iff₀ hp).mpr
    simpa only [pow_succ, mul_comm] using hs.2

theorem scalarDyadicMultiplier_factor (r : ℝ) :
    scalarDyadicMultiplier r * (2 : ℝ) ^ scalarDyadicIndex r = r :=
  div_mul_cancel₀ r (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))

end ModifiedCartan
#print axioms ModifiedCartan.scalarDyadicIndex_tendsto
#print axioms ModifiedCartan.scalarDyadicMultiplier_mem