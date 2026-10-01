import ModifiedCartan.NormComparison
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Joint multiplier/base-radius quotient of LaTeX `eq:strong-indices`.
The filter atTop on the product is the joint, not iterated, limit. -/
def growthScaleRatio (T : ℝ → ℝ) (p : ℝ) (xt : ℝ × ℝ) : EReal :=
  (T (xt.1 * xt.2) / (xt.1 ^ p * T xt.2) : ℝ)

/-- LaTeX `eq:strong-indices`, upper Drasin--Shea index. -/
def strongUpperIndex (T : ℝ → ℝ) : EReal :=
  sSup ((fun p : ℝ => (p : EReal)) ''
    {p | limsup (growthScaleRatio T p) atTop = ⊤})

/-- LaTeX `eq:strong-indices`, lower Drasin--Shea index. -/
def strongLowerIndex (T : ℝ → ℝ) : EReal :=
  sInf ((fun p : ℝ => (p : EReal)) ''
    {p | liminf (growthScaleRatio T p) atTop = 0})

theorem growthScaleRatio_eventually_nonneg (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (p : ℝ) :
    ∀ᶠ xt : ℝ × ℝ in atTop, 0 ≤ growthScaleRatio T p xt := by
  filter_upwards [eventually_ge_atTop ((1, 1) : ℝ × ℝ)] with xt hxt
  have hx : 0 < xt.1 := lt_of_lt_of_le zero_lt_one hxt.1
  have ht : 0 < xt.2 := lt_of_lt_of_le zero_lt_one hxt.2
  change (0 : EReal) ≤ (T (xt.1 * xt.2) / (xt.1 ^ p * T xt.2) : ℝ)
  exact_mod_cast div_nonneg (hT _ (mul_pos hx ht)).le
    (mul_pos (Real.rpow_pos_of_pos hx p) (hT _ ht)).le

theorem strongUpperIndex_uniform_upper (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p : ℝ}
    (hp : strongUpperIndex T < (p : EReal)) :
    ∃ C X r0 : ℝ, 0 < C ∧ 1 ≤ X ∧ 1 ≤ r0 ∧
      ∀ x r, X ≤ x → r0 ≤ r → T (x * r) ≤ C * x ^ p * T r := by
  have hne : limsup (growthScaleRatio T p) atTop ≠ ⊤ := by
    intro he
    have hmem : (p : EReal) ∈ ((fun q : ℝ => (q : EReal)) ''
        {q | limsup (growthScaleRatio T q) atTop = ⊤}) := ⟨p, he, rfl⟩
    exact (not_le_of_gt hp) (le_sSup hmem)
  obtain ⟨C, hC, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hne)
  have he : ∀ᶠ xt : ℝ × ℝ in atTop,
      T (xt.1 * xt.2) / (xt.1 ^ p * T xt.2) < C := by
    filter_upwards [eventually_lt_of_limsup_lt hC] with xt hxt
    dsimp only [growthScaleRatio] at hxt
    exact_mod_cast hxt
  obtain ⟨b, hb⟩ := eventually_atTop.mp he
  refine ⟨max C 1, max b.1 1, max b.2 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_max_right _ _, le_max_right _ _, ?_⟩
  intro x r hx hr
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hx)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hr)
  have hq := hb (x, r) ⟨(le_max_left _ _).trans hx, (le_max_left _ _).trans hr⟩
  have hq' : T (x * r) / (x ^ p * T r) ≤ max C 1 := hq.le.trans (le_max_left _ _)
  have hd := mul_pos (Real.rpow_pos_of_pos hx0 p) (hT r hr0)
  simpa only [mul_assoc] using (div_le_iff₀ hd).mp hq'

theorem strongLowerIndex_uniform_lower (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p : ℝ}
    (hp : (p : EReal) < strongLowerIndex T) :
    ∃ c X r0 : ℝ, 0 < c ∧ 1 ≤ X ∧ 1 ≤ r0 ∧
      ∀ x r, X ≤ x → r0 ≤ r → c * x ^ p * T r ≤ T (x * r) := by
  have hne : liminf (growthScaleRatio T p) atTop ≠ 0 := by
    intro he
    have hmem : (p : EReal) ∈ ((fun q : ℝ => (q : EReal)) ''
        {q | liminf (growthScaleRatio T q) atTop = 0}) := ⟨p, he, rfl⟩
    exact (not_le_of_gt hp) (sInf_le hmem)
  have hnonneg : (0 : EReal) ≤ liminf (growthScaleRatio T p) atTop :=
    le_liminf_of_le (h := growthScaleRatio_eventually_nonneg T hT p)
  have hpos : (0 : EReal) < liminf (growthScaleRatio T p) atTop := by
    rcases eq_or_lt_of_le hnonneg with he | he
    · exact False.elim (hne he.symm)
    · exact he
  obtain ⟨c, hc, hcl⟩ := EReal.exists_between_coe_real hpos
  have hc0 : 0 < c := by exact_mod_cast hc
  have he : ∀ᶠ xt : ℝ × ℝ in atTop,
      c < T (xt.1 * xt.2) / (xt.1 ^ p * T xt.2) := by
    filter_upwards [eventually_lt_of_lt_liminf hcl] with xt hxt
    dsimp only [growthScaleRatio] at hxt
    exact_mod_cast hxt
  obtain ⟨b, hb⟩ := eventually_atTop.mp he
  refine ⟨c, max b.1 1, max b.2 1, hc0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro x r hx hr
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hx)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hr)
  have hq := hb (x, r) ⟨(le_max_left _ _).trans hx, (le_max_left _ _).trans hr⟩
  have hd := mul_pos (Real.rpow_pos_of_pos hx0 p) (hT r hr0)
  simpa only [mul_assoc] using (le_div_iff₀ hd).mp hq.le

end
end ModifiedCartan
#print axioms ModifiedCartan.strongUpperIndex_uniform_upper
#print axioms ModifiedCartan.strongLowerIndex_uniform_lower
