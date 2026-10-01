import FewInflection.Results
import FewInflection.ScalarGauge
import FewInflection.GrowthBasics

open scoped Topology
open Filter Set

namespace FewInflection

noncomputable section

/-!
  Regular variation is unchanged by an eventual equality.  The only point
  that needs care is the compact-uniform quantifier in `RegularlyVarying`:
  a compact set of positive multipliers has a positive minimum, so one
  threshold controls both `r` and every `c * r` simultaneously.
-/
theorem regularlyVarying_congr_eventuallyEq
    {T U : ℝ → ℝ} {ρ : ℝ}
    (hT : RegularlyVarying T ρ)
    (hTU : T =ᶠ[atTop] U) :
    RegularlyVarying U ρ := by
  intro K hK hKpos ε hε
  rcases eventually_atTop.mp hTU with ⟨R₀, hR₀⟩
  by_cases hKne : K.Nonempty
  · obtain ⟨c₀, hc₀K, hc₀min⟩ :=
      hK.exists_isMinOn hKne continuousOn_id
    have hc₀pos : 0 < c₀ := hKpos hc₀K
    have hc₀min' : ∀ c ∈ K, c₀ ≤ c := by
      intro c hc
      simpa [IsMinOn, IsMinFilter] using (hc₀min hc)
    rcases hT K hK hKpos ε hε with ⟨RT, hRT, hbound⟩
    let R : ℝ := max (max R₀ 0) (R₀ / c₀) + 1
    have hR : 0 < R := by
      dsimp [R]
      have hmax : 0 ≤ max (max R₀ 0) (R₀ / c₀) := by
        exact le_trans (le_max_right R₀ 0) (le_max_left _ _)
      linarith
    refine ⟨max R RT, lt_max_of_lt_left hR, ?_⟩
    intro r hr c hc
    have hrR : R < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hrRT : RT < r := lt_of_le_of_lt (le_max_right _ _) hr
    have hrpos : 0 < r := by
      have hRnonneg : 0 ≤ R := le_of_lt hR
      exact lt_of_le_of_lt hRnonneg hrR
    have hRdiv : R₀ / c₀ < r := by
      have hRpart : R₀ / c₀ + 1 ≤ R := by
        dsimp [R]
        have hmax := le_max_right (max R₀ 0) (R₀ / c₀)
        linarith
      linarith
    have hR₀c₀r : R₀ < c₀ * r := by
      simpa only [mul_comm] using (div_lt_iff₀ hc₀pos).mp hRdiv
    have hc₀r_le_cr : c₀ * r ≤ c * r := by
      exact mul_le_mul_of_nonneg_right (hc₀min' c hc) (le_of_lt hrpos)
    have hR₀cr : R₀ < c * r := lt_of_lt_of_le hR₀c₀r hc₀r_le_cr
    have hR₀r : R₀ ≤ r := by
      have hR₀R : R₀ ≤ R := by
        dsimp [R]
        have hR₀max : R₀ ≤ max R₀ 0 := le_max_left _ _
        have hmax₀ : max R₀ 0 ≤ max (max R₀ 0) (R₀ / c₀) :=
          le_max_left _ _
        have hadd : max (max R₀ 0) (R₀ / c₀) ≤
            max (max R₀ 0) (R₀ / c₀) + 1 :=
          le_add_of_nonneg_right (by norm_num)
        exact le_trans hR₀max (le_trans hmax₀ hadd)
      exact le_trans hR₀R (le_of_lt hrR)
    have hEq_r : T r = U r := hR₀ r hR₀r
    have hEq_cr : T (c * r) = U (c * r) := hR₀ (c * r) (le_of_lt hR₀cr)
    have hTbound := hbound r hrRT c hc
    simpa only [hEq_r, hEq_cr] using hTbound
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    refine ⟨1, by norm_num, ?_⟩
    intro r hr c hc
    exact (hKne ⟨c, hc⟩).elim

/-! Exact positive homogeneity implies regular variation. -/
theorem regularlyVarying_of_pos_homogeneous
    {T : ℝ → ℝ} {ρ : ℝ}
    (hTpos : ∀ r, 0 < r → 0 < T r)
    (hhom : ∀ r, 0 < r → ∀ c, 0 < c →
      T (c * r) = Real.rpow c ρ * T r) :
    RegularlyVarying T ρ := by
  intro K hK hKpos ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro r hr c hc
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hcpos : 0 < c := hKpos hc
  have hquot : T (c * r) / T r = Real.rpow c ρ := by
    rw [hhom r hrpos c hcpos]
    field_simp [ne_of_gt (hTpos r hrpos)]
  rw [hquot, sub_self, abs_zero]
  exact hε

/-! The characteristic identity for a nowhere-zero scalar gauge now has its
  precise regular-variation consequence. -/
theorem Curve.scalarGauge_regularlyVarying_iff
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g) {ρ : ℝ} :
    RegularlyVarying (characteristic (f.scalarGauge g hg hgd)) ρ ↔
      RegularlyVarying (characteristic f) ρ := by
  have hchar := characteristic_scalarGauge_eventuallyEq f g hg hgd
  constructor
  · intro h
    exact regularlyVarying_congr_eventuallyEq h hchar
  · intro h
    exact regularlyVarying_congr_eventuallyEq h hchar.symm

/-! A main-conclusion certificate can be transported through the same scalar
  gauge.  The order fields use the exact eventual characteristic identity,
  while the slowly varying witness is transported pointwise on the eventual
  set. -/
def Curve.scalarGauge_mainConclusion
    {n : ℕ} (f : Curve n) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hgd : Differentiable ℂ g)
    (hmain : MainConclusion f) :
    MainConclusion (f.scalarGauge g hg hgd) := by
  have hord := Curve.scalarGauge_order_lowerOrder_eq f g hg hgd
  have hchar := characteristic_scalarGauge_eventuallyEq f g hg hgd
  refine
    { rho := hmain.rho
      order_eq_lowerOrder := by
        calc
          order (f.scalarGauge g hg hgd) = order f := hord.1
          _ = lowerOrder f := hmain.order_eq_lowerOrder
          _ = lowerOrder (f.scalarGauge g hg hgd) := hord.2.symm
      rho_eq_order := by
        calc
          order (f.scalarGauge g hg hgd) = order f := hord.1
          _ = (hmain.rho : EReal) := hmain.rho_eq_order
      rho_eq_lowerOrder := by
        calc
          lowerOrder (f.scalarGauge g hg hgd) = lowerOrder f := hord.2
          _ = (hmain.rho : EReal) := hmain.rho_eq_lowerOrder
      admissible := hmain.admissible
      regularVariation :=
        (Curve.scalarGauge_regularlyVarying_iff f g hg hgd).2
          hmain.regularVariation
      slowlyVarying_factor := by
        rcases hmain.slowlyVarying_factor with ⟨ℓ, hℓ, hEq⟩
        refine ⟨ℓ, hℓ, ?_⟩
        filter_upwards [hchar, hEq] with r hchar_r hEq_r
        exact hchar_r.trans hEq_r }

end

end FewInflection
