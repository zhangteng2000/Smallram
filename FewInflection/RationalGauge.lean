import FewInflection.Results
import FewInflection.ScalarGauge
import FewInflection.MatrixGaugeBounds
import FewInflection.PolynomialGrowth
import FewInflection.GrowthBasics

open scoped BigOperators Topology
open Filter Asymptotics

namespace FewInflection

noncomputable section

/-! The rational normal form is explicitly a scalar gauge of a constant
matrix gauge of the monomial curve.  The characteristic is therefore
eventually unchanged by the scalar factor; the remaining matrix factor is
handled by the finite norm-equivalence bounds in `MatrixGaugeBounds`. -/

theorem RationalNormalForm.characteristic_eventuallyEq_matrixGauge_monomial
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    characteristic f =ᶠ[atTop]
      characteristic (Curve.matrixGauge (monomialCurve n) h.A h.A_invertible) := by
  rcases h.factor with ⟨g, hg, hgd, hrep⟩
  let p : Curve n := Curve.matrixGauge (monomialCurve n) h.A h.A_invertible
  let s : Curve n := Curve.scalarGauge p g hg hgd
  have hcoord : ∀ j z, f.coord j z = s.coord j z := by
    intro j z
    rw [hrep j z]
    simp [s, p, Curve.scalarGauge, Curve.matrixGauge,
      monomialCurve, monomialFamily]
  have hchar : ∀ r : ℝ, characteristic f r = characteristic s r := by
    intro r
    unfold characteristic
    have hv : f.vector = s.vector := by
      funext z j
      exact hcoord j z
    rw [hv]
  have hs := characteristic_scalarGauge_eventuallyEq p g hg hgd
  filter_upwards [hs] with r hr
  exact (hchar r).trans hr

theorem matrixGauge_monomial_logGrowthRatio_tendsto_zero
    {n : ℕ} (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det) :
    Tendsto (logGrowthRatio
      (Curve.matrixGauge (monomialCurve n) A hA)) atTop (𝓝 (0 : EReal)) := by
  let p : Curve n := Curve.matrixGauge (monomialCurve n) A hA
  let C : ℝ := Real.log (matrixGaugeBound A) +
    Real.log (matrixGaugeBound A⁻¹)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (Real.log_nonneg (one_le_matrixGaugeBound A))
      (Real.log_nonneg (one_le_matrixGaugeBound A⁻¹))
  have hupper : ∀ᶠ r : ℝ in atTop,
      characteristic p r ≤ (n : ℝ) * Real.log r + C := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have habs := characteristic_matrixGauge_abs_sub_le
      (monomialCurve n) A hA r
    have hmono := characteristic_monomialCurve_atTop (n := n) hr
    have hdiff := (abs_le.mp habs).2
    rw [hmono, Real.log_pow] at hdiff
    dsimp [p, C]
    linarith
  let D : ℝ := max 1 ((n : ℝ) + C)
  have hD : 0 < D := by
    dsimp [D]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hconst : Tendsto (fun r : ℝ => Real.log D / Real.log r)
      atTop (𝓝 0) := Real.tendsto_log_atTop.const_div_atTop _
  have hllittle := Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hll : Tendsto (fun r : ℝ => Real.log (Real.log r) / Real.log r)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using hllittle.tendsto_div_nhds_zero
  have hq : Tendsto (fun r : ℝ => Real.log (D * Real.log r) / Real.log r)
      atTop (𝓝 0) := by
    have hadd := hconst.add hll
    have heq : (fun r : ℝ => Real.log D / Real.log r +
        Real.log (Real.log r) / Real.log r) =ᶠ[atTop]
        (fun r : ℝ => Real.log (D * Real.log r) / Real.log r) := by
      filter_upwards [eventually_gt_atTop (Real.exp 1 : ℝ)] with r hr
      have hlogpos : 0 < Real.log r := by
        exact Real.log_pos (lt_trans (by norm_num) hr)
      rw [Real.log_mul (ne_of_gt hD) (ne_of_gt hlogpos)]
      ring
    simpa using hadd.congr' heq
  have hreal : Tendsto
      (fun r : ℝ => Real.log (max (characteristic p r) 1) /
        Real.log (max r 2)) atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ r : ℝ in atTop,
        0 ≤ Real.log (max (characteristic p r) 1) /
          Real.log (max r 2) := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
      have hnum : 0 ≤ Real.log (max (characteristic p r) 1) := by
        exact Real.log_nonneg (le_max_right _ _)
      have hden : 0 < Real.log (max r 2) := by
        apply Real.log_pos
        have : 2 ≤ max r 2 := le_max_right _ _
        linarith
      exact div_nonneg hnum hden.le
    have hle : ∀ᶠ r : ℝ in atTop,
        Real.log (max (characteristic p r) 1) /
            Real.log (max r 2) ≤
          Real.log (D * Real.log r) / Real.log r := by
      filter_upwards [characteristic_nonneg_eventually p, hupper,
        eventually_gt_atTop (Real.exp 1 : ℝ)] with r hpr hru hr
      have hr1 : 1 ≤ r := by
        have : 1 < Real.exp 1 := by simp
        exact le_trans (by norm_num) (le_of_lt (this.trans hr))
      have hlogpos : 0 < Real.log r :=
        Real.log_pos (lt_trans (by norm_num) hr)
      have hlogone : 1 ≤ Real.log r := by
        apply (Real.le_log_iff_exp_le (by positivity)).2
        exact le_of_lt hr
      have hnC : 0 ≤ (n : ℝ) + C := by positivity
      have hcharprod : characteristic p r ≤
          ((n : ℝ) + C) * Real.log r := by
        calc
          characteristic p r ≤ (n : ℝ) * Real.log r + C := hru
          _ ≤ (n : ℝ) * Real.log r + C * Real.log r := by
            have hCmul : C ≤ C * Real.log r := by
              calc
                C = C * 1 := by ring
                _ ≤ C * Real.log r :=
                  mul_le_mul_of_nonneg_left hlogone hC
            linarith
          _ = ((n : ℝ) + C) * Real.log r := by ring
      have hDprod : ((n : ℝ) + C) * Real.log r ≤ D * Real.log r := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlogpos.le
      have hDone : 1 ≤ D * Real.log r := by
        have hD1 : 1 ≤ D := le_max_left _ _
        nlinarith [hlogone]
      have hmax : max (characteristic p r) 1 ≤ D * Real.log r := by
        exact max_le (hcharprod.trans hDprod) hDone
      have hmaxpos : 0 < max (characteristic p r) 1 :=
        lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hprodpos : 0 < D * Real.log r := mul_pos hD hlogpos
      have hlog := (Real.strictMonoOn_log.le_iff_le hmaxpos hprodpos).2 hmax
      have hr2 : 2 ≤ r := by
        have hexp : (2 : ℝ) ≤ Real.exp 1 := by
          have h := Real.add_one_le_exp (1 : ℝ)
          norm_num at h ⊢
          exact h
        exact le_trans hexp (le_of_lt hr)
      have hden : 0 < Real.log (max r 2) := by
        rw [max_eq_left hr2]
        exact Real.log_pos (by linarith)
      rw [max_eq_left hr2]
      exact div_le_div_of_nonneg_right hlog hlogpos.le
    exact squeeze_zero' hnonneg hle hq
  exact tendsto_real_coe_ereal_zero hreal

theorem RationalNormalForm.order_eq_zero
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    order f = (0 : EReal) := by
  let p : Curve n := Curve.matrixGauge (monomialCurve n) h.A h.A_invertible
  have hchar := h.characteristic_eventuallyEq_matrixGauge_monomial
  have hlog : logGrowthRatio f =ᶠ[atTop] logGrowthRatio p := by
    filter_upwards [hchar] with r hr
    simp [logGrowthRatio, hr, p]
  have hp : Tendsto (logGrowthRatio p) atTop (𝓝 (0 : EReal)) := by
    simpa [p] using matrixGauge_monomial_logGrowthRatio_tendsto_zero
      h.A h.A_invertible
  have hf : Tendsto (logGrowthRatio f) atTop (𝓝 (0 : EReal)) := hp.congr' hlog.symm
  unfold order
  exact hf.limsup_eq

theorem RationalNormalForm.lowerOrder_eq_zero
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    lowerOrder f = (0 : EReal) := by
  let p : Curve n := Curve.matrixGauge (monomialCurve n) h.A h.A_invertible
  have hchar := h.characteristic_eventuallyEq_matrixGauge_monomial
  have hlog : logGrowthRatio f =ᶠ[atTop] logGrowthRatio p := by
    filter_upwards [hchar] with r hr
    simp [logGrowthRatio, hr, p]
  have hp : Tendsto (logGrowthRatio p) atTop (𝓝 (0 : EReal)) := by
    simpa [p] using matrixGauge_monomial_logGrowthRatio_tendsto_zero
      h.A h.A_invertible
  have hf : Tendsto (logGrowthRatio f) atTop (𝓝 (0 : EReal)) := hp.congr' hlog.symm
  unfold lowerOrder
  exact hf.liminf_eq

theorem smallOrderStatement_of_rationalNormalForm
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    SmallOrderStatement f := by
  intro _ _ _ _
  exact ⟨h, h.order_eq_zero⟩

end

end FewInflection
