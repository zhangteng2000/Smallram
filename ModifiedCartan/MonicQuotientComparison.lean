import ModifiedCartan.PolynomialNegativeArea
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem norm_quotient_difference_le (u v p q : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    ‖u / q - v / p‖ ≤ ‖u - v‖ / ‖q‖ + ‖v‖ * ‖q - p‖ / (‖p‖ * ‖q‖) := by
  have heq : u / q - v / p = (u - v) / q + v * (p - q) / (p * q) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ ‖(u - v) / q‖ + ‖v * (p - q) / (p * q)‖ := norm_add_le _ _
    _ = _ := by rw [norm_div, norm_div, norm_mul, norm_mul, norm_sub_rev p q]

theorem norm_quotient_difference_le_of_error (u v p q : ℂ)
    {d ε V : ℝ} (hd : 0 < d) (hp : d ≤ ‖p‖) (hden : ‖q - p‖ ≤ ε)
    (hsmall : ε ≤ d / 2) (hnum : ‖u - v‖ ≤ ε) (hv : ‖v‖ ≤ V) :
    ‖u / q - v / p‖ ≤ 2 * ε / d + 2 * V * ε / d ^ 2 := by
  have hp0 : p ≠ 0 := norm_pos_iff.mp (hd.trans_le hp)
  have hq : d / 2 ≤ ‖q‖ := by
    have ht := norm_sub_norm_le p q
    rw [norm_sub_rev p q] at ht
    linarith
  have hq0 : q ≠ 0 := norm_pos_iff.mp ((half_pos hd).trans_le hq)
  have hε : 0 ≤ ε := (norm_nonneg _).trans hnum
  have hV : 0 ≤ V := (norm_nonneg _).trans hv
  calc
    _ ≤ ‖u - v‖ / ‖q‖ + ‖v‖ * ‖q - p‖ / (‖p‖ * ‖q‖) :=
      norm_quotient_difference_le u v p q hp0 hq0
    _ ≤ ε / (d / 2) + V * ε / (d * (d / 2)) := by gcongr
    _ = _ := by ring

theorem tendstoInMeasure_zero_of_exceptional_sets
    {α E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E]
    (μ : Measure α) {f : ℕ → α → E} {A : ℕ → Set α} {r : ℕ → ℝ}
    (hA : Tendsto (fun ν => μ (A ν)) atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ᶠ ν in atTop, ∀ x, x ∉ A ν → ‖f ν x‖ ≤ r ν) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hA
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hbound, hr.eventually_lt_const hε] with ν hν hrν
  apply measure_mono
  intro x hx
  by_contra hxA
  exact (lt_of_le_of_lt (hν x hxA) hrν).not_ge hx

theorem norm_quotient_difference_le_exp (u v p q : ℂ) (s B C : ℝ)
    (hp : Real.exp (-s) ≤ ‖p‖)
    (hden : ‖q - p‖ ≤ Real.exp (-B * s))
    (hnum : ‖u - v‖ ≤ Real.exp (-B * s))
    (hv : ‖v‖ ≤ Real.exp (C * s))
    (hsmall : Real.exp (-(B - 1) * s) ≤ 1 / 2) :
    ‖u / q - v / p‖ ≤
      2 * Real.exp (-(B - 1) * s) + 2 * Real.exp (-(B - C - 2) * s) := by
  have hratio : Real.exp (-B * s) / Real.exp (-s) = Real.exp (-(B - 1) * s) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have he : Real.exp (-B * s) ≤ Real.exp (-s) / 2 := by
    have h := (div_le_iff₀ (Real.exp_pos (-s))).mp (hratio.trans_le hsmall)
    linarith
  have h := norm_quotient_difference_le_of_error u v p q
    (Real.exp_pos (-s)) hp hden he hnum hv
  have hpow : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have heq : 2 * Real.exp (-B * s) / Real.exp (-s) +
      2 * Real.exp (C * s) * Real.exp (-B * s) / Real.exp (-s) ^ 2 =
      2 * Real.exp (-(B - 1) * s) + 2 * Real.exp (-(B - C - 2) * s) := by
    rw [hpow]
    calc
      _ = 2 * (Real.exp (-B * s) / Real.exp (-s)) +
          2 * (Real.exp (C * s) * Real.exp (-B * s) / Real.exp (-2 * s)) := by ring
      _ = _ := by
        rw [hratio, ← Real.exp_add, ← Real.exp_sub]
        congr 2
        congr 1
        ring
  exact h.trans_eq heq

theorem exponential_decay_of_scale {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ν => Real.exp (-a * s ν)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (hs.const_mul_atTop_of_neg (neg_lt_zero.mpr ha))

/-- The analytic comparison step of `eq:cramercomparison`, once the Taylor
and determinant estimates have supplied the displayed errors. -/
theorem monic_quotient_comparison_inMeasure
    (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    {u v Q : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {B C : ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (hB : 1 < B) (hBC : C + 2 < B)
    {K : Set ℂ} (hK : MeasurableSet K)
    (hden : ∀ᶠ ν in atTop, ∀ z ∈ K, ‖Q ν z - (P ν).eval z‖ ≤ Real.exp (-B * s ν))
    (hnum : ∀ᶠ ν in atTop, ∀ z ∈ K, ‖u ν z - v ν z‖ ≤ Real.exp (-B * s ν))
    (hv : ∀ᶠ ν in atTop, ∀ z ∈ K, ‖v ν z‖ ≤ Real.exp (C * s ν)) :
    TendstoInMeasure (volume.restrict K)
      (fun ν z => u ν z / Q ν z - v ν z / (P ν).eval z) atTop (fun _ => 0) := by
  let A : ℕ → Set ℂ := fun ν => {z | z ∉ K ∨ ‖(P ν).eval z‖ < Real.exp (-s ν)}
  have hA : Tendsto (fun ν => (volume.restrict K) (A ν)) atTop (𝓝 0) := by
    have heq (ν : ℕ) : (volume.restrict K) (A ν) =
        volume {z : ℂ | z ∈ K ∧ ‖(P ν).eval z‖ < Real.exp (-s ν)} := by
      rw [Measure.restrict_apply' hK]
      congr 1
      ext z
      simp only [A, mem_inter_iff, mem_ofPred_eq]
      tauto
    simp_rw [heq]
    exact monic_polynomial_small_value_area_tendsto_zero P hP hs hm K
  have hfirst := exponential_decay_of_scale hs (show 0 < B - 1 by linarith)
  have hsecond := exponential_decay_of_scale hs (show 0 < B - C - 2 by linarith)
  have hr : Tendsto (fun ν => 2 * Real.exp (-(B - 1) * s ν) +
      2 * Real.exp (-(B - C - 2) * s ν)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hfirst.const_mul 2).add (hsecond.const_mul 2)
  apply tendstoInMeasure_zero_of_exceptional_sets (volume.restrict K) hA hr
  filter_upwards [hden, hnum, hv, hfirst.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with ν hd hn hvν hsmall
  intro z hz
  have hgood : z ∈ K ∧ Real.exp (-s ν) ≤ ‖(P ν).eval z‖ := by
    simpa only [A, mem_ofPred_eq, not_or, not_not, not_lt] using hz
  exact norm_quotient_difference_le_exp (u ν z) (v ν z) ((P ν).eval z) (Q ν z)
    (s ν) B C hgood.2 (hd z hgood.1) (hn z hgood.1) (hvν z hgood.1) hsmall.le

theorem monic_quotient_comparison_localMeasure
    (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    {u v Q : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {B C : ℝ} {U : Set ℂ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (hB : 1 < B) (hBC : C + 2 < B)
    (hden : ∀ᶠ ν in atTop, ∀ z ∈ U, ‖Q ν z - (P ν).eval z‖ ≤ Real.exp (-B * s ν))
    (hnum : ∀ᶠ ν in atTop, ∀ z ∈ U, ‖u ν z - v ν z‖ ≤ Real.exp (-B * s ν))
    (hv : ∀ᶠ ν in atTop, ∀ z ∈ U, ‖v ν z‖ ≤ Real.exp (C * s ν)) :
    LocalMeasureConvergence U
      (fun ν z => u ν z / Q ν z - v ν z / (P ν).eval z) (fun _ => 0) := by
  intro K hK hKU
  apply monic_quotient_comparison_inMeasure P hP hs hm hB hBC hK.measurableSet
  · filter_upwards [hden] with ν hν z hz
    exact hν z (hKU hz)
  · filter_upwards [hnum] with ν hν z hz
    exact hν z (hKU hz)
  · filter_upwards [hv] with ν hν z hz
    exact hν z (hKU hz)

end ModifiedCartan
