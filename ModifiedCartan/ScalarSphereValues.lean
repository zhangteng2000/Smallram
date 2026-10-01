import ModifiedCartan.ScalarSphereProjection
import Mathlib.Topology.Sequences

open scoped Topology ComplexConjugate
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Explicit compact coordinates for the scalar target, including infinity.
Auxiliary construction for LaTeX `thm:A` (b). -/
def scalarSphereValue (a : WithTop ℂ) : ℂ × ℂ :=
  a.recTopCoe (0, 0) (fun z => scalarSphereProjection 1 z)

theorem scalarSphereValue_top : scalarSphereValue ⊤ = (0, 0) := rfl

theorem scalarSphereValue_coe (a : ℂ) :
    scalarSphereValue (a : WithTop ℂ) =
      (conj a / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ), (1 : ℂ) / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)) := by
  change scalarSphereProjection 1 a = _
  simp only [scalarSphereProjection, map_one, one_mul, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_add, Complex.ofReal_one]

def scalarSphereImage : Set (ℂ × ℂ) :=
  {v | v.2.im = 0 ∧ 0 ≤ v.2.re ∧ v.2.re ≤ 1 ∧ ‖v.1‖ ^ 2 = v.2.re * (1 - v.2.re)}

theorem scalarSphereValue_mem (a : WithTop ℂ) : scalarSphereValue a ∈ scalarSphereImage := by
  induction a using WithTop.recTopCoe with
  | top => simp [scalarSphereValue_top, scalarSphereImage]
  | coe a =>
    have hS : 0 < 1 + ‖a‖ ^ 2 := by positivity
    have hne : 1 + ‖a‖ ^ 2 ≠ 0 := hS.ne'
    rw [scalarSphereValue_coe]
    change (1 / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)).im = 0 ∧
      0 ≤ (1 / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)).re ∧
      (1 / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)).re ≤ 1 ∧ _
    have hr : (1 / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)) = ((1 / (1 + ‖a‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hr, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, by positivity, (div_le_one hS).mpr (by nlinarith [sq_nonneg ‖a‖]), ?_⟩
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
    field_simp
    ring

theorem scalarSphereImage_subset_ball : scalarSphereImage ⊆ closedBall (0 : ℂ × ℂ) 1 := by
  intro v hv
  rcases hv with ⟨hi, h0, h1, hsq⟩
  have hre : (v.2.re : ℂ) = v.2 := by
    apply Complex.ext <;> simp [hi]
  have hn2 : ‖v.2‖ ≤ 1 := by
    rw [← hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hn1 : ‖v.1‖ ≤ 1 := by
    nlinarith [sq_nonneg v.2.re, norm_nonneg v.1]
  simpa only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro hn1 hn2

theorem scalarSphereImage_isCompact : IsCompact scalarSphereImage := by
  have hclosed : IsClosed scalarSphereImage := by
    have h0 : IsClosed {v : ℂ × ℂ | v.2.im = 0} := isClosed_eq (by fun_prop) continuous_const
    have h1 : IsClosed {v : ℂ × ℂ | 0 ≤ v.2.re} := isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {v : ℂ × ℂ | v.2.re ≤ 1} := isClosed_le (by fun_prop) continuous_const
    have h3 : IsClosed {v : ℂ × ℂ | ‖v.1‖ ^ 2 = v.2.re * (1 - v.2.re)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact h0.inter (h1.inter (h2.inter h3))
  exact isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, isBounded_closedBall.subset scalarSphereImage_subset_ball⟩

theorem scalarSphereImage_eq_range : scalarSphereImage = range scalarSphereValue := by
  apply Subset.antisymm
  · intro v hv
    rcases hv with ⟨hi, h0, h1, hsq⟩
    have hre : (v.2.re : ℂ) = v.2 := by
      apply Complex.ext <;> simp [hi]
    by_cases hz : v.2.re = 0
    · have hv2 : v.2 = 0 := by rw [← hre, hz, Complex.ofReal_zero]
      have hv1 : v.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.1])
      exact ⟨⊤, by rw [scalarSphereValue_top]; exact Prod.ext hv1.symm hv2.symm⟩
    · have hp : 0 < v.2.re := lt_of_le_of_ne h0 (Ne.symm hz)
      let a : ℂ := conj v.1 / (v.2.re : ℂ)
      have hnorm : ‖a‖ ^ 2 = ‖v.1‖ ^ 2 / v.2.re ^ 2 := by
        simp only [a, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hp, div_pow]
      have henergy : 1 + ‖a‖ ^ 2 = 1 / v.2.re := by
        rw [hnorm, hsq]
        field_simp
        ring
      have hnz : (v.2.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      refine ⟨(a : WithTop ℂ), ?_⟩
      rw [scalarSphereValue_coe, henergy, Complex.ofReal_div, Complex.ofReal_one]
      apply Prod.ext
      · change conj a / (1 / (v.2.re : ℂ)) = v.1
        simp only [a, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
        field_simp
      · change 1 / (1 / (v.2.re : ℂ)) = v.2
        rw [one_div_one_div, hre]
  · rintro v ⟨a, rfl⟩
    exact scalarSphereValue_mem a

theorem scalarSphereValue_injective : Function.Injective scalarSphereValue := by
  intro a b hab
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => rfl
    | coe b =>
      have hs := congrArg Prod.snd hab
      rw [scalarSphereValue_top, scalarSphereValue_coe] at hs
      have hn : (1 : ℂ) / ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        apply div_ne_zero one_ne_zero
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      exact (hn hs.symm).elim
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top =>
      have hs := congrArg Prod.snd hab
      rw [scalarSphereValue_top, scalarSphereValue_coe] at hs
      have hn : (1 : ℂ) / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        apply div_ne_zero one_ne_zero
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      exact (hn hs).elim
    | coe b =>
      have hs := congrArg (fun v : ℂ × ℂ => conj (v.1 / v.2)) hab
      rw [scalarSphereValue_coe, scalarSphereValue_coe] at hs
      have ha : ((1 + ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have hb : ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      dsimp only at hs
      simp only [div_div_div_cancel_right₀ ha, div_div_div_cancel_right₀ hb, div_one,
        Complex.conj_conj] at hs
      exact congrArg (fun z : ℂ => (z : WithTop ℂ)) hs

theorem scalarSphereValue_tendsto_subseq (a : ℕ → WithTop ℂ) :
    ∃ b : WithTop ℂ, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun n => scalarSphereValue (a (ns n))) atTop (𝓝 (scalarSphereValue b)) := by
  obtain ⟨v, hv, ns, hns, ht⟩ := scalarSphereImage_isCompact.tendsto_subseq
    (fun n => scalarSphereValue_mem (a n))
  rw [scalarSphereImage_eq_range] at hv
  obtain ⟨b, rfl⟩ := hv
  exact ⟨b, ns, hns, ht⟩

theorem scalarSphereProjection_eq_coe_value {q : ℂ} (hq : q ≠ 0) (p : ℂ) :
    scalarSphereProjection q p = scalarSphereValue ((p / q : ℂ) : WithTop ℂ) := by
  have h := scalarSphereProjection_mul (inv_ne_zero hq) q p
  rw [inv_mul_cancel₀ hq] at h
  change scalarSphereProjection q p = scalarSphereProjection 1 (p / q)
  simpa only [div_eq_mul_inv, mul_comm] using h.symm

theorem scalarSphereProjection_mem (q p : ℂ) : scalarSphereProjection q p ∈ scalarSphereImage := by
  by_cases hq : q = 0
  · simp only [hq, scalarSphereProjection, zero_mul, zero_add, zero_div]
    exact scalarSphereValue_mem ⊤
  · rw [scalarSphereProjection_eq_coe_value hq p]
    exact scalarSphereValue_mem _
end
end ModifiedCartan
#print axioms ModifiedCartan.scalarSphereImage_eq_range
#print axioms ModifiedCartan.scalarSphereValue_injective
#print axioms ModifiedCartan.scalarSphereValue_tendsto_subseq

