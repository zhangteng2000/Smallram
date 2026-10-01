import FewInflection.Nevanlinna.PoissonKernelBounds
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Tactic

/-!
# Meromorphic finite singular sums

The Poisson--Jensen logarithmic-derivative argument contains finite sums of
translated reciprocal kernels.  This file records the elementary
Meromorphic and characteristic bookkeeping for those sums, using the
corresponding Mathlib inequalities rather than postulating a Jensen estimate.
-/

open scoped BigOperators ComplexConjugate Topology
open Filter Asymptotics MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set
open ValueDistribution

namespace FewInflection

/-! A translated reciprocal is meromorphic on the whole plane. -/
theorem meromorphic_sub_inv (a : ℂ) :
    Meromorphic (fun z : ℂ => (z - a)⁻¹) := by
  intro z
  have hA : AnalyticAt ℂ (fun w : ℂ => w - a) z := by
    fun_prop
  exact hA.meromorphicAt.inv

theorem meromorphic_smul_sub_inv (c a : ℂ) :
    Meromorphic (fun z : ℂ => c * (z - a)⁻¹) := by
  exact Meromorphic.mul (Meromorphic.const c) (meromorphic_sub_inv a)

theorem meromorphic_reflected_kernel (R : ℝ) (a : ℂ) :
    Meromorphic (fun z : ℂ => conj a / ((R : ℂ) ^ 2 - conj a * z)) := by
  intro z
  have hden : AnalyticAt ℂ (fun w : ℂ => (R : ℂ) ^ 2 - conj a * w) z := by
    fun_prop
  have hnum : AnalyticAt ℂ (fun _ : ℂ => conj a) z := by
    fun_prop
  exact hnum.meromorphicAt.div hden.meromorphicAt

/-! The two finite kernel families used in the representation are
    meromorphic, including the harmless multiplicity coefficients. -/
theorem meromorphic_singular_sum
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) :
    Meromorphic (fun z : ℂ => ∑ i ∈ s, c i * (z - a i)⁻¹) := by
  have hfun : (fun z : ℂ => ∑ i ∈ s, c i * (z - a i)⁻¹) =
      ∑ i ∈ s, (fun z : ℂ => c i * (z - a i)⁻¹) := by
    funext z
    simp
  rw [hfun]
  exact Meromorphic.sum (fun i hi => meromorphic_smul_sub_inv (c i) (a i))

theorem meromorphic_reflected_sum
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) (R : ℝ) :
    Meromorphic (fun z : ℂ =>
      ∑ i ∈ s, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) := by
  have hfun : (fun z : ℂ =>
      ∑ i ∈ s, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) =
      ∑ i ∈ s, (fun z : ℂ =>
        c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) := by
    funext z
    simp
  rw [hfun]
  exact Meromorphic.sum (fun i hi =>
    Meromorphic.mul (Meromorphic.const (c i)) (meromorphic_reflected_kernel R (a i)))

/-! Mathlib's finite-sum proximity bound specialized to translated reciprocal
    kernels.  The extra `log s.card` is exactly the finite-sum loss in the
    general theorem. -/
theorem proximity_singular_sum_top_le
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) :
    proximity (fun z : ℂ => ∑ i ∈ s, c i * (z - a i)⁻¹) ⊤ ≤
      ∑ i ∈ s, proximity (fun z : ℂ => c i * (z - a i)⁻¹) ⊤ +
        (fun _ => Real.log s.card) := by
  have h := proximity_sum_top_le s (fun i z => c i * (z - a i)⁻¹)
      (fun i hi => meromorphic_smul_sub_inv (c i) (a i))
  have hfun : (fun z : ℂ => ∑ i ∈ s, c i * (z - a i)⁻¹) =
      ∑ i ∈ s, (fun z : ℂ => c i * (z - a i)⁻¹) := by
    funext z
    simp
  rw [hfun]
  exact h

theorem proximity_reflected_sum_top_le
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) (R : ℝ) :
    proximity (fun z : ℂ =>
      ∑ i ∈ s, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) ⊤ ≤
      ∑ i ∈ s, proximity (fun z : ℂ =>
        c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) ⊤ +
        (fun _ => Real.log s.card) := by
  have h := proximity_sum_top_le s (fun i z =>
      c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z)))
    (fun i hi => Meromorphic.mul (Meromorphic.const (c i))
      (meromorphic_reflected_kernel R (a i)))
  have hfun : (fun z : ℂ =>
      ∑ i ∈ s, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) =
      ∑ i ∈ s, (fun z : ℂ =>
        c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) := by
    funext z
    simp
  rw [hfun]
  exact h

/-! The corresponding characteristic estimate, valid on the usual range
    `1 ≤ r` where logarithmic counting is nonnegative. -/
theorem characteristic_singular_sum_top_le
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) {r : ℝ} (hr : 1 ≤ r) :
    characteristic (fun z : ℂ => ∑ i ∈ s, c i * (z - a i)⁻¹) ⊤ r ≤
      (∑ i ∈ s, characteristic (fun z : ℂ => c i * (z - a i)⁻¹) ⊤) r +
        Real.log s.card := by
  have h := ValueDistribution.characteristic_sum_top_le s
      (fun i z => c i * (z - a i)⁻¹)
      (fun i hi => meromorphic_smul_sub_inv (c i) (a i)) hr
  have hfun : (fun z : ℂ => ∑ i ∈ s, c i * (z - a i)⁻¹) =
      ∑ i ∈ s, (fun z : ℂ => c i * (z - a i)⁻¹) := by
    funext z
    simp
  rw [hfun]
  exact h

theorem characteristic_reflected_sum_top_le
    {ι : Type*} (s : Finset ι) (a c : ι → ℂ) (R : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    characteristic (fun z : ℂ =>
      ∑ i ∈ s, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) ⊤ r ≤
      (∑ i ∈ s, characteristic (fun z : ℂ =>
        c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) ⊤) r +
        Real.log s.card := by
  have h := ValueDistribution.characteristic_sum_top_le s
      (fun i z => c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z)))
      (fun i hi => Meromorphic.mul (Meromorphic.const (c i))
        (meromorphic_reflected_kernel R (a i))) hr
  have hfun : (fun z : ℂ =>
      ∑ i ∈ s, c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) =
      ∑ i ∈ s, (fun z : ℂ =>
        c i * (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * z))) := by
    funext z
    simp
  rw [hfun]
  exact h

end FewInflection
