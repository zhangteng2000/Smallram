import ModifiedCartan.GenusZeroMultiplicity
import ModifiedCartan.DivisorPolynomial

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The removable extension of the quotient by the fixed genus-zero product.
Dependency for LaTeX `lem:small-order-coordinates`. -/
noncomputable def genusZeroQuotient (f : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / genusZeroProduct f) univ

theorem genusZeroQuotient_meromorphicOrderAt {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    meromorphicOrderAt (genusZeroQuotient f) z = 0 := by
  have hp := genusZeroProduct_differentiable hs
  have hq : MeromorphicOn (f / genusZeroProduct f) univ :=
    fun w _ => (hf.analyticAt w).meromorphicAt.div (hp.analyticAt w).meromorphicAt
  have he : meromorphicOrderAt (genusZeroProduct f) z = meromorphicOrderAt f z := by
    rw [(hp.analyticAt z).meromorphicOrderAt_eq, (hf.analyticAt z).meromorphicOrderAt_eq,
      genusZeroProduct_analyticOrderAt hf h0 hs]
  unfold genusZeroQuotient
  rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
    meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hp.analyticAt z).meromorphicAt,
    he]
  have hn := entire_meromorphicOrder_ne_top hf ⟨0, h0⟩ z
  lift meromorphicOrderAt f z to ℤ using hn with k hk
  simp

theorem genusZeroQuotient_differentiable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) :
    Differentiable ℂ (genusZeroQuotient f) := by
  intro z
  have hn := meromorphicNFOn_toMeromorphicNFOn (f / genusZeroProduct f) univ (mem_univ z)
  apply (hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_).differentiableAt
  exact le_of_eq (genusZeroQuotient_meromorphicOrderAt hf h0 hs z).symm

theorem genusZeroQuotient_ne_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    genusZeroQuotient f z ≠ 0 := by
  have hn := meromorphicNFOn_toMeromorphicNFOn (f / genusZeroProduct f) univ (mem_univ z)
  exact hn.meromorphicOrderAt_eq_zero_iff.mp
    (genusZeroQuotient_meromorphicOrderAt hf h0 hs z)

theorem genusZeroProduct_mul_quotient {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    genusZeroProduct f z * genusZeroQuotient f z = f z := by
  have hp := genusZeroProduct_differentiable hs
  by_cases hz : genusZeroProduct f z = 0
  · rw [hz, zero_mul, (genusZeroProduct_eq_zero_iff hf h0 hs z).mp hz]
  have hq : MeromorphicOn (f / genusZeroProduct f) univ :=
    fun w _ => (hf.analyticAt w).meromorphicAt.div (hp.analyticAt w).meromorphicAt
  have hqa := (hf.analyticAt z).div (hp.analyticAt z) hz
  have he : genusZeroQuotient f z = f z / genusZeroProduct f z := by
    unfold genusZeroQuotient
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
      toMeromorphicNFAt_eq_self.mpr hqa.meromorphicNFAt]
    rfl
  rw [he, mul_div_cancel₀ _ hz]

/-- One entire logarithm for the fixed product, with no dependence on a
subsequent growth exponent. Analytic part of LaTeX `lem:small-order-coordinates`. -/
theorem exists_genusZeroProduct_exp_factor {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ z, f z = genusZeroProduct f z * Complex.exp (G z) := by
  let : ContractibleSpace (univ : Set ℂ) :=
    (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace ⟨0, mem_univ 0⟩
  obtain ⟨G, hG, he⟩ := FewInflection.exists_analyticOnNhd_log
    (SimplyConnectedSpace.ofContractible _) isOpen_univ
    (fun z _ => (genusZeroQuotient_differentiable hf h0 hs).analyticAt z)
    (fun z _ => genusZeroQuotient_ne_zero hf h0 hs z)
  refine ⟨G, fun z => (hG z (mem_univ z)).differentiableAt, fun z => ?_⟩
  rw [he z (mem_univ z)]
  exact (genusZeroProduct_mul_quotient hf h0 hs z).symm

end ModifiedCartan
#print axioms ModifiedCartan.exists_genusZeroProduct_exp_factor
