import ModifiedCartan.EntireZeroCopies

open scoped Topology BigOperators
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

/-- Copies of actual zeros lying in the closed disk, with multiplicity. -/
abbrev zeroCopiesInClosedBall (f : ℂ → ℂ) (R : ℝ) :=
  {a : entireZeroCopies f // ‖a.1‖ ≤ R}

theorem entireZeroCopies_mem_diskSupport {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) (a : entireZeroCopies f) (ha : ‖a.1‖ ≤ R) :
    a.1 ∈ diskSupport (divisor f univ) R := by
  apply mem_diskSupport_of_ne
  rw [toClosedBall_eval_within _ (by
    simpa only [mem_closedBall, dist_zero_right, abs_of_nonneg hR] using ha)]
  exact entireZeroCopies_mem_divisor_support hf a

noncomputable def zeroCopiesInClosedBallEquiv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) :
    zeroCopiesInClosedBall f R ≃
      (z : ↥(diskSupport (divisor f univ) R)) × Fin (analyticOrderAt f z.val).toNat where
  toFun a := ⟨⟨a.val.1, entireZeroCopies_mem_diskSupport hf hR a.val a.property⟩, a.val.2⟩
  invFun a := ⟨⟨a.1.val, a.2⟩, norm_le_of_mem_diskSupport hR a.1.property⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨⟨z, hz⟩, i⟩; rfl

theorem zeroCopiesInClosedBall_finite {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) : Finite (zeroCopiesInClosedBall f R) := by
  classical
  exact (zeroCopiesInClosedBallEquiv hf hR).finite_iff.mpr inferInstance

/-- The cardinality of actual repeated zero copies is exactly the
already defined divisor count. No supplied root enumeration is used. -/
theorem zeroCopiesInClosedBall_card {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) :
    (Nat.card (zeroCopiesInClosedBall f R) : ℝ) = zeroCount f R := by
  classical
  rw [Nat.card_congr (zeroCopiesInClosedBallEquiv hf hR), Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_sum]
  rw [Finset.sum_coe_sort (diskSupport (divisor f univ) R)
    (fun z : ℂ => ((analyticOrderAt f z).toNat : ℝ))]
  change (∑ z ∈ diskSupport (divisor f univ) R, ((analyticOrderAt f z).toNat : ℝ)) =
    divisorCount (divisor f univ) R
  rw [divisorCount_eq_sum hR le_rfl]
  apply Finset.sum_congr rfl
  intro z hz
  rw [if_pos (norm_le_of_mem_diskSupport hR hz), entire_divisor_eq_analyticMultiplicity hf]
  norm_cast

theorem finite_zero_copies_count_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 ≤ R) (S : Finset (entireZeroCopies f)) :
    ((S.filter (fun a => ‖a.1‖ ≤ R)).card : ℝ) ≤ zeroCount f R := by
  classical
  letI : Finite (zeroCopiesInClosedBall f R) := zeroCopiesInClosedBall_finite hf hR
  let e : ↥(S.filter (fun a => ‖a.1‖ ≤ R)) → zeroCopiesInClosedBall f R :=
    fun a => ⟨a.val, (Finset.mem_filter.mp a.property).2⟩
  have he : Function.Injective e := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : zeroCopiesInClosedBall f R => x.val) h)
  have hc : (S.filter (fun a => ‖a.1‖ ≤ R)).card ≤ Nat.card (zeroCopiesInClosedBall f R) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_le_card_of_injective e he
  rw [← zeroCopiesInClosedBall_card hf hR]
  exact_mod_cast hc

end ModifiedCartan
#print axioms ModifiedCartan.zeroCopiesInClosedBall_card
