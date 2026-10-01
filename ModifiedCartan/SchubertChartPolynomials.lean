import ModifiedCartan.SchubertChartSlots
import ModifiedCartan.DividedPowerPolynomials
import ModifiedCartan.SchubertFrameReconstruction

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- The Schubert affine chart in divided-power coordinates: unit pivot jets
    and arbitrary coefficients at the free positions. -/
def schubertChartPolynomial {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (j : Fin (n + 1)) : Polynomial ℂ :=
  complexDividedPowerPolynomial (partitionMinorOrders n τ j) +
    ∑ k : {k : ℕ // k ∈ schubertFreeOrders n τ j},
      x ⟨j, k⟩ • complexDividedPowerPolynomial k.val

theorem schubertChartPolynomial_jet {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (j : Fin (n + 1)) (k : ℕ) :
    (Polynomial.derivative^[k] (schubertChartPolynomial τ x j)).eval 0 =
      (if k = partitionMinorOrders n τ j then 1 else 0) +
      ∑ l : {l : ℕ // l ∈ schubertFreeOrders n τ j},
        x ⟨j, l⟩ * (if k = l.val then 1 else 0) := by
  have hadd (p q : Polynomial ℂ) : Polynomial.derivative^[k] (p + q) =
      Polynomial.derivative^[k] p + Polynomial.derivative^[k] q := by
    simp_rw [← Module.End.pow_apply, map_add]
  simp only [schubertChartPolynomial, hadd, Polynomial.iterate_derivative_sum,
    Polynomial.iterate_derivative_smul, Polynomial.eval_add, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, complexDividedPowerPolynomial_jet_zero, smul_eq_mul]

theorem schubertChartPolynomial_pivot_jets {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (i j : Fin (n + 1)) :
    (Polynomial.derivative^[partitionMinorOrders n τ i]
      (schubertChartPolynomial τ x j)).eval 0 = if i = j then 1 else 0 := by
  rw [schubertChartPolynomial_jet]
  have hs : (∑ l : {l : ℕ // l ∈ schubertFreeOrders n τ j},
      x ⟨j, l⟩ * (if partitionMinorOrders n τ i = l.val then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hn := (mem_schubertFreeOrders τ j l.val).mp l.property
    rw [ite_eq_right (Ne.symm (hn.2 i)), mul_zero]
  rw [hs, add_zero]
  simp only [(partitionMinorOrders_strictMono n τ).injective.eq_iff]

theorem schubertChartPolynomial_free_jets {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (j : Fin (n + 1))
    (k : {k : ℕ // k ∈ schubertFreeOrders n τ j}) :
    (Polynomial.derivative^[k.val] (schubertChartPolynomial τ x j)).eval 0 = x ⟨j, k⟩ := by
  rw [schubertChartPolynomial_jet,
    ite_eq_right (((mem_schubertFreeOrders τ j k.val).mp k.property).2 j), zero_add]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l hl hlk
    rw [ite_eq_right (fun he => hlk (Subtype.ext he.symm)), mul_zero]
  · simp

theorem schubertChartPolynomial_natDegree_le {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (j : Fin (n + 1)) :
    (schubertChartPolynomial τ x j).natDegree ≤ partitionMinorOrders n τ j := by
  unfold schubertChartPolynomial
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · exact (complexDividedPowerPolynomial_natDegree _).le
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    apply (Polynomial.natDegree_smul_le _ _).trans
    rw [complexDividedPowerPolynomial_natDegree]
    exact ((mem_schubertFreeOrders τ j k.val).mp k.property).1.le

/-- The chart has the exact Schubert degree profile for every parameter tuple.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem schubertChartPolynomial_natDegree {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) (j : Fin (n + 1)) :
    (schubertChartPolynomial τ x j).natDegree = partitionMinorOrders n τ j := by
  apply le_antisymm (schubertChartPolynomial_natDegree_le τ x j)
  apply Polynomial.le_natDegree_of_ne_zero
  intro hz
  have hj := (polynomialJet_zero_iff_coeff_zero (schubertChartPolynomial τ x j)
    (partitionMinorOrders n τ j)).mpr hz
  rw [schubertChartPolynomial_pivot_jets, ite_eq_left rfl] at hj
  exact one_ne_zero hj

theorem schubertChartPolynomial_linearIndependent {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) : LinearIndependent ℂ (schubertChartPolynomial τ x) :=
  polynomialTuple_linearIndependent_of_identity_jets _ _ 0
    (schubertChartPolynomial_pivot_jets τ x)

def schubertChartSpace {n : ℕ} (τ : YoungDiagram) (x : SchubertChartSlot n τ → ℂ) :
    Submodule ℂ (Polynomial ℂ) := Submodule.span ℂ (Set.range (schubertChartPolynomial τ x))

def schubertChartFrame {n : ℕ} (τ : YoungDiagram) (x : SchubertChartSlot n τ → ℂ) :
    PolynomialSchubertFrame n τ (schubertChartSpace τ x) where
  basis := Module.Basis.span (schubertChartPolynomial_linearIndependent τ x)
  degree_eq j := by
    change ((Module.Basis.span (schubertChartPolynomial_linearIndependent τ x)) j).val.natDegree = _
    rw [Module.Basis.coe_span_apply]
    exact schubertChartPolynomial_natDegree τ x j

theorem schubertChartFrame_polynomials {n : ℕ} (τ : YoungDiagram)
    (x : SchubertChartSlot n τ → ℂ) :
    (schubertChartFrame τ x).polynomials = schubertChartPolynomial τ x :=
  funext (Module.Basis.coe_span_apply (schubertChartPolynomial_linearIndependent τ x))

theorem schubertChartSpace_mem {n D : ℕ} (τ : YoungDiagram) (hτ : PartitionFits n τ)
    (hD : n + 1 + τ.rowLen 0 ≤ D) (x : SchubertChartSlot n τ → ℂ) :
    schubertChartSpace τ x ∈ polynomialSchubertCell n D τ :=
  ⟨hτ, hD, ⟨schubertChartFrame τ x⟩⟩

end
end ModifiedCartan

#print axioms ModifiedCartan.schubertChartSpace_mem
