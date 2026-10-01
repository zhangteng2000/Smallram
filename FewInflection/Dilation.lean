import FewInflection.Definitions

open scoped BigOperators Topology
namespace FewInflection
noncomputable section

private theorem curve_eq_of_coord_eq
    {n : ℕ} {f g : Curve n} (hcoord : f.coord = g.coord) : f = g := by
  cases f with
  | mk fc fh fr =>
    cases g with
    | mk gc gh gr =>
      simp_all

/-- Precomposition of a curve by the dilation `z ↦ t z`. -/
def Curve.dilate {n : ℕ} (f : Curve n) (t : ℂ) : Curve n where
  coord := fun j z => f.coord j (t * z)
  holomorphic := by
    intro j
    exact (f.holomorphic j).comp (by fun_prop)
  reduced := by
    intro z
    rcases f.reduced (t * z) with ⟨j, hj⟩
    exact ⟨j, hj⟩

lemma iteratedDeriv_dilate
    {n : ℕ} (f : Curve n) (t : ℂ) (i : Index n) (j : Index n) (z : ℂ) :
    iteratedDeriv (i : ℕ) (fun x => f.coord j (t * x)) z =
      t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (t * z) := by
  have hcomp := iteratedDeriv_comp_const_mul
    ((f.holomorphic j).contDiff (n := (i : ℕ))) t
  exact congrFun hcomp z

/-- Wronskian transformation under a constant dilation. -/
theorem wronskian_dilate
    {n : ℕ} (f : Curve n) (t z : ℂ) :
    wronskian n (f.dilate t).coord z =
      t ^ (∑ i : Index n, (i : ℕ)) * wronskian n f.coord (t * z) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) =>
      iteratedDeriv (i : ℕ) (f.coord j) (t * z)
  let D : Matrix (Index n) (Index n) ℂ :=
    Matrix.diagonal (fun i : Index n => t ^ (i : ℕ))
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (i : ℕ) ((f.dilate t).coord j) z) =
        D * M := by
    funext i j
    rw [Matrix.diagonal_mul]
    dsimp [D, M, Curve.dilate]
    exact iteratedDeriv_dilate f t i j z
  calc
    wronskian n (f.dilate t).coord z = (D * M).det := by
      simp only [wronskian, hM]
    _ = D.det * M.det := Matrix.det_mul _ _
    _ = (∏ i : Index n, t ^ (i : ℕ)) * wronskian n f.coord (t * z) := by
      rw [Matrix.det_diagonal]
      rfl
    _ = t ^ (∑ i : Index n, (i : ℕ)) * wronskian n f.coord (t * z) := by
      rw [Finset.prod_pow_eq_pow_sum]

/-- Nonzero precomposition preserves linear nondegeneracy. -/
theorem Curve.dilate_linearlyNonDegenerate
    {n : ℕ} (f : Curve n) (t : ℂ) (ht : t ≠ 0)
    (hlin : f.linearlyNonDegenerate) :
    (f.dilate t).linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate at hlin ⊢
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro c hc j
  have hrel : (∑ i : Index n, c i • f.coord i) = 0 := by
    funext w
    obtain ⟨z, hz⟩ : ∃ z : ℂ, t * z = w := by
      refine ⟨w / t, ?_⟩
      field_simp
    have hcz := congrFun hc z
    have hsum :
        (∑ i : Index n, c i • f.coord i) w =
          ∑ i : Index n, c i • f.coord i w := by
      simp [Finset.sum_apply]
    rw [hsum, ← hz]
    simpa [Curve.dilate, Finset.sum_apply] using hcz
  exact hlin c hrel j

/-- Nonzero precomposition also preserves the polynomial-versus-transcendental
alternative.  The inverse scale is absorbed into the polynomial variable. -/
theorem Curve.dilate_transcendental
    {n : ℕ} (f : Curve n) (t : ℂ) (ht : t ≠ 0)
    (htrans : f.Transcendental) :
    (f.dilate t).Transcendental := by
  intro hrep_dilate
  apply htrans
  rcases hrep_dilate with ⟨p, g, hg, hgd, hrep⟩
  let q : Polynomial ℂ := Polynomial.C (t⁻¹) * Polynomial.X
  refine ⟨fun j => (p j).comp q, (fun w => g (t⁻¹ * w)), ?_, ?_, ?_⟩
  · intro w
    exact hg (t⁻¹ * w)
  · exact hgd.comp (by fun_prop)
  · intro j w
    have hrep' := hrep j (t⁻¹ * w)
    have htw : t * (t⁻¹ * w) = w := by
      field_simp
    rw [show (f.dilate t).coord j (t⁻¹ * w) =
      f.coord j (t * (t⁻¹ * w)) by rfl, htw] at hrep'
    have hqeval : (q.eval w) = t⁻¹ * w := by
      simp only [q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change f.coord j w = g (t⁻¹ * w) *
      Polynomial.eval w ((p j).comp q)
    rw [Polynomial.eval_comp, hqeval]
    exact hrep'

/-- Two successive dilations compose by multiplication of their scales. -/
theorem Curve.dilate_dilate
    {n : ℕ} (f : Curve n) (s t : ℂ) :
    (f.dilate s).dilate t = f.dilate (s * t) := by
  apply curve_eq_of_coord_eq
  funext j z
  simp [Curve.dilate]
  ring

/-- For a nonzero scale, transcendence is invariant in both directions. -/
theorem Curve.dilate_transcendental_iff
    {n : ℕ} (f : Curve n) (t : ℂ) (ht : t ≠ 0) :
    f.Transcendental ↔ (f.dilate t).Transcendental := by
  constructor
  · exact Curve.dilate_transcendental f t ht
  · intro h
    have hinv : t⁻¹ ≠ 0 := inv_ne_zero ht
    have hback := Curve.dilate_transcendental (f.dilate t) t⁻¹ hinv h
    have hcomp : (f.dilate t).dilate t⁻¹ = f := by
      apply curve_eq_of_coord_eq
      funext j z
      simp [Curve.dilate]
      field_simp
    simpa [hcomp] using hback

/-- For a nonzero scale, linear nondegeneracy is invariant in both directions. -/
theorem Curve.dilate_linearlyNonDegenerate_iff
    {n : ℕ} (f : Curve n) (t : ℂ) (ht : t ≠ 0) :
    f.linearlyNonDegenerate ↔ (f.dilate t).linearlyNonDegenerate := by
  constructor
  · exact Curve.dilate_linearlyNonDegenerate f t ht
  · intro h
    have hinv : t⁻¹ ≠ 0 := inv_ne_zero ht
    have hback := Curve.dilate_linearlyNonDegenerate (f.dilate t) t⁻¹ hinv h
    have hcomp : (f.dilate t).dilate t⁻¹ = f := by
      apply curve_eq_of_coord_eq
      funext j z
      simp [Curve.dilate]
      field_simp
    simpa [hcomp] using hback

/-- For a positive real scale, the projective characteristic of a dilation is
the original characteristic evaluated at the scaled radius. -/
theorem Curve.characteristic_dilate_of_pos
    {n : ℕ} (f : Curve n) {t r : ℝ} (ht : 0 < t) :
    characteristic (f.dilate (t : ℂ)) r = characteristic f (t * r) := by
  have havg :
      Real.circleAverage
          (fun z : ℂ => Real.log ‖(f.dilate (t : ℂ)).vector z‖) 0 r =
        Real.circleAverage
          (fun z : ℂ => Real.log ‖f.vector z‖) 0 (t * r) := by
    rw [Real.circleAverage_eq_circleAverage_zero_one]
    nth_rw 2 [Real.circleAverage_eq_circleAverage_zero_one]
    apply Real.circleAverage_congr_sphere
    intro z hz
    change Real.log ‖f.vector ((t : ℂ) * ((r : ℂ) * z + 0))‖ =
      Real.log ‖f.vector ((t * r : ℝ) * z + 0)‖
    congr 2
    push_cast
    ring_nf
  unfold characteristic
  rw [havg]
  have hcenter : ‖(f.dilate (t : ℂ)).vector 0‖ = ‖f.vector 0‖ := by
    change ‖f.vector ((t : ℂ) * 0)‖ = ‖f.vector 0‖
    simp
  rw [hcenter]

end
end FewInflection




