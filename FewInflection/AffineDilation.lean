import FewInflection.Dilation

open scoped BigOperators Topology

namespace FewInflection

noncomputable section

private theorem curve_eq_of_coord_eq_affine
    {n : ℕ} {f g : Curve n} (hcoord : f.coord = g.coord) : f = g := by
  cases f with
  | mk fc fh fr =>
    cases g with
    | mk gc gh gr =>
      simp_all

/-! Precomposition by an affine map is the rescaling used around arbitrary
points in the paper. -/
def Curve.affineDilate {n : ℕ} (f : Curve n) (a t : ℂ) : Curve n where
  coord := fun j z => f.coord j (a + t * z)
  holomorphic := by
    intro j
    exact (f.holomorphic j).comp (by fun_prop)
  reduced := by
    intro z
    rcases f.reduced (a + t * z) with ⟨j, hj⟩
    exact ⟨j, hj⟩

lemma iteratedDeriv_affineDilate
    {n : ℕ} (f : Curve n) (a t : ℂ) (i : Index n) (j : Index n) (z : ℂ) :
    iteratedDeriv (i : ℕ) (fun x => f.coord j (a + t * x)) z =
      t ^ (i : ℕ) * iteratedDeriv (i : ℕ) (f.coord j) (a + t * z) := by
  let g : ℂ → ℂ := fun y => f.coord j (a + y)
  have hg : ContDiff ℂ (i : ℕ) g := by
    exact ((f.holomorphic j).contDiff (n := (i : ℕ))).comp
      (contDiff_const.add contDiff_id)
  have hscale := iteratedDeriv_comp_const_mul hg t
  have hshift := iteratedDeriv_comp_const_add (i : ℕ) (f.coord j) a
  have hshift' := congrFun hshift (t * z)
  have hscale' := congrFun hscale z
  dsimp [g] at hscale' hshift'
  rw [hshift'] at hscale'
  simpa [mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using hscale'

theorem wronskian_affineDilate
    {n : ℕ} (f : Curve n) (a t z : ℂ) :
    wronskian n (f.affineDilate a t).coord z =
      t ^ (∑ i : Index n, (i : ℕ)) * wronskian n f.coord (a + t * z) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun (i : Index n) (j : Index n) =>
      iteratedDeriv (i : ℕ) (f.coord j) (a + t * z)
  let D : Matrix (Index n) (Index n) ℂ :=
    Matrix.diagonal (fun i : Index n => t ^ (i : ℕ))
  have hM :
      (fun (i : Index n) (j : Index n) =>
        iteratedDeriv (i : ℕ) ((f.affineDilate a t).coord j) z) = D * M := by
    funext i j
    rw [Matrix.diagonal_mul]
    dsimp [D, M, Curve.affineDilate]
    exact iteratedDeriv_affineDilate f a t i j z
  calc
    wronskian n (f.affineDilate a t).coord z = (D * M).det := by
      simp only [wronskian, hM]
    _ = D.det * M.det := Matrix.det_mul _ _
    _ = (∏ i : Index n, t ^ (i : ℕ)) * wronskian n f.coord (a + t * z) := by
      rw [Matrix.det_diagonal]
      rfl
    _ = t ^ (∑ i : Index n, (i : ℕ)) * wronskian n f.coord (a + t * z) := by
      rw [Finset.prod_pow_eq_pow_sum]

theorem wronskian_affineDilate_ne_zero_iff
    {n : ℕ} (f : Curve n) (a t z : ℂ) (ht : t ≠ 0) :
    wronskian n (f.affineDilate a t).coord z ≠ 0 ↔
      wronskian n f.coord (a + t * z) ≠ 0 := by
  rw [wronskian_affineDilate]
  exact (mul_ne_zero_iff_left (pow_ne_zero _ ht))

theorem Curve.affineDilate_linearlyNonDegenerate
    {n : ℕ} (f : Curve n) (a t : ℂ) (ht : t ≠ 0)
    (hlin : f.linearlyNonDegenerate) :
    (f.affineDilate a t).linearlyNonDegenerate := by
  unfold Curve.linearlyNonDegenerate at hlin ⊢
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro c hc j
  have hrel : (∑ i : Index n, c i • f.coord i) = 0 := by
    funext w
    obtain ⟨z, hz⟩ : ∃ z : ℂ, a + t * z = w := by
      refine ⟨t⁻¹ * (w - a), ?_⟩
      field_simp
      ring
    have hcz := congrFun hc z
    have hsum :
        (∑ i : Index n, c i • f.coord i) w =
          ∑ i : Index n, c i • f.coord i w := by
      simp [Finset.sum_apply]
    rw [hsum, ← hz]
    simpa [Curve.affineDilate, Finset.sum_apply] using hcz
  exact hlin c hrel j

theorem Curve.affineDilate_linearlyNonDegenerate_iff
    {n : ℕ} (f : Curve n) (a t : ℂ) (ht : t ≠ 0) :
    f.linearlyNonDegenerate ↔
      (f.affineDilate a t).linearlyNonDegenerate := by
  constructor
  · exact Curve.affineDilate_linearlyNonDegenerate f a t ht
  · intro h
    have hinv : t⁻¹ ≠ 0 := inv_ne_zero ht
    let b : ℂ := -t⁻¹ * a
    have hback := Curve.affineDilate_linearlyNonDegenerate
      (f.affineDilate a t) b t⁻¹ hinv h
    have hcomp : (f.affineDilate a t).affineDilate b t⁻¹ = f := by
      apply curve_eq_of_coord_eq_affine
      funext j z
      simp [b, Curve.affineDilate]
      field_simp
      ring
    simpa [hcomp] using hback

theorem Curve.affineDilate_affineDilate
    {n : ℕ} (f : Curve n) (a t b s : ℂ) :
    (f.affineDilate a t).affineDilate b s =
      f.affineDilate (a + t * b) (t * s) := by
  apply curve_eq_of_coord_eq_affine
  funext j z
  simp [Curve.affineDilate]
  ring

theorem Curve.affineDilate_transcendental
    {n : ℕ} (f : Curve n) (a t : ℂ) (ht : t ≠ 0)
    (htrans : f.Transcendental) :
    (f.affineDilate a t).Transcendental := by
  intro hrep_affine
  apply htrans
  rcases hrep_affine with ⟨p, g, hg, hgd, hrep⟩
  let q : Polynomial ℂ :=
    Polynomial.C (t⁻¹) * (Polynomial.X - Polynomial.C a)
  refine ⟨fun j => (p j).comp q,
    (fun w => g (t⁻¹ * (w - a))), ?_, ?_, ?_⟩
  · intro w
    exact hg (t⁻¹ * (w - a))
  · exact hgd.comp (by fun_prop)
  · intro j w
    have hrep' := hrep j (t⁻¹ * (w - a))
    have htw : a + t * (t⁻¹ * (w - a)) = w := by
      field_simp
      ring
    rw [show (f.affineDilate a t).coord j (t⁻¹ * (w - a)) =
      f.coord j (a + t * (t⁻¹ * (w - a))) by rfl, htw] at hrep'
    have hqeval : q.eval w = t⁻¹ * (w - a) := by
      simp only [q, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X]
    change f.coord j w = g (t⁻¹ * (w - a)) *
      Polynomial.eval w ((p j).comp q)
    rw [Polynomial.eval_comp, hqeval]
    exact hrep'

theorem Curve.affineDilate_transcendental_iff
    {n : ℕ} (f : Curve n) (a t : ℂ) (ht : t ≠ 0) :
    f.Transcendental ↔ (f.affineDilate a t).Transcendental := by
  constructor
  · exact Curve.affineDilate_transcendental f a t ht
  · intro h
    have hinv : t⁻¹ ≠ 0 := inv_ne_zero ht
    let b : ℂ := -t⁻¹ * a
    have hback := Curve.affineDilate_transcendental
      (f.affineDilate a t) b t⁻¹ hinv h
    have hcomp : (f.affineDilate a t).affineDilate b t⁻¹ = f := by
      apply curve_eq_of_coord_eq_affine
      funext j z
      simp [b, Curve.affineDilate]
      field_simp
      ring
    simpa [hcomp] using hback

/-! The characteristic of an affine rescaling is the characteristic of the
original curve on the translated and rescaled circle.  This is the analytic
identity used when passing to blow-up limits around arbitrary points. -/
theorem Curve.characteristic_affineDilate_of_pos
    {n : ℕ} (f : Curve n) {a : ℂ} {t r : ℝ} (_ht : 0 < t) :
    characteristic (f.affineDilate a (t : ℂ)) r =
      Real.circleAverage (fun z : ℂ => Real.log ‖f.vector z‖) a (t * r) -
        Real.log ‖f.vector a‖ := by
  have havg :
      Real.circleAverage
          (fun z : ℂ => Real.log ‖(f.affineDilate a (t : ℂ)).vector z‖) 0 r =
        Real.circleAverage
          (fun z : ℂ => Real.log ‖f.vector z‖) a (t * r) := by
    rw [Real.circleAverage_eq_circleAverage_zero_one]
    nth_rw 2 [Real.circleAverage_eq_circleAverage_zero_one]
    apply Real.circleAverage_congr_sphere
    intro z hz
    change Real.log ‖f.vector (a + (t : ℂ) * ((r : ℂ) * z + 0))‖ =
      Real.log ‖f.vector (((t * r : ℝ) : ℂ) * z + a)‖
    congr 2
    push_cast
    ring_nf
  unfold characteristic
  rw [havg]
  have hcenter :
      ‖(f.affineDilate a (t : ℂ)).vector 0‖ = ‖f.vector a‖ := by
    change ‖f.vector (a + (t : ℂ) * 0)‖ = ‖f.vector a‖
    simp
  rw [hcenter]

end

end FewInflection
