import ModifiedCartan.ScalarProximityMatrixGauge
import ModifiedCartan.ScalarDyadicProximityLimit

open scoped Topology Matrix
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan

theorem scalarSectorMultiplicity_equiv {m : ℕ} (β : Fin m → WithTop ℂ)
    (e : WithTop ℂ ≃ WithTop ℂ) (a : WithTop ℂ) :
    scalarSectorMultiplicity (fun j => e (β j)) a = scalarSectorMultiplicity β (e.symm a) := by
  classical
  unfold scalarSectorMultiplicity
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← e.eq_symm_apply]

/-- Every original curve has all-radius projective proximity limits equal to
integer multiplicities totaling twice the order. The coordinate normalization
and its target bijection are constructed inside the proof.
Auxiliary to LaTeX `thm:A` (b). -/
theorem scalar_exists_projective_proximity_multiplicities
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    ∃ p : WithTop ℂ → ℕ, HasSum (fun a => (p a : ℝ)) (2 * ρ) ∧
      ∀ a : WithTop ℂ, Tendsto (fun r => scalarProjectiveProximity f a r / characteristic f r)
        atTop (𝓝 ((p a : ℝ) / ρ)) := by
  classical
  obtain ⟨B, hB, hnorm, hB0⟩ :=
    exists_euclidean_matrix_nonzero_coordinates (f.vector 0) (f.vector_ne_zero 0)
  let g := f.matrixGauge B hB
  have hT : characteristic g = characteristic f :=
    characteristic_matrixGauge_of_euclidean_isometry f B hB hnorm
  have hN : ramification g = ramification f := FewInflection.Curve.matrixGauge_ramification_eq f B hB
  have hgL : g.linearlyNonDegenerate := (f.matrixGauge_linearlyNonDegenerate_iff B hB).mp hlin
  have hgT : g.Transcendental := (f.matrixGauge_transcendental_iff B hB).mp htrans
  have hgS : SmallRamification g := by simpa only [SmallRamification, hT, hN] using hsmall
  have hgl : strongLowerIndex (characteristic g) = (ρ : EReal) := by rw [hT]; exact hl
  have hgu : strongUpperIndex (characteristic g) = (ρ : EReal) := by rw [hT]; exact hu
  obtain ⟨q⟩ := scalar_exists_all_dyadic_sector_targets g hgL hgT hgS hρ hgl hgu hm
  obtain ⟨e, he⟩ := exists_scalar_target_equiv_matrix B hB
  let targets : Fin m → WithTop ℂ := fun j => (q j).target
  let p : WithTop ℂ → ℕ := scalarSectorMultiplicity (fun j => e (targets j))
  have hmR : (m : ℝ) = 2 * ρ := by linarith
  refine ⟨p, ?_, fun a => ?_⟩
  · rw [← hmR]
    exact scalarSectorMultiplicity_hasSum _
  · obtain ⟨c, hc, hcform⟩ := he (e.symm a)
    rw [e.apply_symm_apply] at hcform
    have hlim := scalar_projective_proximity_ratio_dyadic g hgL hgT hgS hB0 hρ hgl hgu hm q (e.symm a)
    have hp : p a = scalarSectorMultiplicity targets (e.symm a) := scalarSectorMultiplicity_equiv targets e a
    rw [hp]
    exact scalar_projective_proximity_limit_of_matrixGauge f hlin htrans B hB hnorm hc hcform hlim

end ModifiedCartan
#print axioms ModifiedCartan.scalar_exists_projective_proximity_multiplicities
