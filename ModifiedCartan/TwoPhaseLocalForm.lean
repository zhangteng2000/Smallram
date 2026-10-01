import ModifiedCartan.LocalAffineMaximum

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The three possibilities for a nonempty subset of two prescribed phases. -/
theorem nonempty_finset_subset_pair {B : Finset ℂ} {a b : ℂ}
    (hne : B.Nonempty) (hB : B ⊆ {a, b}) : B = {a} ∨ B = {b} ∨ B = {a, b} := by
  classical
  have hm (x : ℂ) (hx : x ∈ B) : x = a ∨ x = b := by simpa using hB hx
  by_cases ha : a ∈ B
  · by_cases hb : b ∈ B
    · right; right
      apply Finset.Subset.antisymm hB
      intro x hx
      rcases (show x = a ∨ x = b from by simpa using hx) with rfl | rfl
      · exact ha
      · exact hb
    · left
      apply Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, ?_⟩
      intro x hx
      rcases hm x hx with he | rfl
      · exact he
      · exact (hb hx).elim
  · right; left
    obtain ⟨x, hx⟩ := hne
    have hb : b ∈ B := by
      rcases hm x hx with rfl | rfl
      · exact (ha hx).elim
      · exact hx
    apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hb, ?_⟩
    intro y hy
    rcases hm y hy with rfl | he
    · exact (ha hy).elim
    · exact he

/-- The maximum of the opposite affine phases is an absolute real part. -/
theorem phaseAffineMax_opposite (a : ℂ) (k : ℝ) (c z : ℂ)
    (h : ({a, -a} : Finset ℂ).Nonempty) :
    phaseAffineMax {a, -a} h k c z = k + |(a * (z - c)).re| := by
  classical
  unfold phaseAffineMax
  rw [Finset.sup'_insert (H := Finset.singleton_nonempty (-a)), Finset.sup'_singleton]
  change max (k + (a * (z - c)).re) (k + (-a * (z - c)).re) = _
  rw [neg_mul, Complex.neg_re]
  by_cases hp : 0 ≤ (a * (z - c)).re
  · rw [abs_of_nonneg hp, max_eq_left (by linarith)]
  · rw [abs_of_neg (lt_of_not_ge hp), max_eq_right (by linarith)]

/-- Local classification with two opposite weak gradients, proved from the
actual subharmonic representative. Auxiliary to LaTeX `thm:A` (b). -/
theorem IsSubharmonicOn.locally_two_phase_form
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hw : HasWeakComplexGradient U v g) (a : ℂ)
    (hA : ∀ᵐ z ∂volume.restrict U, g z = a ∨ g z = -a) {c : ℂ} (hc : c ∈ U) :
    ∃ s : ℝ, 0 < s ∧ ball c s ⊆ U ∧
      (EqOn (fun z => (u z).toReal) (fun z => (u c).toReal + (a * (z - c)).re) (ball c s) ∨
       EqOn (fun z => (u z).toReal) (fun z => (u c).toReal - (a * (z - c)).re) (ball c s) ∨
       EqOn (fun z => (u z).toReal) (fun z => (u c).toReal + |(a * (z - c)).re|) (ball c s)) := by
  classical
  have hgA : ∀ᵐ z ∂volume.restrict U, g z ∈ ({a, -a} : Finset ℂ) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hA
  obtain ⟨s, B, hB, hs, hsU, hBA, he⟩ := hu.locally_eq_phaseAffineMax hU hrep hw {a, -a} hgA hc
  refine ⟨s, hs, hsU, ?_⟩
  rcases nonempty_finset_subset_pair hB hBA with hB' | hB' | hB'
  · subst B
    left
    intro z hz
    simpa only [phaseAffineMax, Finset.sup'_singleton] using he hz
  · subst B
    right; left
    intro z hz
    simpa only [phaseAffineMax, Finset.sup'_singleton, neg_mul, Complex.neg_re,
      sub_eq_add_neg] using he hz
  · subst B
    right; right
    intro z hz
    exact (he hz).trans (phaseAffineMax_opposite a (u c).toReal c z hB)

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.locally_two_phase_form

