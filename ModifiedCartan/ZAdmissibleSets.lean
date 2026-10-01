import ModifiedCartan.RightZFactors
import ModifiedCartan.ZStripComplement

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The exact predecessor condition on a right support in KP Section 4.1.3.
Its equivalence to existence of actual factors is proved separately. -/
def IsZAdmissible {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z Y : Finset A) : Prop :=
  Z ⊆ Y ∧ ∀ a ∈ Y \ Z, θ⁻¹ a ∈ Y

theorem rightZFactor_isZAdmissible {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (π : Equiv.Perm A) (h : IsRightZFactor θ Z Y π) :
    IsZAdmissible θ Z Y :=
  ⟨((isRightZFactor_iff θ Z Y π).mp h).1, rightZFactor_predecessor_mem θ Z Y π h⟩

theorem zAdmissible_strip_predecessor {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) (a : Z) (i : ℕ)
    (hi : i + 1 < zStripLength θ Z a) (hm : (θ ^ (i + 1)) a.val ∈ Y) :
    (θ ^ i) a.val ∈ Y := by
  have hp := h.2 _ (Finset.mem_sdiff.mpr
    ⟨hm, zStripLength_minimal θ Z a (i + 1) (by omega) hi⟩)
  simpa [pow_succ', Equiv.Perm.mul_apply] using hp

theorem zAdmissible_strip_downward {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) (a : Z) (i j : ℕ)
    (hij : i ≤ j) (hj : j < zStripLength θ Z a) (hm : (θ ^ j) a.val ∈ Y) :
    (θ ^ i) a.val ∈ Y := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    simpa [hi] using hm
  | succ j ih =>
    by_cases he : i = j + 1
    · simpa [he] using hm
    · exact ih (by omega) (by omega) (zAdmissible_strip_predecessor θ Z Y h a j hj hm)

theorem zAdmissible_complement_inv_closed {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) (x : A)
    (hx : x ∈ zStripComplement θ Z ∩ Y) : θ⁻¹ x ∈ zStripComplement θ Z ∩ Y := by
  obtain ⟨hc, hy⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_inter.mpr ⟨(zStripComplement_inv_apply_iff θ Z x).mpr hc,
    h.2 x (Finset.mem_sdiff.mpr ⟨hy, zStripComplement_not_mem_Z θ Z x hc⟩)⟩

theorem zAdmissible_complement_inv_image {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) :
    (zStripComplement θ Z ∩ Y).image (fun x => θ⁻¹ x) = zStripComplement θ Z ∩ Y := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact zAdmissible_complement_inv_closed θ Z Y h a ha
  · rw [Finset.card_image_of_injective _ (θ⁻¹).injective]

theorem zAdmissible_complement_apply_iff {A : Type*} [Fintype A] (θ : Equiv.Perm A)
    (Z Y : Finset A) (h : IsZAdmissible θ Z Y) (x : A) :
    θ x ∈ zStripComplement θ Z ∩ Y ↔ x ∈ zStripComplement θ Z ∩ Y := by
  constructor
  · intro hx
    simpa using zAdmissible_complement_inv_closed θ Z Y h (θ x) hx
  · intro hx
    rw [← zAdmissible_complement_inv_image θ Z Y h] at hx
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hx
    have he' : a = θ x := by simpa using congrArg θ he
    exact he' ▸ ha

end
end ModifiedCartan

