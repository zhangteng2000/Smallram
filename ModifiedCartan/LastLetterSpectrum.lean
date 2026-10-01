import ModifiedCartan.FixedPointDeletion

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A ι : Type*} [Fintype A] [DecidableEq A] {κ : ι → Type*}

def lastLetterSpectrum (a : A) (c : ι → ℂ)
    (e : ∀ i, κ i → (↥(Finset.univ.erase a) → ℂ)) (p : Σ i, κ i) (x : A) : ℂ :=
  if h : x = a then c p.1 else e p.1 p.2 ⟨x, by simp [h]⟩

theorem lastLetterSpectrum_injective (a : A) (c : ι → ℂ) (hc : Function.Injective c)
    (e : ∀ i, κ i → (↥(Finset.univ.erase a) → ℂ)) (he : ∀ i, Function.Injective (e i)) :
    Function.Injective (lastLetterSpectrum a c e) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hh := congrArg (fun f : A → ℂ => f a) h
  have hij : i = j := hc (by simpa [lastLetterSpectrum] using hh)
  subst j
  have hxy : x = y := by
    apply he i
    funext z
    have hz := congrArg (fun f : A → ℂ => f z.val) h
    have hne : z.val ≠ a := (Finset.mem_erase.mp z.property).1
    simpa [lastLetterSpectrum, hne] using hz
  subst y
  rfl

end
end ModifiedCartan


