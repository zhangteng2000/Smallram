import ModifiedCartan.KPBetaCommutation
import Mathlib.Algebra.MvPolynomial.Funext

open scoped Classical BigOperators MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Evaluation of polynomial parameters in the symmetric-group algebra. -/
def kpParameterEvaluation {N : ℕ} (z : Fin N → ℂ) :
    (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)] →ₐ[ℂ] ℂ[Equiv.Perm (Fin N)] :=
  MonoidAlgebra.mapAlgHom (Equiv.Perm (Fin N)) (MvPolynomial.aeval z)

/-- Constant group-algebra elements inside the polynomial parameter algebra. -/
def kpParameterLift {N : ℕ} : ℂ[Equiv.Perm (Fin N)] →ₐ[ℂ]
    (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)] :=
  MonoidAlgebra.mapAlgHom (Equiv.Perm (Fin N)) (Algebra.ofId ℂ (MvPolynomial (Fin N) ℂ))

theorem kpParameterEvaluation_coeff {N : ℕ} (z : Fin N → ℂ)
    (x : (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)]) (g : Equiv.Perm (Fin N)) :
    (kpParameterEvaluation z x).coeff g = MvPolynomial.eval z (x.coeff g) := by
  rw [kpParameterEvaluation, MonoidAlgebra.coeff_mapAlgHom]
  rfl

theorem kpParameterEvaluation_lift {N : ℕ} (z : Fin N → ℂ)
    (x : ℂ[Equiv.Perm (Fin N)]) : kpParameterEvaluation z (kpParameterLift x) = x := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  rw [kpParameterEvaluation_coeff]
  change MvPolynomial.eval z (MvPolynomial.C (x.coeff g)) = x.coeff g
  simp only [MvPolynomial.eval_C]

theorem kpParameterEvaluation_smul {N : ℕ} (z : Fin N → ℂ)
    (r : MvPolynomial (Fin N) ℂ)
    (x : (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)]) :
    kpParameterEvaluation z (r • x) = MvPolynomial.eval z r • kpParameterEvaluation z x := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp only [kpParameterEvaluation_coeff, MonoidAlgebra.coeff_smul_apply, smul_eq_mul, map_mul]

theorem kpParameterEvaluation_ext {N : ℕ}
    {x y : (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)]}
    (h : ∀ z : Fin N → ℂ, kpParameterEvaluation z x = kpParameterEvaluation z y) : x = y := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply MvPolynomial.funext
  intro z
  simpa only [kpParameterEvaluation_coeff] using congrArg (fun u => u.coeff g) (h z)

/-- Polynomial identities in the group algebra are determined by positive
    real parameter tuples. Repeated or complex parameters need no limiting
    eigenspace assumption when this principle is used. -/
theorem kpParameterEvaluation_ext_pos_real {N : ℕ}
    {x y : (MvPolynomial (Fin N) ℂ)[Equiv.Perm (Fin N)]}
    (h : ∀ z : Fin N → ℝ, (∀ i, 0 < z i) →
      kpParameterEvaluation (fun i => (z i : ℂ)) x =
        kpParameterEvaluation (fun i => (z i : ℂ)) y) : x = y := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  let s : Set ℂ := Set.range (fun k : ℕ => ((k + 1 : ℕ) : ℂ))
  have hs : s.Infinite := Set.infinite_range_of_injective (by
    intro k l he
    have hh : k + 1 = l + 1 := Nat.cast_injective he
    omega)
  apply MvPolynomial.funext_set (fun _ : Fin N => s) (fun _ => hs)
  intro z hz
  have hh : ∀ i, ∃ k : ℕ, ((k + 1 : ℕ) : ℂ) = z i := fun i => hz i (Set.mem_univ i)
  choose k hk using hh
  have hp := h (fun i => ((k i + 1 : ℕ) : ℝ)) (fun i => by positivity)
  have he : (fun i => ((((k i + 1 : ℕ) : ℝ)) : ℂ)) = z := by
    funext i
    simpa only [Complex.ofReal_natCast] using hk i
  rw [he] at hp
  simpa only [kpParameterEvaluation_coeff] using congrArg (fun u => u.coeff g) hp

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterEvaluation_ext_pos_real