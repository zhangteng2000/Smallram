import ModifiedCartan.PolynomialDegreeBasis
import ModifiedCartan.SchubertMonicWronskian
import ModifiedCartan.PolynomialAlternantTranslation

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Every actual polynomial space of dimension n+1 belongs to a fitting
    Schubert cell; its degree profile is constructed by basis reduction. -/
theorem polynomialSpace_exists_schubertFrame {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b₀ : Module.Basis (Fin (n + 1)) ℂ V) :
    ∃ τ : YoungDiagram, V ∈ polynomialSchubertCell n (n + 1 + τ.rowLen 0) τ := by
  obtain ⟨b, hb⟩ := polynomialBasis_exists_strictMono_natDegree b₀
  obtain ⟨τ, hf, he⟩ := exists_partitionAlternantExponent
    (fun i : Fin (n + 1) => (b i.rev).val.natDegree)
    (fun _ _ hij => hb (Fin.rev_strictAnti hij))
  refine ⟨τ, (partitionFits_iff_height_le τ).mpr hf, le_rfl, ⟨⟨b, ?_⟩⟩⟩
  intro i
  have hi := congrFun he i.rev
  rw [partitionAlternantExponent_rev, Fin.rev_rev] at hi
  exact hi.symm

/-- Changing the polynomial basis does not change the monic Wronskian. -/
theorem polynomialWronskian_normalize_basis_change {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b c : Module.Basis (Fin (n + 1)) ℂ V) :
    normalize (FewInflection.polynomialWronskian (fun j => (c j).val)) =
      normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) := by
  rw [← partitionPolynomialMinor_bot, ← partitionPolynomialMinor_bot,
    partitionPolynomialMinor_basis_change b c, normalize_mul]
  have hn : normalize (Polynomial.C (b.toMatrix c).det) = (1 : Polynomial ℂ) :=
    normalize_eq_one.mpr (Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (polynomialBasis_toMatrix_det_ne_zero b c)))
  rw [hn, mul_one]

theorem schubertMonicWronskian_eq_basis {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (b : Module.Basis (Fin (n + 1)) ℂ V) :
    schubertMonicWronskian hV =
      normalize (FewInflection.polynomialWronskian (fun j => (b j).val)) :=
  polynomialWronskian_normalize_basis_change b (schubertFrame hV).basis

theorem schubertMonicWronskian_natDegree {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) :
    (schubertMonicWronskian hV).natDegree = partitionSize τ := by
  have he : (schubertMonicWronskian hV).natDegree =
      (FewInflection.polynomialWronskian (schubertFrame hV).polynomials).natDegree := by
    simp only [schubertMonicWronskian, Polynomial.natDegree, Polynomial.degree_normalize]
  rw [he]
  exact polynomialSchubertCell_wronskian_degree hV

theorem schubertWronskiFibre_partitionSize {M n D : ℕ} {τ : YoungDiagram}
    (roots : Fin M → ℂ) {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ)
    (hW : schubertMonicWronskian hV = ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    partitionSize τ = M := by
  have he := congrArg Polynomial.natDegree hW
  rw [schubertMonicWronskian_natDegree] at he
  have hd : (∏ i, (Polynomial.X - Polynomial.C (roots i))).natDegree = M := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (roots i))]
    simp
  exact he.trans hd

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialSpace_exists_schubertFrame
#print axioms ModifiedCartan.schubertWronskiFibre_partitionSize