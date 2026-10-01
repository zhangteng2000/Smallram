import Mathlib.Algebra.MonoidAlgebra.MapDomain

namespace ModifiedCartan
noncomputable section

theorem addMonoidAlgebra_comm_coeff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N]
    (p : AddMonoidAlgebra (AddMonoidAlgebra R M) N) (m : M) (n : N) :
    ((AddMonoidAlgebra.commRingEquiv p).coeff m).coeff n = (p.coeff n).coeff m := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | single j r =>
    induction r using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs =>
      simp only [AddMonoidAlgebra.single_add, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hr, hs]
    | single i a =>
      simp only [AddMonoidAlgebra.commRingEquiv_single_single, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply]
      split_ifs <;> simp_all

end
end ModifiedCartan

