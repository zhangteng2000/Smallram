import ModifiedCartan.ZCycleSupportParameters
import Mathlib.Data.Fintype.Powerset

open scoped Classical

namespace ModifiedCartan
noncomputable section

instance {A : Type*} [Fintype A] (θ : Equiv.Perm A) (Z : Finset A) :
    Fintype (ZComplementCycleParameters θ Z) :=
  inferInstanceAs (Fintype {C : Finset (PermutationCycles θ) //
    C ⊆ permutationCycleImage θ (zStripComplement θ Z)})

end
end ModifiedCartan
