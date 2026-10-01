import ModifiedCartan.SupportedPermutationRestrictions
import Mathlib.Data.Fintype.Powerset

open scoped Classical

namespace ModifiedCartan
noncomputable section

def finiteSubtypeSupportImage {A : Type*} (U : Finset A) (X : Finset U) : Finset A :=
  X.map (Function.Embedding.subtype (fun a => a ∈ U))

theorem finiteSubtypeSupportImage_mem {A : Type*} (U : Finset A) (X : Finset U) (a : U) :
    a.val ∈ finiteSubtypeSupportImage U X ↔ a ∈ X := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := Finset.mem_map.mp h
    have hba : b = a := Subtype.ext he
    simpa only [hba] using hb
  · intro h
    exact Finset.mem_map.mpr ⟨a, h, rfl⟩

theorem finiteSubtypeSupportImage_subset {A : Type*} (U : Finset A) (X : Finset U) :
    finiteSubtypeSupportImage U X ⊆ U := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
  exact b.property

theorem finiteSubtypeSupportImage_preimage {A : Type*} (U : Finset A) (X : Finset U) :
    (finiteSubtypeSupportImage U X).subtype (fun a => a ∈ U) = X := by
  ext a
  rw [Finset.mem_subtype, finiteSubtypeSupportImage_mem]

theorem finiteSubtypeSupportImage_subtype {A : Type*} (U X : Finset A) (hX : X ⊆ U) :
    finiteSubtypeSupportImage U (X.subtype (fun a => a ∈ U)) = X :=
  Finset.subtype_map_of_mem (fun _ ha => hX ha)

theorem finiteSubtypeSupportImage_univ {A : Type*} (U : Finset A) :
    finiteSubtypeSupportImage U Finset.univ = U := by
  ext a
  constructor
  · exact fun h => finiteSubtypeSupportImage_subset U _ h
  · intro ha
    exact Finset.mem_map.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩

theorem finiteSubtypeSupportImage_union {A : Type*} (U : Finset A) (X Y : Finset U) :
    finiteSubtypeSupportImage U (X ∪ Y) =
      finiteSubtypeSupportImage U X ∪ finiteSubtypeSupportImage U Y :=
  Finset.map_union X Y

theorem finiteSubtypeSupportImage_inter {A : Type*} (U : Finset A) (X Y : Finset U) :
    finiteSubtypeSupportImage U (X ∩ Y) =
      finiteSubtypeSupportImage U X ∩ finiteSubtypeSupportImage U Y :=
  Finset.map_inter X Y

theorem finiteSubtypeSupportImage_card {A : Type*} (U : Finset A) (X : Finset U) :
    (finiteSubtypeSupportImage U X).card = X.card := Finset.card_map _

def finiteSubtypeSupportEquiv {A : Type*} (U : Finset A) :
    Finset U ≃ {X : Finset A // X ⊆ U} where
  toFun X := ⟨finiteSubtypeSupportImage U X, finiteSubtypeSupportImage_subset U X⟩
  invFun X := X.val.subtype (fun a => a ∈ U)
  left_inv := finiteSubtypeSupportImage_preimage U
  right_inv X := Subtype.ext (finiteSubtypeSupportImage_subtype U X.val X.property)

def finiteSubtypeSupportElementEquiv {A : Type*} (U : Finset A) (X : Finset U) :
    X ≃ ↥(finiteSubtypeSupportImage U X) where
  toFun a := ⟨a.val.val, (finiteSubtypeSupportImage_mem U X a.val).mpr a.property⟩
  invFun a := ⟨⟨a.val, finiteSubtypeSupportImage_subset U X a.property⟩,
    (finiteSubtypeSupportImage_mem U X _).mp a.property⟩
  left_inv a := rfl
  right_inv a := rfl

end
end ModifiedCartan

