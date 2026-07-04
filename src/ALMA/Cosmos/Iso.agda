------------------------------------------------------------------------
-- Isomorphism in a category
--
-- Defines the notion of isomorphism (_≅_) for objects in any category
-- proves that isomorphism is an equivalence relation, and provides the
-- corresponding IsEquivalence instance (isoEquiv)
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Iso where

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary using (IsEquivalence)
open import Categories.Category using (Category)

-- Isomorphism in a category
module Iso {o ℓ e : Level} (C : Category o ℓ e) where
  open Category C
  open Equiv
  open HomReasoning
  -- Object isomorphism: two-sided inverse up to ≈
  infix 4 _≅_
  record _≅_ (A B : Obj) : Set (ℓ ⊔ e) where
    constructor iso
    field
      to   : A ⇒ B
      from : B ⇒ A
      isoˡ : from ∘ to ≈ id
      isoʳ : to ∘ from ≈ id
  open _≅_ public

  -- Isomorphism is an equivalence relation
  isoRefl : ∀ {A : Obj} → A ≅ A
  isoRefl = iso id id identityˡ identityʳ
  isoSym : ∀ {A B : Obj} → A ≅ B → B ≅ A
  isoSym i = iso (from i) (to i) (isoʳ i) (isoˡ i)
  isoTrans : ∀ {A B D : Obj} → A ≅ B → B ≅ D → A ≅ D
  isoTrans {A} {B} {D} i j = iso
    (to j ∘ to i)
    (from i ∘ from j)
    (begin
      (from i ∘ from j) ∘ (to j ∘ to i)
        ≈⟨ assoc ⟩
      from i ∘ (from j ∘ (to j ∘ to i))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      from i ∘ ((from j ∘ to j) ∘ to i)
        ≈⟨ refl⟩∘⟨ isoˡ j ⟩∘⟨refl ⟩
      from i ∘ (id ∘ to i)
        ≈⟨ refl⟩∘⟨ identityˡ ⟩
      from i ∘ to i
        ≈⟨ isoˡ i ⟩
      id
        ∎)
    (begin
      (to j ∘ to i) ∘ (from i ∘ from j)
        ≈⟨ assoc ⟩
      to j ∘ (to i ∘ (from i ∘ from j))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      to j ∘ ((to i ∘ from i) ∘ from j)
        ≈⟨ refl⟩∘⟨ isoʳ i ⟩∘⟨refl ⟩
      to j ∘ (id ∘ from j)
        ≈⟨ refl⟩∘⟨ identityˡ ⟩
      to j ∘ from j
        ≈⟨ isoʳ j ⟩
      id
        ∎)
  isoEquiv : IsEquivalence _≅_
  isoEquiv = record
    { refl  = isoRefl
    ; sym   = isoSym
    ; trans = isoTrans
    }
