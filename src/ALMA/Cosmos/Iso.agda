------------------------------------------------------------------------
-- Isomorphism in a category
--
-- Defines the notion of isomorphism (_≅_) for objects in any category
-- proves that isomorphism is an equivalence relation, and provides the
-- corresponding IsEquivalence instance (isoEquiv)
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Iso where

open import Agda.Primitive using (_⊔_; Level)
open import Categories.Category using (Category)
open import Relation.Binary using (IsEquivalence)

-- Isomorphism in a category
module Iso {o ℓ e : Level} (C : Category o ℓ e) where
  open Category C
  open Equiv
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
    left-inverse
    right-inverse
    where
      left-inverse : (from i ∘ from j) ∘ (to j ∘ to i) ≈ id {A = A}
      left-inverse =
        let
          inner-step1 = sym-assoc
          inner-step2 = ∘-resp-≈ˡ (isoˡ j)
          inner-step3 = identityˡ
          inner-eq    = trans inner-step1 (trans inner-step2 inner-step3)
          step1 = assoc
          step2 = ∘-resp-≈ʳ inner-eq
          step3 = isoˡ i
        in
        trans step1 (trans step2 step3)
      right-inverse : (to j ∘ to i) ∘ (from i ∘ from j) ≈ id {A = D}
      right-inverse =
        let
          inner-step1 = sym-assoc
          inner-step2 = ∘-resp-≈ˡ (isoʳ i)
          inner-step3 = identityˡ
          inner-eq    = trans inner-step1 (trans inner-step2 inner-step3)
          step1 = assoc
          step2 = ∘-resp-≈ʳ inner-eq
          step3 = isoʳ j
        in
        trans step1 (trans step2 step3)
  isoEquiv : IsEquivalence _≅_
  isoEquiv = record
    { refl  = isoRefl
    ; sym   = isoSym
    ; trans = isoTrans
    }
