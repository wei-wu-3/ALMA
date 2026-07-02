------------------------------------------------------------------------
-- Category with an object equivalence relation
--
-- Defines ObjEquivCat: a Category equipped with an object equivalence _≈ₒ_ and a coherent transport of morphisms
-- The standard instance uses the notion of isomorphism from category theory
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ObjEquivCat where

open import Agda.Primitive using (_⊔_; lsuc; Level)
open import Categories.Category using (Category)
open import Relation.Binary using (IsEquivalence)

open import ALMA.Cosmos.Iso

-- Category with an object equivalence
record ObjEquivCat (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  field
    cat : Category o ℓ e
  private
    module Cat = Category cat
  open Cat using (Obj; _⇒_; _≈_; id; _∘_)
  infix 4 _≈ₒ_
  field
    -- Object equivalence relation
    _≈ₒ_       : Obj → Obj → Set (ℓ ⊔ e)
    ≈ₒ-isEquiv : IsEquivalence _≈ₒ_
    -- Transport of morphisms along object equivalences
    transport : ∀ {A₁ A₂ B₁ B₂}
                → A₁ ≈ₒ A₂ → B₁ ≈ₒ B₂
                → A₁ ⇒ B₁
                → A₂ ⇒ B₂
    -- Coherence laws
    transport-resp-≈ : ∀ {A₁ A₂ B₁ B₂}
                        → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂)
                        → ∀ {f g : A₁ ⇒ B₁}
                        → f ≈ g → transport eqA eqB f ≈ transport eqA eqB g
    transport-refl : ∀ {A B} {f : A ⇒ B}
                        → transport (IsEquivalence.refl ≈ₒ-isEquiv) (IsEquivalence.refl ≈ₒ-isEquiv) f ≈ f
    transport-trans : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                        → (eqA₁ : A₁ ≈ₒ A₂) (eqA₂ : A₂ ≈ₒ A₃)
                        → (eqB₁ : B₁ ≈ₒ B₂) (eqB₂ : B₂ ≈ₒ B₃)
                        → {f : A₁ ⇒ B₁}
                        → transport (IsEquivalence.trans ≈ₒ-isEquiv eqA₁ eqA₂)
                                        (IsEquivalence.trans ≈ₒ-isEquiv eqB₁ eqB₂) f
                          ≈
                          transport eqA₂ eqB₂ (transport eqA₁ eqB₁ f)
    transport-∘ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
                → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂) (eqC : C₁ ≈ₒ C₂)
                → (f : A₁ ⇒ B₁) (g : B₁ ⇒ C₁)
                → transport eqB eqC g ∘ transport eqA eqB f
                  ≈ transport eqA eqC (g ∘ f)
    transport-id : ∀ {A B} (eqA : A ≈ₒ B)
                 → transport eqA eqA (id {A}) ≈ id {B}

-- Canonical instance: isomorphism as object equivalence
objEquivCatFromIso : ∀ {o ℓ e} (C : Category o ℓ e) → ObjEquivCat o ℓ e
objEquivCatFromIso C =
  let
    open Category C
    open Equiv
    open Iso C
  in
  let
    transport' : ∀ {A₁ A₂ B₁ B₂} → A₁ ≅ A₂ → B₁ ≅ B₂ → (A₁ ⇒ B₁) → (A₂ ⇒ B₂)
    transport' A≅ B≅ f = to B≅ ∘ f ∘ from A≅
    transport-resp-≈' : ∀ {A₁ A₂ B₁ B₂}
                      → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂)
                      → ∀ {f g : A₁ ⇒ B₁}
                      → f ≈ g → transport' eqA eqB f ≈ transport' eqA eqB g
    transport-resp-≈' _ _ f≈g = ∘-resp-≈ʳ (∘-resp-≈ˡ f≈g)
    transport-refl' : ∀ {A B} {f : A ⇒ B} → transport' isoRefl isoRefl f ≈ f
    transport-refl' =
      let
        step1 = ∘-resp-≈ʳ identityʳ
        step2 = identityˡ
      in
      trans step1 step2
    transport-trans' : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                     → (eqA₁ : A₁ ≅ A₂) (eqA₂ : A₂ ≅ A₃)
                     → (eqB₁ : B₁ ≅ B₂) (eqB₂ : B₂ ≅ B₃)
                     → {f : A₁ ⇒ B₁}
                     → transport' (isoTrans eqA₁ eqA₂) (isoTrans eqB₁ eqB₂) f
                       ≈ transport' eqA₂ eqB₂ (transport' eqA₁ eqB₁ f)
    transport-trans' eqA₁ eqA₂ eqB₁ eqB₂ {f} =
      let
        step1 = assoc
        step2 = ∘-resp-≈ʳ (∘-resp-≈ʳ sym-assoc)
        step3 = ∘-resp-≈ʳ sym-assoc
      in
      trans step1 (trans step2 step3)
    transport-∘' : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
                 → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂) (eqC : C₁ ≅ C₂)
                 → (f : A₁ ⇒ B₁) (g : B₁ ⇒ C₁)
                 → transport' eqB eqC g ∘ transport' eqA eqB f
                   ≈ transport' eqA eqC (g ∘ f)
    transport-∘' eqA eqB eqC f g =
      let
        step1 = ∘-resp-≈ˡ sym-assoc
        step2 = assoc
        step3 = ∘-resp-≈ʳ sym-assoc
        step4 = ∘-resp-≈ʳ (∘-resp-≈ˡ (isoˡ eqB))
        step5 = ∘-resp-≈ʳ identityˡ
        step6 = assoc
        step7 = ∘-resp-≈ʳ sym-assoc
      in
      trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 step7)))))
    transport-id' : ∀ {A B} (eqA : A ≅ B)
                  → transport' eqA eqA (id {A}) ≈ id {B}
    transport-id' eqA =
      let
        step1 = ∘-resp-≈ʳ identityˡ
        step2 = isoʳ eqA
      in
      trans step1 step2
  in
  record
  { cat              = C
  ; _≈ₒ_             = _≅_
  ; ≈ₒ-isEquiv       = isoEquiv
  ; transport        = transport'
  ; transport-resp-≈ = transport-resp-≈'
  ; transport-refl   = transport-refl'
  ; transport-trans  = transport-trans'
  ; transport-∘      = transport-∘'
  ; transport-id     = transport-id'
  }
