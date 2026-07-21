------------------------------------------------------------------------
-- Morphisms between ContCat-valued functors
--
-- A natural transformation α : FC → FD ∘ H
-- where FC, FD : ContCat-valued functors, H : C → D
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCatEquivFunctor where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; setoid)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Container.Core using (shape)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation
  using (NaturalTransformation; id; _∘ᵥ_; _∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (unitorʳ; associator; NaturalIsomorphism)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv
  using (shapeFunctor; ContCatEquiv; ShapeCat; module ContCatEquiv)
open import ALMA.Cosmos.ContCategoryLemmas
  using (shape-eq-from-≈M; ShapeOf; PosOf; actSOf; actPOf)

-- Pairs a base functor with a natural transformation between ContCat-valued functors
module _ {o h e o′ ℓ′ e′ s p : Level}
    {C : Category o h e}
    {D : Category o′ ℓ′ e′}
    (FC : Functor C (ContCat s p))
    (FD : Functor D (ContCat s p))
    (baseFunctor : Functor C D)
    (containerNat : NaturalTransformation FC (FD ∘F baseFunctor)) where
  record ContCatEquivFunctor : Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ s ⊔ p)) where

-- Identity ContCatEquivFunctor
idContCatEquivFunctor : ∀ {o h e s p} {C : Category o h e}
  (FC : Functor C (ContCat s p))
  → ContCatEquivFunctor FC FC idF (NaturalIsomorphism.F⇐G unitorʳ)
idContCatEquivFunctor FC = record {}

-- Composition of ContCatEquivFunctors
compContCatEquivFunctor : ∀ {o h e o′ ℓ′ e′ o″ ℓ″ e″ s p}
    {C : Category o h e}
    {D : Category o′ ℓ′ e′}
    {E : Category o″ ℓ″ e″}
    (FC : Functor C (ContCat s p))
    (FD : Functor D (ContCat s p))
    (FE : Functor E (ContCat s p))
    {bg : Functor D E} {bf : Functor C D}
    {ng : NaturalTransformation FD (FE ∘F bg)}
    {nf : NaturalTransformation FC (FD ∘F bf)}
  → ContCatEquivFunctor FD FE bg ng
  → ContCatEquivFunctor FC FD bf nf
  → ContCatEquivFunctor FC FE (bg ∘F bf)
      ( NaturalIsomorphism.F⇒G (associator bf bg FE)
          ∘ᵥ (ng ∘ʳ bf)
          ∘ᵥ nf
      )
compContCatEquivFunctor _ _ _ _ _ = record {}

-- Trivial constructor packing a functor and natural transformation
mkContCatEquivFunctor : ∀ {o h e o′ ℓ′ e′ s p}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    (F : Functor C D)
    (FC : Functor C (ContCat s p))
    (FD : Functor D (ContCat s p))
    (α : NaturalTransformation FC (FD ∘F F))
  → ContCatEquivFunctor FC FD F α
mkContCatEquivFunctor _ _ _ _ = record {}

-- Functor between shape categories induced by a ContCatEquivFunctor
module ShapeCatMorphism {o h e o′ ℓ′ e′ s p}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {H : Functor C D}
    {α : NaturalTransformation FC (FD ∘F H)}
    (cf : ContCatEquivFunctor FC FD H α)
    where
  private
    open NaturalTransformation α
    module H = Functor H
    module FC = Functor FC
    module FD = Functor FD
  S : Functor (ShapeCat C FC) (ShapeCat D FD)
  S = record
    { F₀ = λ { (A , s) → (H.₀ A , shape (η A) s) }
    ; F₁ = λ { {(A , s)} {(B , t)} (f , p) →
        let
          comm-shape : shape (η B) (shape (FC.F₁ f) s) ≡ shape (FD.F₁ (H.F₁ f)) (shape (η A) s)
          comm-shape = shape-eq-from-≈M (commute f) s
          q : shape (FD.F₁ (H.F₁ f)) (shape (η A) s) ≡ shape (η B) t
          q = trans (sym comm-shape) (cong (shape (η B)) p)
        in (H.F₁ f , q) }
    ; identity     = λ { {A , s} → H.identity }
    ; homomorphism = λ { {f = _} {g = _} → H.homomorphism }
    ; F-resp-≈     = λ { {f = _} {g = _} f≈g → H.F-resp-≈ f≈g }
    }
