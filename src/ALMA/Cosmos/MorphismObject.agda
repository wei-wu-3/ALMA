------------------------------------------------------------------------
-- Object-level homomorphisms between unfolding systems
--
-- A MorphismObject witnesses the commutation of object/position mappings
-- with the container natural isomorphism
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.MorphismObject where

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_,_; proj₂)
open import Data.Container.Core using (shape)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_; id)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquivFunctor
  using (ContCatEquivFunctor; module ShapeCatMorphism)
open import ALMA.Cosmos.Unfolding using (Unfolding)

module _ {o h e o′ ℓ′ e′ s p u v : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
         {X : Set u} {Y : Set v}
         (UF : Unfolding FC X) (UG : Unfolding FD Y)
         (S  : Functor (ShapeCat C FC) (ShapeCat D FD))
         (shapeTrans : ∀ {A} {s : ShapeOf FC A}
                     → PosOf FC s
                     → ShapeOf FD
                         (Functor.₀ (Unfolding.unfoldFunctor UG)
                                    (Functor.₀ S (A , s)))) where
  private
    module C  = Category C; module D  = Category D
    module FC = Functor FC; module FD = Functor FD
    module UF = Unfolding UF; module UG = Unfolding UG; module Sf = Functor S
  record MorphismObject : Set (o ⊔ s ⊔ p) where
    field
      onPos      : ∀ {A} {s : ShapeOf FC A} → PosOf FC s → PosOf FD (proj₂ (Sf.₀ (A , s)))
      pts-compat : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s) → shapeTrans p ≡ UG.pos-to-shape (proj₂ (Sf.₀ (A , s))) (onPos p)

module _ {o h e s p u : Level} {C : Category o h e}
         {FC : Functor C (ContCat s p)} {X : Set u} (UF : Unfolding FC X) where
  private module UF = Unfolding UF
  idMorphismObject : MorphismObject UF UF id (λ p → UF.pos-to-shape _ p)
  idMorphismObject = record { onPos = λ p → p ; pts-compat = λ p → refl }

module _ {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
         {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)} {FE : Functor E (ContCat s p)}
         {X : Set u} {Y : Set v} {Z : Set w}
         (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
         (S₁ : Functor (ShapeCat C FC) (ShapeCat D FD))
         (S₂ : Functor (ShapeCat D FD) (ShapeCat E FE))
         (shTrans₁ : ∀ {A} {s : ShapeOf FC A} → PosOf FC s → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG) (Functor.₀ S₁ (A , s))))
         (shTrans₂ : ∀ {A} {s : ShapeOf FD A} → PosOf FD s → ShapeOf FE (Functor.₀ (Unfolding.unfoldFunctor UH) (Functor.₀ S₂ (A , s)))) where
  compMorphismObject : (mo₁ : MorphismObject UF UG S₁ shTrans₁) (mo₂ : MorphismObject UG UH S₂ shTrans₂)
                     → MorphismObject UF UH (S₂ ∘F S₁) (λ p → shTrans₂ (MorphismObject.onPos mo₁ p))
  compMorphismObject mo₁ mo₂ = record
    { onPos = λ p → onPos mo₂ (onPos mo₁ p)
    ; pts-compat = λ p → pts-compat mo₂ (onPos mo₁ p)
    } where open MorphismObject

module _ {o h e o′ ℓ′ e′ s p u v : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
         {X : Set u} {Y : Set v} (UF : Unfolding FC X) (UG : Unfolding FD Y) where
  private
    module UF  = Unfolding UF
    module UG  = Unfolding UG
    module FD  = Functor FD
    module UFf = Functor UF.unfoldFunctor
  mkMorphismObject :
    ∀ {H : Functor C D} {α : NaturalTransformation FC (FD ∘F H)}
    → (cf : ContCatEquivFunctor FC FD H α)
    → let module SCM = ShapeCatMorphism cf in
      (ni : NaturalIsomorphism (H ∘F UF.unfoldFunctor) (UG.unfoldFunctor ∘F SCM.S))
    → (onPos₀ : ∀ {A} {s : ShapeOf FC A} → PosOf FC s → PosOf FD (proj₂ (Functor.₀ SCM.S (A , s))))
    → (coh : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
           → shape (FD.₁ (NaturalTransformation.η (NaturalIsomorphism.F⇒G ni) (A , s)))
                   (shape (NaturalTransformation.η α (UFf.₀ (A , s))) (UF.pos-to-shape s p))
             ≡ UG.pos-to-shape (proj₂ (Functor.₀ SCM.S (A , s))) (onPos₀ p))
    → MorphismObject UF UG SCM.S
        (λ {A} {s} p → shape (FD.₁ (NaturalTransformation.η (NaturalIsomorphism.F⇒G ni) (A , s)))
                             (shape (NaturalTransformation.η α (UFf.₀ (A , s))) (UF.pos-to-shape s p)))
  mkMorphismObject cf ni onPos₀ coh = record { onPos = onPos₀ ; pts-compat = coh }
