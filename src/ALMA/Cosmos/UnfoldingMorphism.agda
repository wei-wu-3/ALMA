------------------------------------------------------------------------
-- Morphism-level structure for container-based unfolding systems
--
-- Lifts base-category morphisms to unfoldings and enforces functor laws
-- and position-action compatibility, all up to object equivalence transport
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.UnfoldingMorphism where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (Container; _⇒_; shape; position)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.UnfoldingObject
open import ALMA.Cosmos.ContCategoryLemmas

record UnfoldingMorphism (ℓ : Level) (CE : ContCatEquiv ℓ) (X : Set (lsuc (lsuc ℓ)))
                         (UO : UnfoldingObject ℓ CE X) : Set (lsuc (lsuc ℓ)) where
  private
    module CE′ = ContCatEquiv CE
    module OE  = ObjEquivCat CE′.base
    module Cat = Category OE.cat
  open UnfoldingObject UO
  field
    unfold-hom : ∀ {A B} (f : Cat._⇒_ A B) (s : ShapeOf CE′.containerFunctor A)
                 → unfold-obj s Cat.⇒ unfold-obj (actSOf CE′.containerFunctor f s)
    unfold-hom-resp-≈ : ∀ {A B} {f f' : Cat._⇒_ A B} {s s' : ShapeOf CE′.containerFunctor A}
                      → (f≈ : f Cat.≈ f') (s≡ : s ≡ s')
                      → OE.transport (unfold-obj-resp-≈ s≡)
                                     (unfold-obj-resp-≈ (trans (actS-resp-≈ CE′.containerFunctor f≈ s)
                                                               (cong (actSOf CE′.containerFunctor f') s≡)))
                                     (unfold-hom f s)
                        Cat.≈ unfold-hom f' s'
    unfold-hom-id : ∀ {A} (s : ShapeOf CE′.containerFunctor A)
                  → unfold-hom Cat.id s
                    Cat.≈ OE.transport (IsEquivalence.refl OE.≈ₒ-isEquiv)
                                       (IsEquivalence.sym OE.≈ₒ-isEquiv (unfold-obj-resp-≈ (actS-id-eq CE′.containerFunctor s)))
                                       Cat.id
    unfold-hom-comp : ∀ {A B C} {f : Cat._⇒_ A B} {g : Cat._⇒_ B C} (s : ShapeOf CE′.containerFunctor A)
                    → unfold-hom (g Cat.∘ f) s
                      Cat.≈ OE.transport (IsEquivalence.refl OE.≈ₒ-isEquiv)
                                         (IsEquivalence.sym OE.≈ₒ-isEquiv (unfold-obj-resp-≈ (actS-comp-eq CE′.containerFunctor s)))
                                         (unfold-hom g (actSOf CE′.containerFunctor f s) Cat.∘ unfold-hom f s)
    pos-actS-compat : ∀ {A B} (f : Cat._⇒_ A B) (s : ShapeOf CE′.containerFunctor A)
                    → (p : PosOf CE′.containerFunctor (actSOf CE′.containerFunctor f s))
                    → pos-to-shape (actSOf CE′.containerFunctor f s) p
                      ≡ actSOf CE′.containerFunctor (unfold-hom f s) (pos-to-shape s (actPOf CE′.containerFunctor f s p))
