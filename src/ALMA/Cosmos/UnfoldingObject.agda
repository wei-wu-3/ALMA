------------------------------------------------------------------------
-- Object-level structure for container-based unfolding systems
--
-- Maps shapes/positions to base-category objects and next-universe seeds,
-- with transport laws coherent with the container functor
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.UnfoldingObject where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (Container; shape; position)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ContCatEquiv

ShapeOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → Functor C (ContCat s p) → Category.Obj C → Set s
ShapeOf F A = Container.Shape (Functor.₀ F A)
PosOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
      → (F : Functor C (ContCat s p)) {A : Category.Obj C}
      → ShapeOf F A → Set p
PosOf F {A} s = Container.Position (Functor.₀ F A) s

record UnfoldingObject (ℓ : Level) (CE : ContCatEquiv ℓ) (X : Set (lsuc (lsuc ℓ))) 
  : Set (lsuc (lsuc ℓ)) where
  private
    module CE = ContCatEquiv CE
    module OE = ObjEquivCat CE.base
    module Cat = Category OE.cat
  open CE using (containerFunctor; transportContainer)
  open OE using (_≈ₒ_; ≈ₒ-isEquiv)
  open Cat using (Obj)
  field
    unfold-obj   : {A : Obj} → ShapeOf containerFunctor A → Obj
    pos-to-shape : ∀ {A} (s : ShapeOf containerFunctor A) 
                   → PosOf containerFunctor s → ShapeOf containerFunctor (unfold-obj s)
    unfold-next  : ∀ {A} → ShapeOf containerFunctor A → X
    unfold-obj-resp-≈ : ∀ {A} {s₁ s₂ : ShapeOf containerFunctor A}
                      → s₁ ≡ s₂ → unfold-obj s₁ ≈ₒ unfold-obj s₂
    pos-to-shape-resp-≈ : ∀ {A} (s : ShapeOf containerFunctor A) {p₁ p₂ : PosOf containerFunctor s}
                        → p₁ ≡ p₂ → pos-to-shape s p₁ ≡ pos-to-shape s p₂
    pos-to-shape-transport : ∀ {A} {s₁ s₂ : ShapeOf containerFunctor A}
                            → (eq : s₁ ≡ s₂) {p : PosOf containerFunctor s₁}
                            → shape (transportContainer (unfold-obj-resp-≈ eq)) (pos-to-shape s₁ p)
                              ≡ pos-to-shape s₂ (subst (PosOf containerFunctor) eq p)
