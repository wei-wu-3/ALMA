{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.CosmosMorphism where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (J)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.Unfolding using (Unfolding; module Unfolding)
open import ALMA.Cosmos using (Cosmos; out)

record ShapeEndo {o h e s p : Level} {C : Category o h e}
    (FC : Functor C (ContCat s p)) : Set (o ⊔ h ⊔ s) where
  field
    shapeMap   : ∀ {A : Category.Obj C} → ShapeOf FC A → ShapeOf FC A
    shapeNat   : ∀ {A B} (f : Category._⇒_ C A B) (s : ShapeOf FC A)
               → shapeMap (actSOf FC f s) ≡ actSOf FC f (shapeMap s)

open ShapeEndo public

idShapeEndo : ∀ {o h e s p} {C : Category o h e}
              (FC : Functor C (ContCat s p)) → ShapeEndo FC
idShapeEndo FC = record
  { shapeMap = λ s → s
  ; shapeNat = λ f s → refl
  }

compShapeEndo : ∀ {o h e s p} {C : Category o h e}
                {FC : Functor C (ContCat s p)}
              → (T U : ShapeEndo FC) → ShapeEndo FC
compShapeEndo T U = record
  { shapeMap = λ s → T .shapeMap (U .shapeMap s)
  ; shapeNat = λ f s →
      trans (cong (T .shapeMap) (U .shapeNat f s))
            (T .shapeNat f (U .shapeMap s))
  }

mutual
  record _⇒ℱ[_]_
    {o h e s p : Level} {C : Category o h e}
    {FC : Functor C (ContCat s p)}
    (F : Cosmos C FC) (σ : ShapeEndo FC) (G : Cosmos C FC)
    : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    coinductive
    field
      out : ⇒ℱLayer[ σ ] F G

  record ⇒ℱLayer[_]
    {o h e s p : Level} {C : Category o h e}
    {FC : Functor C (ContCat s p)}
    (σ : ShapeEndo FC) (F G : Cosmos C FC)
    : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    inductive
    private
      module C = Category C
      UF = out F
      UG = out G
    field
      onPos : ∀ {A} {s : ShapeOf FC A}
            → PosOf FC (σ .shapeMap s) → PosOf FC s

      onActP : ∀ {A B} (f : Category._⇒_ C A B) (s : ShapeOf FC A)
                 (q : PosOf FC (σ .shapeMap (actSOf FC f s)))
             → onPos (actPOf FC f (σ .shapeMap s)
                        (subst (PosOf FC) (σ .shapeNat f s) q))
               ≡ actPOf FC f s (onPos q)

      onunfold-next : ∀ {A} (s : ShapeOf FC A)
                    → Unfolding.unfold-next UF s
                      ⇒ℱ[ σ ] Unfolding.unfold-next UG (σ .shapeMap s)

open _⇒ℱ[_]_ public
open ⇒ℱLayer[_] public

id⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
     → {F : Cosmos C FC} → F ⇒ℱ[ idShapeEndo FC ] F
id⇒ℱ {FC = FC} {F = F} .out .onPos = λ p → p
id⇒ℱ .out .onActP f s q = refl
id⇒ℱ {FC = FC} {F = F} .out .onunfold-next s = id⇒ℱ

comp⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
       {σ₁ σ₂ : ShapeEndo FC} {F G H : Cosmos C FC}
     → G ⇒ℱ[ σ₂ ] H
     → F ⇒ℱ[ σ₁ ] G
     → F ⇒ℱ[ compShapeEndo σ₂ σ₁ ] H
comp⇒ℱ {σ₁ = σ₁} {σ₂ = σ₂} {F = F} {G = G} {H = H} g f .out .onPos p =
  f .out .onPos (g .out .onPos p)
comp⇒ℱ {σ₁ = σ₁} {σ₂ = σ₂} {F = F} {G = G} {H = H} g f .out .onActP =
  {!!}
comp⇒ℱ {σ₁ = σ₁} {σ₂ = σ₂} {F = F} {G = G} {H = H} g f .out .onunfold-next s =
  comp⇒ℱ (g .out .onunfold-next (σ₁ .shapeMap s)) (f .out .onunfold-next s)