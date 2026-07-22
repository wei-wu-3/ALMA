------------------------------------------------------------------------
-- MorphismMorphism: compatibility of position maps with hom-actions
-- 态射间态射：位置映射与态射作用的相容性
--
-- onActP : onPos commutes with the container position maps actPOf,
-- modulo the position transport encoded by the parameter actP
-- onActP : onPos 与容器的位置映射 actPOf 交换，模掉由参数 actP 编码的位置运输
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.MorphismMorphism where

open import Agda.Primitive using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos.MorphismObject
  using (MorphismObject; idMorphismObject; compMorphismObject)

-- Given a MorphismObject (onPos : PosOf FC s → PosOf FD (S s)),
-- a MorphismMorphism witnesses that onPos is compatible with the
-- hom-action on positions (actPOf), up to the shape transport encoded by the parameter actP.
-- 给定一个 MorphismObject（onPos : PosOf FC s → PosOf FD (S s)），
-- MorphismMorphism 证明 onPos 与位置上的态射作用（actPOf）相容，模掉由参数 actP 编码的 shape 运输。
module _ {o h e o′ ℓ′ e′ s p u v : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
         {X : Set u} {Y : Set v}
         (UF : Unfolding FC X) (UG : Unfolding FD Y)
         (S  : Functor (ShapeCat C FC) (ShapeCat D FD))
         (shapeTrans : ∀ {A} {s : ShapeOf FC A}
                     → PosOf FC s
                     → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG)
                                             (Functor.₀ S (A , s))))
         (MO : MorphismObject UF UG S shapeTrans)
         (actP : ∀ {A B} (f : Category._⇒_ C A B) (s : ShapeOf FC A)
               → PosOf FD (proj₂ (Functor.₀ S (B , actSOf FC f s)))
               → PosOf FD (proj₂ (Functor.₀ S (A , s)))) where
  private
    module C  = Category C
    module D  = Category D
    module FC = Functor FC
    module FD = Functor FD
    module Sf = Functor S
    module MO = MorphismObject MO
  -- MorphismMorphism : onPos commutes with actPOf modulo actP
  -- 态射间态射：onPos 与 actPOf 模 actP 交换
  record MorphismMorphism : Set (o ⊔ h ⊔ s ⊔ p) where
    field
      onActP : ∀ {A B} (f : C._⇒_ A B) (s : ShapeOf FC A)
             → (p : PosOf FC (actSOf FC f s))
             → MO.onPos (actPOf FC f s p)
               ≡ actP f s (MO.onPos p)

-- actP-from-S : canonical actP derived from the functor S itself
-- actP-from-S : 由函子 S 本身导出的典范 actP
module _ {o h e o′ ℓ′ e′ s p : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         (FC : Functor C (ContCat s p)) (FD : Functor D (ContCat s p))
         (S  : Functor (ShapeCat C FC) (ShapeCat D FD)) where
  private
    module C  = Category C
    module FC = Functor FC
    module FD = Functor FD
    module Sf = Functor S
  actP-from-S : ∀ {A B} (f : C._⇒_ A B) (s : ShapeOf FC A)
              → PosOf FD (proj₂ (Sf.₀ (B , actSOf FC f s)))
              → PosOf FD (proj₂ (Sf.₀ (A , s)))
  actP-from-S {A} f s q =
    actPOf FD (proj₁ (Sf.₁ (f , refl))) (proj₂ (Sf.₀ (A , s)))
      (subst (PosOf FD) (sym (proj₂ (Sf.₁ (f , refl)))) q)

-- Identity MorphismMorphism
-- 恒等态射间态射
module _ {o h e s p u : Level} {C : Category o h e}
         {FC : Functor C (ContCat s p)} {X : Set u}
         (UF : Unfolding FC X) where
  private
    module UF = Unfolding UF
  idMorphismMorphism :
    MorphismMorphism UF UF idF (λ p → UF.pos-to-shape _ p)
                    (idMorphismObject UF)
                    (λ f s → actPOf FC f s)
  idMorphismMorphism = record { onActP = λ f s p → refl }

-- Composition of MorphismMorphisms
-- 态射间态射的复合
module _ {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
         {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)} {FE : Functor E (ContCat s p)}
         {X : Set u} {Y : Set v} {Z : Set w}
         (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
         (S₁ : Functor (ShapeCat C FC) (ShapeCat D FD))
         (S₂ : Functor (ShapeCat D FD) (ShapeCat E FE))
         (shTrans₁ : ∀ {A} {s : ShapeOf FC A} → PosOf FC s
                   → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG) (Functor.₀ S₁ (A , s))))
         (shTrans₂ : ∀ {A} {s : ShapeOf FD A} → PosOf FD s
                   → ShapeOf FE (Functor.₀ (Unfolding.unfoldFunctor UH) (Functor.₀ S₂ (A , s))))
         (actP₁ : ∀ {A B} (f : Category._⇒_ C A B) (s : ShapeOf FC A)
                → PosOf FD (proj₂ (Functor.₀ S₁ (B , actSOf FC f s)))
                → PosOf FD (proj₂ (Functor.₀ S₁ (A , s))))
         (actP₂ : ∀ {A B} (f : Category._⇒_ D A B) (s : ShapeOf FD A)
                → PosOf FE (proj₂ (Functor.₀ S₂ (B , actSOf FD f s)))
                → PosOf FE (proj₂ (Functor.₀ S₂ (A , s))))
         (actP₁₂ : ∀ {A B} (f : Category._⇒_ C A B) (s : ShapeOf FC A)
                 → PosOf FE (proj₂ (Functor.₀ (S₂ ∘F S₁) (B , actSOf FC f s)))
                 → PosOf FE (proj₂ (Functor.₀ (S₂ ∘F S₁) (A , s)))) where
  private
    module C  = Category C
    module D  = Category D
    module FC = Functor FC
    module FD = Functor FD
    module FE = Functor FE
    module S₁ = Functor S₁
    module S₂ = Functor S₂
  -- compMorphismMorphism : compose two MorphismMorphisms
  -- compMorphismMorphism : 复合两个态射间态射
  compMorphismMorphism :
      {MOf : MorphismObject UF UG S₁ shTrans₁}
      {MOg : MorphismObject UG UH S₂ shTrans₂}
      (MMf : MorphismMorphism UF UG S₁ shTrans₁ MOf actP₁)
      (MMg : MorphismMorphism UG UH S₂ shTrans₂ MOg actP₂)
      (coh : ∀ {A B} (f : C._⇒_ A B) (s : ShapeOf FC A)
               (p : PosOf FC (actSOf FC f s))
           → MorphismObject.onPos MOg
               (MorphismObject.onPos MOf (actPOf FC f s p))
             ≡ actP₁₂ f s (MorphismObject.onPos MOg (MorphismObject.onPos MOf p)))
      → MorphismMorphism UF UH (S₂ ∘F S₁)
                 (λ p → shTrans₂ (MorphismObject.onPos MOf p))
                 (compMorphismObject UF UG UH S₁ S₂ shTrans₁ shTrans₂ MOf MOg)
                 actP₁₂
  compMorphismMorphism {MOf} {MOg} MMf MMg coh = record
    { onActP = coh }
