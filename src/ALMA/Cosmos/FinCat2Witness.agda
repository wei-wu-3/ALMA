------------------------------------------------------------------------
-- FinCat2Witness — reusable witness over FinCat 2
-- FinCat2Witness —— FinCat 2 上的可复用见证
--
-- Provides a concrete StrictLayer over FinCat 2 with a trivial container,
-- two distinguished cosmoi (cosmos-id, cosmos-const0) differing only in
-- F₀, and a proof they are not bisimilar. Shared by
-- ConditionalNontrivialLimit and LayerZeroMediator
-- 提供 FinCat 2 上平凡容器的具体 StrictLayer、两个仅在 F₀ 上不同的
-- 区分宇宙（cosmos-id 与 cosmos-const0），以及它们不互模拟的证明
-- 由 ConditionalNontrivialLimit 与 LayerZeroMediator 共享
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2Witness where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality.Core using (sym)
open import Relation.Nullary using (¬_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁)
open import Data.Nat using (suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Terminal using (_≈C_)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchyInstances using (module FinCatHierarchy)
open FinCatHierarchy using (FinCat)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (LayerIdx; Tower)

open StrictLayer
open Tower
open _≈C_

-- Trivial container over FinCat 2: singleton shapes and positions
-- FinCat 2 上的平凡容器：形状与位置均为单点集
TrivialFC : Functor (FinCat 2) (ContCat lzero lzero)
TrivialFC = record
  { F₀ = λ _ → record
      { Shape    = Lift lzero (⊤ {lzero})
      ; Position = λ _ → Lift lzero (⊤ {lzero})
      }
  ; F₁ = λ _ → record
      { shape    = λ _ → lift tt
      ; position = λ _ → lift tt
      }
  ; identity = record
      { shape-eq    = λ { (lift tt) → refl }
      ; position-eq = λ _ _ → refl
      }
  ; homomorphism = record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }
  ; F-resp-≈ = λ _ → record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }
  }

-- The base layer: FinCat 2 paired with the trivial container
-- 基础层：FinCat 2 配平凡容器
TwoObjLayer : StrictLayer lzero lzero lzero lzero lzero
TwoObjLayer = record { C = FinCat 2 ; FC = TrivialFC }

-- Layer index matching FinCat 2 with the trivial container
-- 匹配 FinCat 2 与平凡容器的层索引
twoIdx : LayerIdx
twoIdx = record { o = lzero ; h = lzero ; e = lzero ; s = lzero ; p = lzero }

-- The tower starting at TwoObjLayer
-- 从 TwoObjLayer 开始的塔
twoTower : Tower twoIdx
twoTower = record { layer₀ = TwoObjLayer }

-- Cosmos with F₀ = proj₁ (identity-like universe)
-- F₀ = proj₁ 的宇宙（类恒等宇宙）
cosmos-id : Cosmos (FinCat 2) TrivialFC
cosmos-id .out = record
  { unfoldFunctor = record
      { F₀ = proj₁
      ; F₁ = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
  ; unfold-next     = λ _ → cosmos-id
  ; pos-to-shape    = λ _ _ → lift tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- Cosmos with F₀ = λ _ → fzero (constant on first object)
-- F₀ = λ _ → fzero 的宇宙（常值于第一个对象）
cosmos-const0 : Cosmos (FinCat 2) TrivialFC
cosmos-const0 .out = record
  { unfoldFunctor = record
      { F₀ = λ _ → fzero
      ; F₁ = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
  ; unfold-next     = λ _ → cosmos-const0
  ; pos-to-shape    = λ _ _ → lift tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- fzero ≠ fsuc fzero at the appropriate type
-- 在恰当类型下 fzero ≠ fsuc fzero
zero≠suc-fzero : ∀ {n} → ¬ (fzero {n = suc n} ≡ fsuc {n = suc n} (fzero {n = n}))
zero≠suc-fzero ()

-- cosmos-id and cosmos-const0 are not bisimilar: their F₀ differ at fsuc fzero
-- cosmos-id 与 cosmos-const0 不互模拟：在 fsuc fzero 处 F₀ 不同
cosmos-id≉cosmos-const0 : ¬ (cosmos-id ≈C cosmos-const0)
cosmos-id≉cosmos-const0 eq =
  zero≠suc-fzero
    (sym (unfoldFunctor₀-eq eq {A = fsuc fzero} (lift tt)))
