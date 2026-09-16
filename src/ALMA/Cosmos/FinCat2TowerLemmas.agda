------------------------------------------------------------------------
-- Structural lemmas about the FinCat 2 tower
-- FinCat 2 塔的结构引理
--
-- Results that depend on the concrete twoTower but not on any limit
-- construction:
-- every layer's shape set is inhabited
-- every layer's shape set is a singleton
-- layer objects are in bijection with Fin 2
-- Also includes an experimental LimitLayer construction (colimitLimit);
-- see the note on its F₁ field
-- 只依赖具体 twoTower、不依赖极限构造的结果：
-- 每层形状集可居留
-- 每层形状集为单点
-- 层对象与 Fin 2 双射
-- 另含一个实验性的 LimitLayer 构造（colimitLimit）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2TowerLemmas where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality.Core using (cong; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Base using (id)

open import Categories.Category.Core using (Category)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchyInstances using (module FinCatHierarchy)
open FinCatHierarchy using (FinCat)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (LayerIdx; Tower; LimitLayer)
open import ALMA.Cosmos.FinCat2Witness using (TrivialFC; TwoObjLayer; twoIdx; twoTower)

open StrictLayer
open Tower
open LimitLayer

-- Local alias for the ⇔ projections
-- ⇔ 投影的局部别名
to-⇔ : ∀ {a b} {A : Set a} {B : Set b} → A ⇔ B → A → B
to-⇔ = Function.Bundles.Equivalence.to

from-⇔ : ∀ {a b} {A : Set a} {B : Set b} → A ⇔ B → B → A
from-⇔ = Function.Bundles.Equivalence.from

-- Every layer's shape set is inhabited
-- 每层形状集可居留
shape-inhabited-at
  : ∀ n (A : Category.Obj (C (layer twoTower n)))
  → ShapeOf (FC (layer twoTower n)) A
shape-inhabited-at zero    A         = lift tt
shape-inhabited-at (suc n) (A , s)   = lift (shape-inhabited-at n A)

-- Every layer's shape set is a singleton
-- 每层形状集为单点
shape-singleton-at
  : ∀ n (A : Category.Obj (C (layer twoTower n)))
  → (s t : ShapeOf (FC (layer twoTower n)) A) → s ≡ t
shape-singleton-at zero    A         (lift tt) (lift tt) = refl
shape-singleton-at (suc n) (A , _)   (lift u)  (lift v)  =
  cong lift (shape-singleton-at n A u v)

-- Object projection from any layer to Fin 2 (via repeated proj₁)
-- 从任意层到 Fin 2 的对象投影（反复取 proj₁）
proj-obj : ∀ n → Category.Obj (C (layer twoTower n)) → Fin 2
proj-obj zero    A       = A
proj-obj (suc n) (A , _) = proj-obj n A

-- Object embedding from Fin 2 into any layer (mutual with embed-shape)
-- 从 Fin 2 到任意层的对象嵌入（与 embed-shape 互递归）
mutual
  embed-obj : ∀ n → Fin 2 → Category.Obj (C (layer twoTower n))
  embed-obj zero    A = A
  embed-obj (suc n) A = (embed-obj n A , embed-shape n (embed-obj n A))

  embed-shape : ∀ n (A : Category.Obj (C (layer twoTower n)))
              → ShapeOf (FC (layer twoTower n)) A
  embed-shape zero    _       = lift tt
  embed-shape (suc n) (A , _) = lift (embed-shape n A)

-- Layer objects are in bijection with Fin 2
-- 层对象与 Fin 2 双射
layer-obj-bijection
  : ∀ n → Category.Obj (C (layer twoTower n)) ⇔ Fin 2
layer-obj-bijection zero    = mk⇔ id id
layer-obj-bijection (suc n) =
  mk⇔ (λ { (A , _) → to-⇔ (layer-obj-bijection n) A })
       (λ A → from-⇔ (layer-obj-bijection n) A
              , shape-inhabited-at n (from-⇔ (layer-obj-bijection n) A))

-- Experimental LimitLayer construction
-- 实验性 LimitLayer 构造
--
-- The F₁ field below is set to the constant tt. This compiles only
-- because the target category's morphism set is
-- treated as a singleton after projection; it is not a faithful functor in
-- the usual sense. Kept as a proof-of-inhabitation of LimitLayer
-- 下面的 F₁ 字段取常值 tt。它能通过类型检查只是因为
-- 投影后目标范畴的态射集被视为单点；它不是通常意义上的忠实函子
-- 保留它仅作为 LimitLayer 可居留性的证明

colimitLimit : LimitLayer twoIdx twoTower
colimitLimit = record
  { o∞ = lzero ; h∞ = lzero ; e∞ = lzero ; s∞ = lzero ; p∞ = lzero
  ; layer∞ = TwoObjLayer
  ; projC = λ n → record
      { F₀           = to-⇔ (layer-obj-bijection n)
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
  }
