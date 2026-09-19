------------------------------------------------------------------------
-- Structural lemmas about the FinCat 2 tower
-- FinCat 2 塔的结构引理
--
-- Collects results depending only on twoTower, independent of any limit
-- construction: shape-set inhabitation and singleton property at every
-- layer, bijection between layer objects and Fin 2, canonical morphism
-- between any two layer objects (hom), collapsibility of every layer
-- (twoTower-collapsible), and canonical retraction of a Cosmos into its
-- base layer (twoTower-retract)
-- 汇集只依赖 twoTower、不依赖任何极限构造的结果：每层形状集的可居留性
-- 与单点性、层对象与 Fin 2 的双射、任意两个层对象之间的规范态射（hom）、
-- 每层的可坍缩性（twoTower-collapsible）、从 Cosmos 到其基层的规范
-- 收缩（twoTower-retract）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2TowerLemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; trans)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Base using (id)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchy
  using (Collapsible; collapsible→ShapeCat-collapsible)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (Tower)
open import ALMA.Cosmos.FinCat2Witness using (twoTower)

open Function.Bundles.Equivalence using (to; from)
open StrictLayer
open Tower

-- Shape set inhabitation at every layer
-- Layer 0: lift tt; layer suc n: lift of the layer-n inhabitant
-- 每层形状集的可居留性
-- 第 0 层：lift tt；第 suc n 层：第 n 层居民的 lift
shape-inhabited-at
  : ∀ n (A : Category.Obj (C (layer twoTower n)))
  → ShapeOf (FC (layer twoTower n)) A
shape-inhabited-at zero    A         = lift tt
shape-inhabited-at (suc n) (A , s)   = lift (shape-inhabited-at n A)

-- Shape set singleton property at every layer
-- Layer 0: refl on lift tt; layer suc n: cong lift of the layer-n proof
-- 每层形状集的单点性
-- 第 0 层：lift tt 上的 refl；第 suc n 层：第 n 层证明的 cong lift
shape-singleton-at
  : ∀ n (A : Category.Obj (C (layer twoTower n)))
  → (s t : ShapeOf (FC (layer twoTower n)) A) → s ≡ t
shape-singleton-at zero    A         (lift tt) (lift tt) = refl
shape-singleton-at (suc n) (A , _)   (lift u)  (lift v)  =
  cong lift (shape-singleton-at n A u v)

-- Object projection C_n → Fin 2 by iterated proj₁
-- proj-obj n is a retraction of embed-obj n
-- 对象投影 C_n → Fin 2，反复取 proj₁
-- proj-obj n 是 embed-obj n 的收缩
proj-obj : ∀ n → Category.Obj (C (layer twoTower n)) → Fin 2
proj-obj zero    A       = A
proj-obj (suc n) (A , _) = proj-obj n A

-- Object embedding Fin 2 → C_n, mutually recursive with embed-shape,
-- which supplies the required shape component
-- 对象嵌入 Fin 2 → C_n，与 embed-shape 互递归，
-- 后者提供所需的形状分量
mutual
  embed-obj : ∀ n → Fin 2 → Category.Obj (C (layer twoTower n))
  embed-obj zero    A = A
  embed-obj (suc n) A = (embed-obj n A , embed-shape n (embed-obj n A))

  -- Shape component of an embedded object
  -- 嵌入对象的形状分量
  embed-shape : ∀ n (A : Category.Obj (C (layer twoTower n)))
              → ShapeOf (FC (layer twoTower n)) A
  embed-shape zero    _       = lift tt
  embed-shape (suc n) (A , _) = lift (embed-shape n A)

-- Bijection between layer objects and Fin 2
-- Layer 0: identity; layer suc n: inherited, shape component from
-- shape-inhabited-at
-- 层对象与 Fin 2 的双射
-- 第 0 层：恒等；第 suc n 层：继承自第 n 层，
-- 形状分量由 shape-inhabited-at 提供
layer-obj-bijection
  : ∀ n → Category.Obj (C (layer twoTower n)) ⇔ Fin 2
layer-obj-bijection zero    = mk⇔ id id
layer-obj-bijection (suc n) =
  mk⇔ (λ { (A , _) → to (layer-obj-bijection n) A })
       (λ A → from (layer-obj-bijection n) A
              , shape-inhabited-at n (from (layer-obj-bijection n) A))

-- Canonical morphism between any two layer objects
-- Every layer is collapsible, so the morphism is unique up to _≈_
-- Layer 0: tt (FinCat 2 = Indiscrete (Fin 2))
-- Layer suc n: pair (hom n A B , eq), eq from shape-singleton-at
-- 任意两个层对象之间的规范态射
-- 每层可坍缩，故态射在 _≈_ 意义下唯一
-- 第 0 层：tt（FinCat 2 = Indiscrete (Fin 2)）
-- 第 suc n 层：(hom n A B , eq) 对，eq 由 shape-singleton-at 提供
hom : (n : ℕ) (X Y : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
    → Category._⇒_ (StrictLayer.C (Tower.layer twoTower n)) X Y
hom zero    X Y = tt
hom (suc n) (A , s) (B , t) = (hom n A B , eq)
  where
    FC_n = StrictLayer.FC (Tower.layer twoTower n)
    eq   = shape-singleton-at n B (actSOf FC_n (hom n A B) s) t

-- Collapsibility of every layer: any two parallel morphisms are
-- _≈_-equivalent
-- Layer 0: refl; layer suc n: inherited via
-- collapsible→ShapeCat-collapsible
-- 每层的可坍缩性：任意两个平行态射 _≈_ 等价
-- 第 0 层：refl；第 suc n 层：经 collapsible→ShapeCat-collapsible 继承
twoTower-collapsible : (n : ℕ)
  → Collapsible (StrictLayer.C (Tower.layer twoTower n))
twoTower-collapsible zero    = λ _ _ → refl
twoTower-collapsible (suc n) =
  collapsible→ShapeCat-collapsible
    {C  = StrictLayer.C (Tower.layer twoTower n)}
    {FC = StrictLayer.FC (Tower.layer twoTower n)}
    (twoTower-collapsible n)

-- Canonical retraction of a Cosmos into its base layer
-- For x at layer n and shape s at object A, the retraction is the
-- unique morphism x.F₀ (A , s) → A, obtained via hom
-- Used as the retract argument of mkEmbeddingData in FinCat2DefaultUnif
-- 从 Cosmos 到其基层的规范收缩
-- 对第 n 层的 x 与对象 A 上的形状 s，收缩是唯一态射
-- x.F₀ (A , s) → A，由 hom 给出
-- 在 FinCat2DefaultUnif 中用作 mkEmbeddingData 的 retract 参数
twoTower-retract : (n : ℕ)
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
              (StrictLayer.FC (Tower.layer twoTower n)))
  {A : Category.Obj (StrictLayer.C (Tower.layer twoTower n))}
  (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  → Category._⇒_ (StrictLayer.C (Tower.layer twoTower n))
      (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A
twoTower-retract n x {A} s =
  hom n (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A

-- x.pos-to-shape collapses to the second component of x.F₀
-- x.pos-to-shape 塌缩为 x.F₀ 的第二分量
x-pos-eq : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  (A : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
  (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  (s' : ShapeOf (StrictLayer.FC (Tower.layer twoTower (suc n))) (A , s))
  (p : PosOf (StrictLayer.FC (Tower.layer twoTower (suc n))) {A = (A , s)} s')
  → Unfolding.pos-to-shape (out x) {A = (A , s)} s' p
  ≡ lift (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , s')))
x-pos-eq n x A s s' p =
  trans (sym (lower-lift-eq (Unfolding.pos-to-shape (out x) {A = (A , s)} s' p)))
        (cong lift (shape-singleton-at n
          (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , s')))
          (lower (Unfolding.pos-to-shape (out x) {A = (A , s)} s' p))
          (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , s')))))
  where
    lower-lift-eq : ∀ {a b} {A : Set a} (u : Lift b A) → lift (lower u) ≡ u
    lower-lift-eq (lift _) = refl
