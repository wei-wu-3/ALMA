------------------------------------------------------------------------
-- Unfolding Functor Record
-- 展开函子记录
--
-- Defines the unfolding functor for a cosmos layer, mapping shaped objects to
-- the base category with seeds for the next universe
-- 为宇宙层定义展开函子，将带形状的对象映射到基范畴，
-- 并为下一层宇宙提供种子
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Unfolding where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (Func)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

-- Unfolding for a cosmos layer:
-- given a functor F : C → ContCat and a seed set X, an Unfolding records
-- a functor from the shape category back to C, a next-seed assignment,
-- and a position-to-shape map compatible with the functorial action
-- 宇宙层的展开：
-- 给定函子 F : C → ContCat 与种子集 X，Unfolding 记录
-- 一个从形状范畴回到 C 的函子、一个下一层种子赋值，
-- 以及与函子作用相容的位置到形状映射
module _ {o h e s p u : Level}
         {C : Category o h e}
         (F : Functor C (ContCat s p))
         (X : Set u) where
  private
    module C   = Category C
    module F   = Functor F
    ShapeCat′ : Category (o ⊔ s) (h ⊔ s) e
    ShapeCat′ = ShapeCat C F
  record Unfolding : Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u) where
    field
      -- The unfolding functor: ShapeCat(F) → C
      -- 展开函子：ShapeCat(F) → C
      unfoldFunctor   : Functor ShapeCat′ C
      -- Next-seed assignment: each shape yields a seed in X
      -- 下一层种子赋值：每个形状产生 X 中的一个种子
      unfold-next     : ∀ {A} → ShapeOf F A → X
      -- Position-to-shape map: positions of a shape become shapes of the unfolded object
      -- 位置到形状映射：某形状的位置成为展开后对象的形状
      pos-to-shape    : ∀ {A} (s : ShapeOf F A) → PosOf F s → ShapeOf F (Functor.₀ unfoldFunctor (A , s))
      -- Compatibility: pos-to-shape commutes with the functorial action on shapes/positions
      -- 相容性：pos-to-shape 与形状/位置上的函子作用交换
      pos-actS-compat : ∀ {A B} (f : A C.⇒ B) (s : ShapeOf F A)
                      → (p : PosOf F (actSOf F f s))
                      → pos-to-shape (actSOf F f s) p
                        ≡ actSOf F (Functor.₁ unfoldFunctor (f , refl))
                                 (pos-to-shape s (actPOf F f s p))
  open Unfolding public

-- Functorial action on unfoldings: map the seed set along a function X → Y
-- 展开上的函子作用：沿函数 X → Y 映射种子集
mapUnfolding : ∀ {o h e s p u v} {C : Category o h e} {F : Functor C (ContCat s p)} {X : Set u} {Y : Set v}
             → (X → Y) → Unfolding F X → Unfolding F Y
mapUnfolding f u = record
  { unfoldFunctor   = unfoldFunctor u
  ; unfold-next     = λ s → f (unfold-next u s)
  ; pos-to-shape    = pos-to-shape u
  ; pos-actS-compat = pos-actS-compat u
  }
-- Identity law: mapUnfolding id u ≡ u
-- 恒等律：mapUnfolding id u ≡ u
mapUnfolding-id : ∀ {o h e s p u} {C : Category o h e} {F : Functor C (ContCat s p)} {X : Set u}
                 (u : Unfolding F X) → mapUnfolding id u ≡ u
mapUnfolding-id u = refl
-- Composition law: mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
-- 复合律：mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
mapUnfolding-∘ : ∀ {o h e s p u v w}
                   {C : Category o h e}
                   {F : Functor C (ContCat s p)}
                   {X : Set u} {Y : Set v} {Z : Set w}
                   (f : Y → Z) (g : X → Y)
                   (u : Unfolding F X)
               → mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
mapUnfolding-∘ f g u = refl

-- Setoid structure for unfoldings
-- 展开的集合（Setoid）结构
module UnfoldingSetoid {o h e s p u : Level}
                       {C : Category o h e}
                       {F : Functor C (ContCat s p)} where
  private
    module C = Category C
    module F = Functor F
    ShapeOf′ = ShapeOf F
    PosOf′   = PosOf F
  -- Equivalence on unfoldings: equal unfolding functors, compatible pos-to-shape,
  -- and pointwise equivalent next-seed assignments
  -- 展开上的等价关系：展开函子相等，pos-to-shape 相容，
  -- 下一层种子赋值逐点等价
  record _≈U_ {X : Setoid u u}
              (u₁ u₂ : Unfolding F (Setoid.Carrier X))
              : Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u) where
    private
      module X  = Setoid X
      module U₁ = Unfolding u₁
      module U₂ = Unfolding u₂
    field
      -- The unfolding functors are propositionally equal
      -- 展开函子取命题相等
      unfoldFunctor-eq : U₁.unfoldFunctor ≡ U₂.unfoldFunctor
      -- pos-to-shape agrees after transporting along unfoldFunctor-eq
      -- pos-to-shape 在沿 unfoldFunctor-eq 传输后一致
      pos-to-shape-eq  : ∀ {A} (s : ShapeOf′ A) (p : PosOf′ s)
                       → subst (λ G → ShapeOf′ (Functor.₀ G (A , s)))
                                unfoldFunctor-eq
                                (U₁.pos-to-shape s p)
                       ≡ U₂.pos-to-shape s p
      -- Next-seed assignments are pointwise equivalent in X
      -- 下一层种子赋值在 X 中逐点等价
      unfold-next-eq   : ∀ {A} (s : ShapeOf′ A)
                       → X._≈_ (U₁.unfold-next s) (U₂.unfold-next s)

  -- Reflexivity of _≈U_
  -- _≈U_ 的自反性
  ≈U-refl : {X : Setoid u u} → Reflexive (_≈U_ {X})
  ≈U-refl {X = X} = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ _ _ → refl
    ; unfold-next-eq   = λ _ → Setoid.refl X
    }
  -- Symmetry of _≈U_
  -- _≈U_ 的对称性
  ≈U-sym : (X : Setoid u u) → Symmetric (_≈U_ {X})
  ≈U-sym X (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts ; unfold-next-eq = un })
    = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ s p → sym (pts s p)
    ; unfold-next-eq   = λ s → Setoid.sym X (un s)
    }
  -- Transitivity of _≈U_
  -- _≈U_ 的传递性
  ≈U-trans : (X : Setoid u u) → Transitive (_≈U_ {X})
  ≈U-trans X (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts₁ ; unfold-next-eq = un₁ })
             (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts₂ ; unfold-next-eq = un₂ })
    = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ s p → trans (pts₁ s p) (pts₂ s p)
    ; unfold-next-eq   = λ s → Setoid.trans X (un₁ s) (un₂ s)
    }

  -- Assemble the setoid of unfoldings over a given setoid X
  -- 组装给定集合 X 上的展开 Setoid
  unfoldingSetoid : Setoid u u → Setoid (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
                                        (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
  unfoldingSetoid X = record
    { Carrier       = Unfolding F (Setoid.Carrier X)
    ; _≈_           = _≈U_ {X}
    ; isEquivalence = record
      { refl  = ≈U-refl {X}
      ; sym   = ≈U-sym X
      ; trans = ≈U-trans X
      }
    }

  -- mapUnfolding respects setoid equivalence: lifts Func X Y to Func (Unf X) (Unf Y)
  -- mapUnfolding 保持集合等价：将 Func X Y 提升为 Func (Unf X) (Unf Y)
  mapUnfolding-resp : (X Y : Setoid u u)
                    → Func X Y
                    → Func (unfoldingSetoid X) (unfoldingSetoid Y)
  mapUnfolding-resp X Y f = record
    { to   = λ u → mapUnfolding (Func.to f) u
    ; cong = λ {u₁ u₂} eq → helper eq
    }
    where
      module X = Setoid X
      module Y = Setoid Y
      helper : {u₁ u₂ : Unfolding F (Setoid.Carrier X)}
             → _≈U_ {X} u₁ u₂
             → _≈U_ {Y} (mapUnfolding (Func.to f) u₁) (mapUnfolding (Func.to f) u₂)
      helper (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts ; unfold-next-eq = un })
        = record
        { unfoldFunctor-eq = refl
        ; pos-to-shape-eq  = λ s p → pts s p
        ; unfold-next-eq   = λ s → Func.cong f (un s)
        }

  -- Pointwise version: if f ≈ g pointwise and u₁ _≈U_ u₂, then mapUnfolding f u₁ _≈U_ mapUnfolding g u₂
  -- 逐点版本：若 f ≈ g 逐点成立且 u₁ _≈U_ u₂，则 mapUnfolding f u₁ _≈U_ mapUnfolding g u₂
  mapUnfolding-resp-≈ : (A B : Set u)
                      (f g : A → B)
                      → (∀ {x} → f x ≡ g x)
                      → {u₁ u₂ : Unfolding F A}
                      → _≈U_ {setoid A} u₁ u₂
                      → _≈U_ {setoid B} (mapUnfolding f u₁) (mapUnfolding g u₂)
  mapUnfolding-resp-≈ A B f g f≈g {u₁} {u₂} u₁≈u₂ =
    let
      SA = setoid A
      SB = setoid B
      sf : Func SA SB
      sf = record { to = f ; cong = cong f }
      module R = Func (mapUnfolding-resp SA SB sf)
      fg-eq : _≈U_ {SB} (mapUnfolding f u₂) (mapUnfolding g u₂)
      fg-eq = record
        { unfoldFunctor-eq = refl
        ; pos-to-shape-eq  = λ s p → refl
        ; unfold-next-eq   = λ s → f≈g {unfold-next u₂ s}
        }
      module SBS = Setoid (unfoldingSetoid SB)
    in SBS.trans (R.cong u₁≈u₂) fg-eq
