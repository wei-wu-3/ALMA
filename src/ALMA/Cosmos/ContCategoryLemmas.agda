------------------------------------------------------------------------
-- Container morphism equivalence lemmas and container functor basics
-- 容器态射等价引理与容器函子基础投影
--
-- shape-level laws for ≈M (sym, trans, assoc, whiskering) and
-- basic container functor projections (ShapeOf, PosOf, actSOf, actPOf)
-- ≈M 的形状层代数律（对称、传递、结合、削）
-- 及容器函子的基本投影（ShapeOf、PosOf、actSOf、actPOf）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCategoryLemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (trans-reflʳ)
open import Data.Container.Core using (Container; shape; position; _⇒_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory
  using (_≈M_; ≈M-sym; ≈M-trans; ∘M-assoc; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ; ContCat)

-- Basic ≈M operations
-- ≈M 的基本操作

-- Extract the shape-level equality from an ≈M proof
-- 从 ≈M 证明中提取形状层的等式
shape-eq-from-≈M : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
                  → f ≈M g → ∀ x → _⇒_.shape f x ≡ _⇒_.shape g x
shape-eq-from-≈M eq x = let open _≈M_ eq in shape-eq x

-- ≈M algebraic laws (shape layer)
-- ≈M 的代数律（形状层）

-- Shape component of ≈M-sym equals pointwise sym of the shape component
-- ≈M-sym 的形状分量等于形状分量的逐点对称
shape-eq-sym : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
              → (eq : f ≈M g) (x : Container.Shape C)
              → shape-eq-from-≈M (≈M-sym eq) x ≡ sym (shape-eq-from-≈M eq x)
shape-eq-sym _ _ = refl
-- Shape component of ≈M-trans equals pointwise trans of the shape components
-- ≈M-trans 的形状分量等于形状分量的逐点传递
shape-eq-trans : ∀ {s p} {C D : Container s p} {f g h : C ⇒ D}
                → (eq1 : f ≈M g) (eq2 : g ≈M h) (x : Container.Shape C)
                → shape-eq-from-≈M (≈M-trans eq1 eq2) x
                  ≡ trans (shape-eq-from-≈M eq1 x) (shape-eq-from-≈M eq2 x)
shape-eq-trans _ _ _ = refl
-- Shape component of ∘M-assoc is definitionally refl
-- ∘M-assoc 的形状分量在定义上即为 refl
shape-eq-assoc : ∀ {s p} {A B C D : Container s p}
              → {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
              → (x : Container.Shape A)
              → shape-eq-from-≈M (∘M-assoc {A = A} {B} {C} {D} {f} {g} {h}) x ≡ refl
shape-eq-assoc _ = refl
-- Shape component respects left whiskering: precomposition with f
-- 形状分量关于左削（与 f 的前复合）的相容性
shape-eq-resp-ˡ : ∀ {s p} {A B C : Container s p}
                  → {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
                  → (eq : g₁ ≈M g₂) (x : Container.Shape A)
                  → shape-eq-from-≈M (∘M-resp-≈ˡ {f = f} eq) x
                    ≡ shape-eq-from-≈M eq (_⇒_.shape f x)
shape-eq-resp-ˡ {f = f} eq x = trans-reflʳ (shape-eq-from-≈M eq (_⇒_.shape f x))
-- Shape component respects right whiskering: postcomposition with g
-- 形状分量关于右削（与 g 的后复合）的相容性
shape-eq-resp-ʳ : ∀ {s p} {A B C : Container s p}
                → {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
                → (eq : f₁ ≈M f₂) (x : Container.Shape A)
                → shape-eq-from-≈M (∘M-resp-≈ʳ {g = g} eq) x
                  ≡ cong (shape g) (shape-eq-from-≈M eq x)
shape-eq-resp-ʳ _ _ = refl

-- Container functor helpers
-- 容器函子辅助投影

-- Shape set of a container-valued functor F at object A
-- 容器值函子 F 在对象 A 处的形状集
ShapeOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → Functor C (ContCat s p) → Category.Obj C → Set s
ShapeOf F A = Container.Shape (Functor.₀ F A)
-- Position set of a container-valued functor F at shape s
-- 容器值函子 F 在形状 s 处的位置集
PosOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
      → (F : Functor C (ContCat s p)) {A : Category.Obj C}
      → ShapeOf F A → Set p
PosOf F {A} s = Container.Position (Functor.₀ F A) s
-- Action of a container-valued functor on shapes
-- 容器值函子在形状上的作用
actSOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → Category._⇒_ C A B → ShapeOf F A → ShapeOf F B
actSOf F f = shape (Functor.₁ F f)
-- Action of a container-valued functor on positions (contravariant in shape)
-- 容器值函子在位置上的作用（关于形状反变）
actPOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → (f : Category._⇒_ C A B) (s : ShapeOf F A)
        → PosOf F (actSOf F f s) → PosOf F s
actPOf F f s = position (Functor.₁ F f) {s}
