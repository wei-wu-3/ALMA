------------------------------------------------------------------------
-- Proves substitution–commutation for position maps, and sequential
-- (vertical) commutativity of shape components under composition of
-- natural transformations valued in ContCat
-- 证明位置映射与替换的交换性，以及取值于 ContCat 的自然变换
-- 在纵复合下形状分量的顺序交换性
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCatEquivLemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Product.Base using (proj₂)
open import Data.Container.Core using (shape)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; _∘ᵥ_)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (shape-eq-from-≈M; ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos.MorphismObject using (MorphismObject)

-- Substitution commutes with the position map of a MorphismObject:
-- applying onPos after substituting along a shape equality in the source
-- equals substituting along the induced shape equality in the target
-- after applying onPos
-- 替换与 MorphismObject 的位置映射交换：
-- 在源端沿形状等式替换后再施加 onPos，
-- 等于先施加 onPos 再在目标端沿诱导的形状等式替换
onPos-subst-comm :
  ∀ {o h e o′ ℓ′ e′ s p u v}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {X : Set u} {Y : Set v}
    {UF : Unfolding FC X} {UG : Unfolding FD Y}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {shapeTrans : ∀ {A} {s : ShapeOf FC A}
                → PosOf FC s
                → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG)
                                        (Functor.₀ S (A , s)))}
    (MO : MorphismObject UF UG S shapeTrans)
    {A : Category.Obj C}
    {s₁ s₂ : ShapeOf FC A}
    (eq : s₁ ≡ s₂)
    (p : PosOf FC s₁)
  → MorphismObject.onPos MO (subst (PosOf FC) eq p)
    ≡ subst (λ s → PosOf FD (proj₂ (Functor.₀ S (A , s))))
            eq
            (MorphismObject.onPos MO p)
onPos-subst-comm MO refl p = refl

-- Sequential (vertical) commutativity of shape components under composition
-- for two composable natural transformations α : G ⟹ H and β : F ⟹ G:
-- the shape component of α ∘ᵥ β satisfies the naturality square with
-- respect to any morphism f : A → B in the source category
-- 两个可复合自然变换 α : G ⟹ H 与 β : F ⟹ G 的形状映射的
-- 顺序（纵向）交换性：α ∘ᵥ β 的形状分量关于源范畴中
-- 任意态射 f : A → B 满足自然性方块
glue-shape-eq :
  ∀ {o h e s p}
    {C : Category o h e}
    {F G H : Functor C (ContCat s p)}
    {α : NaturalTransformation G H} {β : NaturalTransformation F G}
    {A B : Category.Obj C} (f : Category._⇒_ C A B)
    (s : ShapeOf F A)
  → shape (NaturalTransformation.η (α ∘ᵥ β) B)
          (shape (Functor.F₁ F f) s)
    ≡ shape (Functor.F₁ H f)
            (shape (NaturalTransformation.η (α ∘ᵥ β) A) s)
glue-shape-eq {F = F} {G} {H} {α = α} {β = β} {A = A} {B = B} f s =
  let open ≡-Reasoning in
  begin
    shape (NTα.η B) (shape (NTβ.η B) (shape (F.F₁ f) s))
      ≡⟨ cong (shape (NTα.η B))
              (shape-eq-from-≈M (NTβ.commute f) s) ⟩
    shape (NTα.η B) (shape (G.F₁ f) (shape (NTβ.η A) s))
      ≡⟨ shape-eq-from-≈M (NTα.commute f)
                          (shape (NTβ.η A) s) ⟩
    shape (H.F₁ f) (shape (NTα.η A) (shape (NTβ.η A) s))
    ∎
  where
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module NTα = NaturalTransformation α
    module NTβ = NaturalTransformation β

-- Sequential (vertical) commutativity for three composable natural
-- transformations α : H ⟹ I, β : G ⟹ H, γ : F ⟹ G:
-- the shape component of α ∘ᵥ β ∘ᵥ γ satisfies the naturality square
-- The proof factors β ∘ᵥ γ via glue-shape-eq, then applies naturality of α
-- 三个可复合自然变换 α : H ⟹ I、β : G ⟹ H、γ : F ⟹ G 的
-- 顺序（纵向）交换性：α ∘ᵥ β ∘ᵥ γ 的形状分量满足自然性方块
-- 证明先经 glue-shape-eq 分解 β ∘ᵥ γ，再施加 α 的自然性
comp-nat-shape-eq :
  ∀ {o h e s p}
    {C : Category o h e}
    {F G H I : Functor C (ContCat s p)}
    {α : NaturalTransformation H I}
    {β : NaturalTransformation G H}
    {γ : NaturalTransformation F G}
    {A B : Category.Obj C} (f : Category._⇒_ C A B)
    (s : ShapeOf F A)
  → shape (NaturalTransformation.η (α ∘ᵥ β ∘ᵥ γ) B)
          (shape (Functor.F₁ F f) s)
    ≡ shape (Functor.F₁ I f)
            (shape (NaturalTransformation.η (α ∘ᵥ β ∘ᵥ γ) A) s)
comp-nat-shape-eq {F = F} {G} {H} {I} {α = α} {β = β} {γ = γ} {A = A} {B = B} f s =
  let open ≡-Reasoning in
  begin
    shape (NTα.η B) (shape (NTβγ.η B) (shape (F.F₁ f) s))
      ≡⟨ cong (shape (NTα.η B))
              (glue-shape-eq {α = β} {β = γ} f s) ⟩
    shape (NTα.η B) (shape (H.F₁ f) (shape (NTβγ.η A) s))
      ≡⟨ shape-eq-from-≈M (NTα.commute f)
                          (shape (NTβγ.η A) s) ⟩
    shape (I.F₁ f) (shape (NTα.η A) (shape (NTβγ.η A) s))
    ∎
  where
    module F = Functor F
    module H = Functor H
    module I = Functor I
    module NTα = NaturalTransformation α
    βγ = β ∘ᵥ γ
    module NTβγ = NaturalTransformation βγ
