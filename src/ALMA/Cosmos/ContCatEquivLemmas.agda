------------------------------------------------------------------------
-- Lemmas for the refactored Cosmos architecture
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCatEquivLemmas where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; module ≡-Reasoning)
open import Data.Container.Core using (shape)
open import Data.Product using (_,_; proj₂)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.ContCategoryLemmas using (shape-eq-from-≈M; ShapeOf; PosOf)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos.MorphismObject using (MorphismObject)

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

-- Sequential commutativity of shape maps for two composable natural transformations
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

-- Sequential commutativity for three composable natural transformations
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
