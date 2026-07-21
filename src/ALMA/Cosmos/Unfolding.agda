------------------------------------------------------------------------
-- Unfolding Functor Record
--
-- Defines the unfolding functor for a cosmos layer, mapping shaped objects to
-- the base category with seeds for the next universe
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Unfolding where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; setoid)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (_,_)
open import Data.Container.Core using (Container)
open import Function using (Func; id; _∘_)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Construction.Elements using (Elements)
open import Categories.Functor using (Functor; _∘F_)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv
  using (ContCatEquiv; ShapeCat; module ContCatEquiv)
open import ALMA.Cosmos.ContCategoryLemmas
  using (shape-eq-from-≈M; ShapeOf; PosOf; actSOf; actPOf)

-- Unfolding for a cosmos layer
module _ {o h e s p u : Level}
         {C : Category o h e}
         (F : Functor C (ContCat s p))
         (X : Set u) where
  private
    module C   = Category C
    module F   = Functor F
    ShapeCat′ : Category (o ⊔ s) (h ⊔ s) e
    ShapeCat′ = ShapeCat C F
  record Unfolding : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)) where
    field
      unfoldFunctor   : Functor ShapeCat′ C
      unfold-next     : ∀ {A} → ShapeOf F A → X
      pos-to-shape    : ∀ {A} (s : ShapeOf F A) → PosOf F s → ShapeOf F (Functor.₀ unfoldFunctor (A , s))
      pos-actS-compat : ∀ {A B} (f : A C.⇒ B) (s : ShapeOf F A)
                      → (p : PosOf F (actSOf F f s))
                      → pos-to-shape (actSOf F f s) p
                        ≡ actSOf F (Functor.₁ unfoldFunctor (f , refl))
                                 (pos-to-shape s (actPOf F f s p))
  open Unfolding public

-- Functorial action on unfoldings
mapUnfolding : ∀ {o h e s p u v} {C : Category o h e} {F : Functor C (ContCat s p)} {X : Set u} {Y : Set v}
             → (X → Y) → Unfolding F X → Unfolding F Y
mapUnfolding f u = record
  { unfoldFunctor   = unfoldFunctor u
  ; unfold-next     = λ s → f (unfold-next u s)
  ; pos-to-shape    = pos-to-shape u
  ; pos-actS-compat = pos-actS-compat u
  }
mapUnfolding-id : ∀ {o h e s p u} {C : Category o h e} {F : Functor C (ContCat s p)} {X : Set u}
                 (u : Unfolding F X) → mapUnfolding id u ≡ u
mapUnfolding-id u = refl
mapUnfolding-∘ : ∀ {o h e s p u v w} {C : Category o h e} {F : Functor C (ContCat s p)}
                   {X : Set u} {Y : Set v} {Z : Set w}
                   {f : Y → Z} {g : X → Y} (u : Unfolding F X)
                 → mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
mapUnfolding-∘ u = refl

-- Setoid structure for unfoldings
module UnfoldingSetoid {o h e s p u : Level}
                       {C : Category o h e}
                       {F : Functor C (ContCat s p)} where
  private
    module C = Category C
    module F = Functor F
    ShapeOf′ = ShapeOf F
    PosOf′   = PosOf F
  record _≈U_ {X : Setoid u u}
              (u₁ u₂ : Unfolding F (Setoid.Carrier X))
              : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)) where
    private
      module X  = Setoid X
      module U₁ = Unfolding u₁
      module U₂ = Unfolding u₂
    field
      unfoldFunctor-eq : U₁.unfoldFunctor ≡ U₂.unfoldFunctor
      pos-to-shape-eq  : ∀ {A} (s : ShapeOf′ A) (p : PosOf′ s)
                       → subst (λ G → ShapeOf′ (Functor.₀ G (A , s)))
                                unfoldFunctor-eq
                                (U₁.pos-to-shape s p)
                       ≡ U₂.pos-to-shape s p
      unfold-next-eq   : ∀ {A} (s : ShapeOf′ A)
                       → X._≈_ (U₁.unfold-next s) (U₂.unfold-next s)

  ≈U-refl : {X : Setoid u u} → Reflexive (_≈U_ {X})
  ≈U-refl {X = X} = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ _ _ → refl
    ; unfold-next-eq   = λ _ → Setoid.refl X
    }
  ≈U-sym : (X : Setoid u u) → Symmetric (_≈U_ {X})
  ≈U-sym X (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts ; unfold-next-eq = un })
    = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ s p → sym (pts s p)
    ; unfold-next-eq   = λ s → Setoid.sym X (un s)
    }
  ≈U-trans : (X : Setoid u u) → Transitive (_≈U_ {X})
  ≈U-trans X (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts₁ ; unfold-next-eq = un₁ })
             (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts₂ ; unfold-next-eq = un₂ })
    = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ s p → trans (pts₁ s p) (pts₂ s p)
    ; unfold-next-eq   = λ s → Setoid.trans X (un₁ s) (un₂ s)
    }

  unfoldingSetoid : Setoid u u → Setoid (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u))
                                        (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u))
  unfoldingSetoid X = record
    { Carrier       = Unfolding F (Setoid.Carrier X)
    ; _≈_           = _≈U_ {X}
    ; isEquivalence = record
      { refl  = ≈U-refl {X}
      ; sym   = ≈U-sym X
      ; trans = ≈U-trans X
      }
    }

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
