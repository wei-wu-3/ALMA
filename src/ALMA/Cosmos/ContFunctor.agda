------------------------------------------------------------------------
-- Containers as polynomial functors on Setoids
--
-- Builds functor ⟦ C ⟧ and embedding ContCat → [Setoids, Setoids]
-- Proves preservation of identity, composition, and the equivalence _≈M_
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContFunctor where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (refl; cong)
open import Relation.Binary using (Setoid)
open import Function using (Func; _∘_)
open import Data.Product using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; map)
open import Data.Container.Morphism renaming (id to idCont; _∘_ to _∘Cont_)
open import Data.Container.Relation.Binary.Equality.Setoid using (setoid)
open import Data.Container.Relation.Binary.Pointwise as PW using (_,_)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; id; _∘ᵥ_; ntHelper)

open import ALMA.Cosmos.ContCategory using (_≈M_; ContCat)

module _ {s p ℓ′} where
  record ContFunctor (C : Container s p) : Set (lsuc (s ⊔ p ⊔ ℓ′)) where
    private
      module Src = Category (Setoids ℓ′ ℓ′) renaming
        ( id to idS ; _∘_ to _∘S_ ; _⇒_ to _⇒S_ ; _≈_ to _≈S_ )
      module Tgt = Category (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)) renaming
        ( id to idT ; _∘_ to _∘T_ ; _⇒_ to _⇒T_ ; _≈_ to _≈T_ )
    ⟦_⟧ₛ : Setoid ℓ′ ℓ′ → Setoid (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)
    ⟦_⟧ₛ A = setoid A C
    mapₛ : {A B : Setoid ℓ′ ℓ′} → A Src.⇒S B → ⟦ A ⟧ₛ Tgt.⇒T ⟦ B ⟧ₛ
    mapₛ {A} {B} f = record
      { to   = map {C = C} {X = Setoid.Carrier A} {Y = Setoid.Carrier B} (Func.to f)
      ; cong = λ { (sh , ps) → sh , λ p → Func.cong f (ps p) }
      }
    map-id≗ : {A : Setoid ℓ′ ℓ′} → mapₛ (Src.idS {A}) Tgt.≈T Tgt.idT {A = ⟦_⟧ₛ A}
    map-id≗ {A} {x = (s , h)} =
      refl PW., λ p → Setoid.refl A {x = h p}
    map-∘≗ : {A B D : Setoid ℓ′ ℓ′} {f : A Src.⇒S B} {g : B Src.⇒S D} →
             mapₛ (g Src.∘S f) Tgt.≈T (mapₛ g Tgt.∘T mapₛ f)
    map-∘≗ {A} {B} {D} {f = f} {g = g} {x = (s , h)} =
      refl PW., λ p → Setoid.refl D {x = Func.to g (Func.to f (h p))}
    map-resp-≗ : {A B : Setoid ℓ′ ℓ′} {f g : A Src.⇒S B} →
                 f Src.≈S g → mapₛ f Tgt.≈T mapₛ g
    map-resp-≗ {A} {B} {f} {g} f≈g {x = (s , h)} =
      refl PW., λ p → f≈g {x = h p}
    functor : Functor (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′))
    functor = record
      { F₀           = ⟦_⟧ₛ
      ; F₁           = mapₛ
      ; identity     = λ {A} → map-id≗ {A = A}
      ; homomorphism = λ {A} {B} {D} {f} {g} → map-∘≗ {A = A} {B = B} {D = D} {f = f} {g = g}
      ; F-resp-≈     = λ {A} {B} {f} {g} f≈g → map-resp-≗ {A = A} {B = B} {f = f} {g = g} f≈g
      }

  private
    module FuncCat = Category (Functors (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)))
  ⟦_⟧ : Container s p → Functor (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′))
  ⟦ C ⟧ = ContFunctor.functor {C = C} (record {})
  mapNT : {C D : Container s p} → (C ⇒ D) → NaturalTransformation ⟦ C ⟧ ⟦ D ⟧
  mapNT {C} {D} m = ntHelper record
    { η = λ X → record
      { to   = λ { (s , k) → let open _⇒_ m in (shape s , k ∘ position) }
      ; cong = λ { (refl PW., eq) → let open _⇒_ m in refl PW., λ p → eq (position p) }
      }
    ; commute = λ {X Y} f {x} →
        let open _⇒_ m
            (s , k) = x
        in refl PW., λ p → Setoid.refl Y {x = Func.to f (k (position p))}
    }
  mapNT-id : {C : Container s p}
           → mapNT (idCont C) FuncCat.≈ id
  mapNT-id {C} {X} {x = (s , k)} =
    refl PW., λ p → Setoid.refl X {x = k p}
  mapNT-∘ : {C D E : Container s p} {m : D ⇒ E} {n : C ⇒ D}
          → mapNT (m ∘Cont n) FuncCat.≈ (mapNT m ∘ᵥ mapNT n)
  mapNT-∘ {C} {D} {E} {m} {n} {X} {x = (s , k)} =
    refl PW., λ p → Setoid.refl X
  mapNT-resp-≈ : {C D : Container s p} {m n : C ⇒ D}
               → m ≈M n → mapNT m FuncCat.≈ mapNT n
  mapNT-resp-≈ {C} {D} {m} {n} eq {X} {x = (s , k)} =
    eq.shape-eq s PW., λ q → Setoid.reflexive X (cong k (eq.pos-eq s q))
    where module eq = _≈M_ eq
  ContEmbedding : Functor (ContCat s p) (Functors (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)))
  ContEmbedding = record
    { F₀        = ⟦_⟧
    ; F₁        = mapNT
    ; identity  = λ {A} {X} {x} → mapNT-id {C = A} {X} {x}
    ; homomorphism = λ {X Y Z f g} {S} {x} → mapNT-∘ {m = g} {n = f} {S} {x}
    ; F-resp-≈  = λ {A B f g} eq {X} {x} → mapNT-resp-≈ eq {X} {x}
    }
