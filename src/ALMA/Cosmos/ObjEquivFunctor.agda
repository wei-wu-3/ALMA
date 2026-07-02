------------------------------------------------------------------------
-- Functors between categories with object equivalence
--
-- Preserve object equivalence and commute with transport. Includes
-- composition and a constructor from ordinary functors via isomorphisms
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ObjEquivFunctor where

open import Agda.Primitive using (_⊔_; Level)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)

open import ALMA.Cosmos.Iso
open import ALMA.Cosmos.ObjEquivCat

-- ObjEquivFunctor: functor between categories with object equivalence
record ObjEquivFunctor {o ℓ e : Level} (C D : ObjEquivCat o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private
    module C = ObjEquivCat C
    module D = ObjEquivCat D
  field
    baseFunctor : Functor C.cat D.cat
  module BF = Functor baseFunctor
  field
    ≈ₒ-homo : ∀ {A B : Category.Obj C.cat}
            → A C.≈ₒ B → BF.₀ A D.≈ₒ BF.₀ B
    transport-comm : ∀ {A₁ A₂ B₁ B₂ : Category.Obj C.cat}
                     (eqA : A₁ C.≈ₒ A₂) (eqB : B₁ C.≈ₒ B₂)
                     {f : Category._⇒_ C.cat A₁ B₁}
                   → Category._≈_ D.cat
                       (D.transport (≈ₒ-homo eqA) (≈ₒ-homo eqB) (BF.₁ f))
                       (BF.₁ (C.transport eqA eqB f))

-- Composition of ObjEquivFunctors
compObjEquivFunctor : ∀ {o ℓ e} {C D E : ObjEquivCat o ℓ e}
  → ObjEquivFunctor D E → ObjEquivFunctor C D → ObjEquivFunctor C E
compObjEquivFunctor {C = C} {D} {E} G F = record
  { baseFunctor    = G.baseFunctor ∘F F.baseFunctor
  ; ≈ₒ-homo        = λ eq → G.≈ₒ-homo (F.≈ₒ-homo eq)
  ; transport-comm = λ eqA eqB {f} →
      let
        module EC = Category (ObjEquivCat.cat E)
        open EC
        open Equiv
      in
      trans
        (G.transport-comm (F.≈ₒ-homo eqA) (F.≈ₒ-homo eqB) {f = F.BF.₁ f})
        (Functor.F-resp-≈ G.baseFunctor (F.transport-comm eqA eqB {f = f}))
  }
  where
    module F = ObjEquivFunctor F
    module G = ObjEquivFunctor G

-- Constructor from an ordinary functor (using isomorphisms as object equivalence)
module _ {o ℓ e : Level} {C D : Category o ℓ e} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module IsoC = Iso C
    module IsoD = Iso D
    CE = objEquivCatFromIso C
    DE = objEquivCatFromIso D
    module CE = ObjEquivCat CE
    module DE = ObjEquivCat DE
  -- Functor F lifts isomorphisms in C to isomorphisms in D
  F-iso : ∀ {A B} → IsoC._≅_ A B → IsoD._≅_ (F.₀ A) (F.₀ B)
  F-iso i = IsoD.iso (F.₁ (IsoC.to i)) (F.₁ (IsoC.from i))
    (trans (D.Equiv.sym F.homomorphism) (trans (F.F-resp-≈ (IsoC.isoˡ i)) F.identity))
    (trans (D.Equiv.sym F.homomorphism) (trans (F.F-resp-≈ (IsoC.isoʳ i)) F.identity))
    where open D.Equiv

  -- Main constructor
  objEquivFunctorFromIso : ObjEquivFunctor CE DE
  objEquivFunctorFromIso = record
    { baseFunctor    = F
    ; ≈ₒ-homo        = F-iso
    ; transport-comm = λ eqA eqB {f} →
        let
          open D
          open Equiv
          t  = IsoC.to eqB
          fr = IsoC.from eqA
        in
        trans (sym (assoc {f = F.₁ fr} {g = F.₁ f} {h = F.₁ t}))
        (trans (∘-resp-≈ˡ (sym (F.homomorphism {f = f} {g = t})))
        (trans (sym (F.homomorphism {f = fr} {g = t C.∘ f})) (F.F-resp-≈ C.assoc)))
    }
