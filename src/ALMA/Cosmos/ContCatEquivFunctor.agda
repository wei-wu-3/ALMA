------------------------------------------------------------------------
-- ContCatEquivFunctor: morphism between ContCatEquiv instances
--
-- Combines an ObjEquivFunctor with a container natural transformation
-- contCatEquivFunctorFromIso: constructor using objEquivFunctorFromIso + a natural transformation
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCatEquivFunctor where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Category using (Category)
open import Categories.Functor  using (Functor)
open import Data.Container.Core using (_⇒_)
open import Data.Container.Morphism using (id; _∘_)

open import ALMA.Cosmos.Iso
open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ObjEquivFunctor

-- ContCatEquivFunctor record
record ContCatEquivFunctor {ℓ : Level} (F G : ContCatEquiv ℓ) : Set (lsuc ℓ) where
  private
    module FC = ObjEquivCat (ContCatEquiv.base F)
    module GC = ObjEquivCat (ContCatEquiv.base G)
    module F  = ContCatEquiv F
    module G  = ContCatEquiv G
  field
    -- Underlying functor preserving object equivalences
    objEquivFunctor : ObjEquivFunctor F.base G.base
  open ObjEquivFunctor objEquivFunctor
  field
    containerNat : ∀ {A : Category.Obj FC.cat}
                 → Functor.₀ F.containerFunctor A ⇒ Functor.₀ G.containerFunctor (BF.₀ A)
    natural : ∀ {A B : Category.Obj FC.cat}
              (f : Category._⇒_ FC.cat A B)
            → (containerNat ∘ Functor.₁ F.containerFunctor f) ≈M
              (Functor.₁ G.containerFunctor (BF.₁ f) ∘ containerNat)
    transport-nat : ∀ {A₁ A₂ : Category.Obj FC.cat}
                    (eqA : FC._≈ₒ_ A₁ A₂)
                  → (containerNat ∘ F.transportContainer eqA) ≈M
                    (G.transportContainer (≈ₒ-homo eqA) ∘ containerNat)

-- Identity ContCatEquivFunctor
idContCatEquivFunctor : ∀ {ℓ} (C : ContCatEquiv ℓ) → ContCatEquivFunctor C C
idContCatEquivFunctor C = record
  { objEquivFunctor = record
    { baseFunctor    = record
      { F₀           = λ x → x
      ; F₁           = λ f → f
      ; identity     = Cat.Equiv.refl
      ; homomorphism = Cat.Equiv.refl
      ; F-resp-≈     = λ eq → eq
      }
    ; ≈ₒ-homo        = λ eq → eq
    ; transport-comm = λ eqA eqB {f} → OE.transport-resp-≈ eqA eqB (Cat.Equiv.refl {x = f})
    }
  ; containerNat     = λ {A} → id (Fctr.₀ A)
  ; natural          = λ f → ≈M-refl
  ; transport-nat    = λ eqA → ≈M-refl
  }
  where
    module C   = ContCatEquiv C
    module OE  = ObjEquivCat C.base
    module Cat = Category OE.cat
    module Fctr = Functor C.containerFunctor

-- Composition of ContCatEquivFunctors
compContCatEquivFunctor : ∀ {ℓ} {F G H : ContCatEquiv ℓ}
  → ContCatEquivFunctor G H → ContCatEquivFunctor F G → ContCatEquivFunctor F H
compContCatEquivFunctor {ℓ} {F} {G} {H} g f = record
  { objEquivFunctor = compObjEquivFunctor g.objEquivFunctor f.objEquivFunctor
  ; containerNat    = λ {A} → g.containerNat {fobj.₀ A} ∘ f.containerNat {A}
  ; natural         = λ {A B} h →
      let
        fN-A  = f.containerNat {A}
        fN-B  = f.containerNat {B}
        gN-fA = g.containerNat {fobj.₀ A}
        gN-fB = g.containerNat {fobj.₀ B}
        Fh    = fctr.₁ h
        Gfh   = gctr.₁ (fobj.₁ h)
        Hgfh  = hctr.₁ (gobj.₁ (fobj.₁ h))
      in
      ≈M-trans (∘M-assoc {f = Fh} {g = fN-B} {h = gN-fB})
      (≈M-trans (∘M-resp-≈ʳ {g = gN-fB} (f.natural h))
      (≈M-trans (≈M-sym (∘M-assoc {f = fN-A} {g = Gfh} {h = gN-fB}))
      (≈M-trans (∘M-resp-≈ˡ {f = fN-A} (g.natural (fobj.₁ h)))
      (∘M-assoc {f = fN-A} {g = gN-fA} {h = Hgfh}))))
  ; transport-nat   = λ {A₁ A₂} eqA →
      let
        fN-A1  = f.containerNat {A₁}
        fN-A2  = f.containerNat {A₂}
        gN-fA1 = g.containerNat {fobj.₀ A₁}
        gN-fA2 = g.containerNat {fobj.₀ A₂}
        Ft     = F.transportContainer eqA
        Gft    = G.transportContainer (f≈ₒ-homo eqA)
        Hgft   = H.transportContainer (g≈ₒ-homo (f≈ₒ-homo eqA))
      in
      ≈M-trans (∘M-assoc {f = Ft} {g = fN-A2} {h = gN-fA2})
      (≈M-trans (∘M-resp-≈ʳ {g = gN-fA2} (f.transport-nat eqA))
      (≈M-trans (≈M-sym (∘M-assoc {f = fN-A1} {g = Gft} {h = gN-fA2}))
      (≈M-trans (∘M-resp-≈ˡ {f = fN-A1} (g.transport-nat (f≈ₒ-homo eqA)))
      (∘M-assoc {f = fN-A1} {g = gN-fA1} {h = Hgft}))))
  }
  where
    module F = ContCatEquiv F
    module G = ContCatEquiv G
    module H = ContCatEquiv H
    module f = ContCatEquivFunctor f
    module g = ContCatEquivFunctor g
    fctr = F.containerFunctor
    gctr = G.containerFunctor
    hctr = H.containerFunctor
    fobj = ObjEquivFunctor.baseFunctor f.objEquivFunctor
    gobj = ObjEquivFunctor.baseFunctor g.objEquivFunctor
    f≈ₒ-homo = ObjEquivFunctor.≈ₒ-homo f.objEquivFunctor
    g≈ₒ-homo = ObjEquivFunctor.≈ₒ-homo g.objEquivFunctor
    module fobj = Functor fobj
    module gobj = Functor gobj
    module fctr = Functor fctr
    module gctr = Functor gctr
    module hctr = Functor hctr

-- Constructor: functor + natural transformation → ContCatEquivFunctor
module _ {ℓ} {C D : Category (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)}
         (F : Functor C D)
         (FC : Functor C (ContCat (lsuc ℓ) (lsuc ℓ)))
         (FD : Functor D (ContCat (lsuc ℓ) (lsuc ℓ)))
         (α : ∀ {A : Category.Obj C} → Functor.₀ FC A ⇒ Functor.₀ FD (Functor.₀ F A))
         (nat : ∀ {A B} (f : Category._⇒_ C A B)
              → (α ∘ Functor.₁ FC f) ≈M (Functor.₁ FD (Functor.₁ F f) ∘ α))
       where
  private
    F-contEquiv = contCatEquivFromIso C FC
    G-contEquiv = contCatEquivFromIso D FD
    module FE = ContCatEquiv F-contEquiv
    module GE = ContCatEquiv G-contEquiv
    objEquivF  = objEquivFunctorFromIso {C = C} {D} F
  contCatEquivFunctorFromIso : ContCatEquivFunctor F-contEquiv G-contEquiv
  contCatEquivFunctorFromIso = record
    { objEquivFunctor = objEquivF
    ; containerNat    = α
    ; natural         = nat
    ; transport-nat   = λ eqA → nat (Iso.to eqA)
    }
