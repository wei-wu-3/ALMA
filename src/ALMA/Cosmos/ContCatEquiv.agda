------------------------------------------------------------------------
-- Category with object equivalence and a container functor
--
-- Defines ContCatEquiv: an ObjEquivCat equipped with a functor to
-- the container category, and a transport of containers coherent
-- with the object equivalence
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCatEquiv where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (_⇒_)
open import Data.Container.Morphism using (id; _∘_)
open import Relation.Binary using (IsEquivalence)

open import ALMA.Cosmos.Iso
open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCategory

record ContCatEquiv (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    base : ObjEquivCat (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)
  open ObjEquivCat base
  field
    containerFunctor : Functor cat (ContCat (lsuc ℓ) (lsuc ℓ))
    transportContainer : ∀ {A₁ A₂}
                        → A₁ ≈ₒ A₂
                        → Functor.₀ containerFunctor A₁ ⇒ Functor.₀ containerFunctor A₂
    transportContainer-refl : ∀ {A}
                            → transportContainer (IsEquivalence.refl ≈ₒ-isEquiv) ≈M id (Functor.₀ containerFunctor A)
    transportContainer-trans : ∀ {A₁ A₂ A₃}
                              → (eq1 : A₁ ≈ₒ A₂) (eq2 : A₂ ≈ₒ A₃)
                              → transportContainer (IsEquivalence.trans ≈ₒ-isEquiv eq1 eq2)
                                ≈M (transportContainer eq2 ∘ transportContainer eq1)
    act-natural : ∀ {A₁ A₂ B₁ B₂}
                → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂)
                → (f : Category._⇒_ cat A₁ B₁)
                → (transportContainer eqB ∘ Functor.₁ containerFunctor f)
                  ≈M
                  (Functor.₁ containerFunctor (transport eqA eqB f) ∘ transportContainer eqA)

module _ {ℓ : Level}
         (C : Category (lsuc ℓ) (lsuc ℓ) (lsuc ℓ))
         (F : Functor C (ContCat (lsuc ℓ) (lsuc ℓ))) where
  private
    module C = Category C
    module F = Functor F
    open Iso C
    -- Transport of morphisms along isomorphisms (defined as to ∘ f ∘ from)
    transport' : ∀ {A₁ A₂ B₁ B₂} → A₁ ≅ A₂ → B₁ ≅ B₂ → (A₁ C.⇒ B₁) → (A₂ C.⇒ B₂)
    transport' A≅ B≅ f = to B≅ C.∘ f C.∘ from A≅
     -- proofs of ObjEquivCat fields
    transport-resp-≈' : ∀ {A₁ A₂ B₁ B₂}
                      → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂)
                      → ∀ {f g : A₁ C.⇒ B₁}
                      → f C.≈ g → transport' eqA eqB f C.≈ transport' eqA eqB g
    transport-resp-≈' _ _ f≈g = C.∘-resp-≈ʳ (C.∘-resp-≈ˡ f≈g)
    transport-refl' : ∀ {A B} {f : A C.⇒ B}
                    → transport' isoRefl isoRefl f C.≈ f
    transport-refl' = C.Equiv.trans (C.∘-resp-≈ʳ C.identityʳ) C.identityˡ
    transport-trans' : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                     → (eqA₁ : A₁ ≅ A₂) (eqA₂ : A₂ ≅ A₃)
                     → (eqB₁ : B₁ ≅ B₂) (eqB₂ : B₂ ≅ B₃)
                     → {f : A₁ C.⇒ B₁}
                     → transport' (isoTrans eqA₁ eqA₂) (isoTrans eqB₁ eqB₂) f
                       C.≈ transport' eqA₂ eqB₂ (transport' eqA₁ eqB₁ f)
    transport-trans' eqA₁ eqA₂ eqB₁ eqB₂ {f} =
      C.Equiv.trans C.assoc (C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc))
                               (C.∘-resp-≈ʳ C.sym-assoc))
    transport-∘' : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
                 → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂) (eqC : C₁ ≅ C₂)
                 → (f : A₁ C.⇒ B₁) (g : B₁ C.⇒ C₁)
                 → transport' eqB eqC g C.∘ transport' eqA eqB f
                   C.≈ transport' eqA eqC (g C.∘ f)
    transport-∘' eqA eqB eqC f g =
      C.Equiv.trans (C.∘-resp-≈ˡ C.sym-assoc)
      (C.Equiv.trans C.assoc
      (C.Equiv.trans (C.∘-resp-≈ʳ C.sym-assoc)
      (C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (isoˡ eqB)))
      (C.Equiv.trans (C.∘-resp-≈ʳ C.identityˡ)
      (C.Equiv.trans C.assoc
      (C.∘-resp-≈ʳ C.sym-assoc))))))
    transport-id' : ∀ {A B} (eqA : A ≅ B)
                  → transport' eqA eqA (C.id {A}) C.≈ C.id {B}
    transport-id' eqA = C.Equiv.trans (C.∘-resp-≈ʳ C.identityˡ) (isoʳ eqA)
    -- Construct an ObjEquivCat instance using isomorphisms
    isoObjEquiv : ObjEquivCat (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)
    isoObjEquiv = record
      { cat              = C
      ; _≈ₒ_             = _≅_
      ; ≈ₒ-isEquiv       = isoEquiv
      ; transport        = transport'
      ; transport-resp-≈ = transport-resp-≈'
      ; transport-refl   = transport-refl'
      ; transport-trans  = transport-trans'
      ; transport-∘      = transport-∘'
      ; transport-id     = transport-id'
      }
    open ObjEquivCat isoObjEquiv
    -- Container transport via functor action on "to"
    transportContainer : ∀ {A₁ A₂} → A₁ ≈ₒ A₂ → F.₀ A₁ ⇒ F.₀ A₂
    transportContainer eq = F.₁ (to eq)
    -- Proofs of container transport properties
    transportContainer-refl : ∀ {A}
      → transportContainer (IsEquivalence.refl ≈ₒ-isEquiv {A}) ≈M id (F.₀ A)
    transportContainer-refl = F.identity
    transportContainer-trans : ∀ {A₁ A₂ A₃}
      → (eq1 : A₁ ≈ₒ A₂) (eq2 : A₂ ≈ₒ A₃)
      → transportContainer (IsEquivalence.trans ≈ₒ-isEquiv eq1 eq2)
        ≈M (transportContainer eq2 ∘ transportContainer eq1)
    transportContainer-trans eq1 eq2 = F.homomorphism
    -- The crucial naturality proof, with explicit expansion of transport
    act-natural : ∀ {A₁ A₂ B₁ B₂}
                → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂)
                → (f : C._⇒_ A₁ B₁)
                → (transportContainer eqB ∘ F.₁ f)
                  ≈M
                  (F.₁ (transport eqA eqB f) ∘ transportContainer eqA)
    act-natural {A₁} {A₂} {B₁} {B₂} eqA eqB f =
      let
        X = F.₀ A₁
        Y = F.₀ A₂
        Z = F.₀ B₁
        W = F.₀ B₂
        Ff : X ⇒ Z
        Ff = F.₁ f
        Ffrom : Y ⇒ X
        Ffrom = F.₁ (from eqA)
        Fto : X ⇒ Y
        Fto = F.₁ (to eqA)
        g' = f C.∘ from eqA
        h' = to eqB C.∘ g'
        Ft : Z ⇒ W
        Ft = transportContainer eqB
        L : X ⇒ W
        L = Ft ∘ Ff
        Fh' : Y ⇒ W
        Fh' = F.₁ h'
        R : X ⇒ W
        R = Fh' ∘ Fto
        open Functor F
        -- F preserves the isomorphism condition: F(from) ∘ F(to) ≈ id
        isoCond : Ffrom ∘ Fto ≈M id X
        isoCond = ≈M-trans (≈M-sym (homomorphism {f = to eqA} {g = from eqA}))
                          (≈M-trans (F-resp-≈ (isoˡ eqA)) identity)
        step1 : R ≈M Fh' ∘ Fto
        step1 = ≈M-refl
        step2 : Fh' ≈M Ft ∘ F.₁ g'
        step2 = homomorphism {f = g'} {g = to eqB}
        step3 : Fh' ∘ Fto ≈M (Ft ∘ F.₁ g') ∘ Fto
        step3 = ∘M-resp-≈ step2 (≈M-refl {f = Fto})
        step4 : (Ft ∘ F.₁ g') ∘ Fto ≈M Ft ∘ (F.₁ g' ∘ Fto)
        step4 = ∘M-assoc {A = X} {B = Y} {C = Z} {D = W}
                         {f = Fto} {g = F.₁ g'} {h = Ft}
        step5 : F.₁ g' ≈M Ff ∘ Ffrom
        step5 = homomorphism {f = from eqA} {g = f}
        step6 : F.₁ g' ∘ Fto ≈M (Ff ∘ Ffrom) ∘ Fto
        step6 = ∘M-resp-≈ step5 (≈M-refl {f = Fto})
        step7 : (Ff ∘ Ffrom) ∘ Fto ≈M Ff ∘ (Ffrom ∘ Fto)
        step7 = ∘M-assoc {A = X} {B = Y} {C = X} {D = Z}
                         {f = Fto} {g = Ffrom} {h = Ff}
        step8 : Ff ∘ (Ffrom ∘ Fto) ≈M Ff ∘ id X
        step8 = ∘M-resp-≈ (≈M-refl {f = Ff}) isoCond
        step9 : Ff ∘ id X ≈M Ff
        step9 = ∘M-identityʳ {A = X} {B = Z} {f = Ff}
        step10 : F.₁ g' ∘ Fto ≈M Ff
        step10 = ≈M-trans step6 (≈M-trans step7 (≈M-trans step8 step9))
        step11 : Ft ∘ (F.₁ g' ∘ Fto) ≈M Ft ∘ Ff
        step11 = ∘M-resp-≈ (≈M-refl {f = Ft}) step10
        R≈L : R ≈M L
        R≈L = ≈M-trans step1 (≈M-trans step3 (≈M-trans step4 step11))
      in
        ≈M-sym R≈L

  -- The final ContCatEquiv instance (as a normal function)
  contCatEquivFromIso : ContCatEquiv ℓ
  contCatEquivFromIso = record
    { base                = isoObjEquiv
    ; containerFunctor    = F
    ; transportContainer  = transportContainer
    ; transportContainer-refl  = transportContainer-refl
    ; transportContainer-trans = transportContainer-trans
    ; act-natural         = act-natural
    }
