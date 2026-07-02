------------------------------------------------------------------------
-- ALMA — Infinite, Unbounded, Self-Referential Dynamic Cosmos
--
-- Built with type theory, category theory, containers, and coalgebraic unfolding
-- Cosmos is the terminal coalgebra of a polynomial functor internalized in type theory
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos where

open import Agda.Primitive using (lsuc; Level)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (_⇒_; shape; position)
open import Data.Container.Morphism using (id; _∘_)

open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.ObjEquivFunctor using (ObjEquivFunctor)
open import ALMA.Cosmos.ContCatEquivFunctor using (ContCatEquivFunctor; compContCatEquivFunctor; idContCatEquivFunctor)
open import ALMA.Cosmos.UnfoldingObject
open import ALMA.Cosmos.UnfoldingMorphism
open import ALMA.Cosmos.MorphismObject
open import ALMA.Cosmos.MorphismMorphism

-- Core definitions — CosmosLayer and Cosmos as terminal coalgebra
record CosmosLayer (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) : Set (lsuc (lsuc ℓ)) where
  field
    contEquiv    : ContCatEquiv ℓ
    unfoldingObj : UnfoldingObject ℓ contEquiv X
    unfoldingMor : UnfoldingMorphism ℓ contEquiv X unfoldingObj
record Cosmos (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    out : CosmosLayer ℓ (Cosmos ℓ)
open Cosmos public

-- Universe morphisms — _⇒ℱ_ and ⇒ℱLayer as coalgebra homomorphisms
mutual
  record _⇒ℱ_ {ℓ} (F G : Cosmos ℓ) : Set (lsuc ℓ) where
    coinductive
    field
      out : ⇒ℱLayer F G
  record ⇒ℱLayer {ℓ} (F G : Cosmos ℓ) : Set (lsuc ℓ) where
    inductive
    private
      module FL = CosmosLayer (out F)
      module GL = CosmosLayer (out G)
      module CE-F = ContCatEquiv FL.contEquiv
      module CE-G = ContCatEquiv GL.contEquiv
      module UO-F = UnfoldingObject FL.unfoldingObj
      module UO-G = UnfoldingObject GL.unfoldingObj
      module UM-F = UnfoldingMorphism FL.unfoldingMor
      module UM-G = UnfoldingMorphism GL.unfoldingMor
    field
      contEquivFunctor : ContCatEquivFunctor FL.contEquiv GL.contEquiv
      morphismObj      : MorphismObject contEquivFunctor FL.unfoldingObj GL.unfoldingObj
      morphismMor      : MorphismMorphism morphismObj FL.unfoldingMor GL.unfoldingMor
      onunfold-next : ∀ {A} (s : Data.Container.Core.Shape (Functor.₀ CE-F.containerFunctor A))
                      → UO-F.unfold-next s ⇒ℱ UO-G.unfold-next (Data.Container.Core.shape (ContCatEquivFunctor.containerNat contEquivFunctor) s)
open _⇒ℱ_ public

-- Identity morphism — id⇒ℱ as identity coalgebra homomorphism
id⇒ℱ : ∀ {ℓ} {F : Cosmos ℓ} → F ⇒ℱ F
id⇒ℱ {F = F} .out =
  let
    open CosmosLayer (out F)
    CE = contEquiv
    UO = unfoldingObj
    UM = unfoldingMor
  in record
  { contEquivFunctor = idContCatEquivFunctor CE
  ; morphismObj = record
    { onPos         = λ p → p
    ; onunfold-obj  = λ s → IsEquivalence.refl (ObjEquivCat.≈ₒ-isEquiv (ContCatEquiv.base CE))
    ; onPos-to-shape = λ {s = s} p →
        let open UnfoldingObject UO in
        trans (shape-eq-from-≈M (ContCatEquiv.transportContainer-refl CE {A = unfold-obj s})
              (pos-to-shape s p)) refl
    }
  ; morphismMor = record { onActP = λ _ _ _ → refl }
  ; onunfold-next = λ s → id⇒ℱ
  }

-- Morphism composition — _∘⇒ℱ_ as composition of coalgebra homomorphisms
_∘⇒ℱ_ : ∀ {ℓ} {F G H : Cosmos ℓ} → G ⇒ℱ H → F ⇒ℱ G → F ⇒ℱ H
_∘⇒ℱ_ {ℓ} {F} {G} {H} g f .out = record
  { contEquivFunctor = compCF
  ; morphismObj      = compMO
  ; morphismMor      = compMM
  ; onunfold-next    = λ {A} s → nextG (shape (ContCatEquivFunctor.containerNat cF) s) ∘⇒ℱ nextF s
  }
  where
    open ⇒ℱLayer (g .out) 
      renaming (contEquivFunctor to cG; morphismObj to moG; morphismMor to mmG; onunfold-next to nextG)
    open ⇒ℱLayer (f .out) 
      renaming (contEquivFunctor to cF; morphismObj to moF; morphismMor to mmF; onunfold-next to nextF)
    compCF = compContCatEquivFunctor cG cF
    compMO = compMorphismObject moG moF
    compMM = compMorphismMorphism mmG mmF

-- Instance — UnitCosmos as the trivial one-object cosmos
-- The trivial terminal category: one object ⊤, one morphism tt
UnitCat : ∀ {ℓ} → Category (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)
UnitCat = record
  { Obj       = ⊤
  ; _⇒_       = λ _ _ → ⊤
  ; _≈_       = _≡_
  ; id        = tt
  ; _∘_       = λ _ _ → tt
  ; equiv     = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈  = λ {A B C f g h i} _ _ → refl
  ; assoc     = λ {A B C D f g h} → refl
  ; sym-assoc = λ {A B C D f g h} → refl
  ; identityˡ = λ {A B f} → refl
  ; identityʳ = λ {A B f} → refl
  ; identity² = λ {A} → refl
  }
-- The trivial container functor: every object maps to the ⊤-container
UnitContainerFunctor : ∀ {ℓ} → Functor (UnitCat {ℓ}) (ContCat (lsuc ℓ) (lsuc ℓ))
UnitContainerFunctor = record
  { F₀ = λ _ → record { Shape = ⊤ ; Position = λ _ → ⊤ }
  ; F₁ = λ _ → record { shape = λ _ → tt ; position = λ _ → tt }
  ; identity     = ≈M-refl
  ; homomorphism = ≈M-refl
  ; F-resp-≈     = λ _ → ≈M-refl
  }
-- The ContCatEquiv for the trivial cosmos: auto-constructed from UnitCat + UnitContainerFunctor
UnitContCatEquiv : ∀ {ℓ} → ContCatEquiv ℓ
UnitContCatEquiv = contCatEquivFromIso UnitCat UnitContainerFunctor
-- The trivial unit cosmos: every layer unfolds to itself
UnitCosmos : ∀ {ℓ} → Cosmos ℓ
UnitCosmos {ℓ} .out = record
  { contEquiv    = UnitContCatEquiv
  ; unfoldingObj = record
    { unfold-obj             = λ _ → tt
    ; pos-to-shape           = λ _ _ → tt
    ; unfold-next            = λ _ → UnitCosmos
    ; unfold-obj-resp-≈      = λ _ → unitIso _ _
    ; pos-to-shape-resp-≈    = λ _ _ → refl
    ; pos-to-shape-transport = λ _ → refl
    }
  ; unfoldingMor = record
    { unfold-hom          = λ _ _ → tt
    ; unfold-hom-resp-≈   = λ _ _ → refl
    ; unfold-hom-id       = λ _ → refl
    ; unfold-hom-comp     = λ _ → refl
    ; pos-actS-compat     = λ _ _ _ → refl
    }
  }
  where
    open ContCatEquiv UnitContCatEquiv
    open ObjEquivCat base
    -- Every two objects in UnitCat are isomorphic via tt
    unitIso : ∀ (x y : ⊤) → x ≈ₒ y
    unitIso tt tt = record { to = tt ; from = tt ; isoˡ = refl ; isoʳ = refl }
