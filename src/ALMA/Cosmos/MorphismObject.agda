------------------------------------------------------------------------
-- Object-level homomorphisms between unfolding systems
--
-- A MorphismObject witnesses the commutation of object/position mappings
-- with the container natural transformation, up to object equivalence
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.MorphismObject where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (shape)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.ObjEquivFunctor
open import ALMA.Cosmos.ContCatEquivFunctor
open import ALMA.Cosmos.UnfoldingObject

record MorphismObject {ℓ : Level}
  {CEF CEG : ContCatEquiv ℓ}
  (CF : ContCatEquivFunctor CEF CEG)
  {X Y : Set (lsuc (lsuc ℓ))}
  (UOF : UnfoldingObject ℓ CEF X)
  (UOG : UnfoldingObject ℓ CEG Y)
  : Set (lsuc ℓ) where
  private
    open ContCatEquiv CEF renaming (containerFunctor to Fctr)
    open ContCatEquiv CEG renaming (containerFunctor to Gctr; transportContainer to Gtrans)
    open ObjEquivCat (ContCatEquiv.base CEG) using (_≈ₒ_)
    module UOF = UnfoldingObject UOF
    module UOG = UnfoldingObject UOG
    module CFstruct = ContCatEquivFunctor CF
    module CFobj = ObjEquivFunctor CFstruct.objEquivFunctor
    module CFbase = Functor CFobj.baseFunctor using (₀)
  field
    onPos : ∀ {A} {s : ShapeOf Fctr A}
          → PosOf Fctr s
          → PosOf Gctr (shape CFstruct.containerNat s)
    onunfold-obj : ∀ {A} (s : ShapeOf Fctr A)
                 → CFbase.₀ (UOF.unfold-obj s) ≈ₒ
                   UOG.unfold-obj (shape CFstruct.containerNat s)
    onPos-to-shape : ∀ {A} {s : ShapeOf Fctr A} (p : PosOf Fctr s)
                   → shape (Gtrans (onunfold-obj s))
                           (shape (CFstruct.containerNat {UOF.unfold-obj s}) (UOF.pos-to-shape s p))
                     ≡ UOG.pos-to-shape (shape CFstruct.containerNat s) (onPos p)

-- Identity MorphismObject
idMorphismObject : ∀ {ℓ : Level}
  {CE : ContCatEquiv ℓ}
  {X : Set (lsuc (lsuc ℓ))}
  {UO : UnfoldingObject ℓ CE X}
  → MorphismObject (idContCatEquivFunctor CE) UO UO
idMorphismObject {CE = CE} {UO = UO} = record
  { onPos         = λ p → p
  ; onunfold-obj  = λ s → IsEquivalence.refl (ObjEquivCat.≈ₒ-isEquiv (ContCatEquiv.base CE))
  ; onPos-to-shape = λ {s = s} p →
      let
        module CE = ContCatEquiv CE
        module UO = UnfoldingObject UO
        trans-refl : CE.transportContainer _ ≈M _
        trans-refl = CE.transportContainer-refl {A = UO.unfold-obj s}
      in
      _≈M_.shape-eq trans-refl (UO.pos-to-shape s p)
  }