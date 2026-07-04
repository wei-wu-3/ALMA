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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.ObjEquivFunctor
open import ALMA.Cosmos.ContCatEquivFunctor
open import ALMA.Cosmos.UnfoldingObject
open import ALMA.Cosmos.UnfoldingMorphism
open import ALMA.Cosmos.ContCategoryLemmas

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

-- Composition of MorphismObjects: chains the object/position mappings
module _ {ℓ : Level}
  {CEF CEG CEH : ContCatEquiv ℓ}
  {CF : ContCatEquivFunctor CEF CEG}
  {CG : ContCatEquivFunctor CEG CEH}
  {X Y Z : Set (lsuc (lsuc ℓ))}
  {UOF : UnfoldingObject ℓ CEF X}
  {UOG : UnfoldingObject ℓ CEG Y}
  {UOH : UnfoldingObject ℓ CEH Z}
  where
  private
    module CEF = ContCatEquiv CEF
    module CEG = ContCatEquiv CEG
    module CEH = ContCatEquiv CEH
    module CF = ContCatEquivFunctor CF
    module CG = ContCatEquivFunctor CG
    compCF = compContCatEquivFunctor CG CF
    module compCF = ContCatEquivFunctor compCF
    module OEH = ObjEquivCat CEH.base
  compMorphismObject :
    (MOg : MorphismObject CG UOG UOH)
    (MOf : MorphismObject CF UOF UOG)
    → MorphismObject compCF UOF UOH
  compMorphismObject MOg MOf = record
    { onPos = λ p → onPos-g (onPos-f p)
    ; onunfold-obj = λ s →
        IsEquivalence.trans OEH.≈ₒ-isEquiv
          (ObjEquivFunctor.≈ₒ-homo CG.objEquivFunctor (onunfold-obj-f s))
          (onunfold-obj-g (shape CF.containerNat s))
    ; onPos-to-shape = λ {A} {s} p →
        let
          module CGfun = ContCatEquivFunctor CG
          module UOF = UnfoldingObject UOF
          module UOG = UnfoldingObject UOG
          module UOH = UnfoldingObject UOH
          s' = shape CF.containerNat s
          eqf = onunfold-obj-f s
          eqg = onunfold-obj-g s'
          eq1 = ObjEquivFunctor.≈ₒ-homo CGfun.objEquivFunctor eqf
          eq-comp = IsEquivalence.trans OEH.≈ₒ-isEquiv eq1 eqg
          y = shape CF.containerNat (UOF.pos-to-shape s p)
          x = shape CGfun.containerNat y
          step1 : shape compCF.containerNat (UOF.pos-to-shape s p) ≡ x
          step1 = refl
          step2 : shape (CEH.transportContainer eq-comp) (shape compCF.containerNat (UOF.pos-to-shape s p))
                 ≡ shape (CEH.transportContainer eqg) (shape (CEH.transportContainer eq1) x)
          step2 = trans (cong (shape (CEH.transportContainer eq-comp)) step1)
                        (shape-eq-from-≈M (CEH.transportContainer-trans eq1 eqg) x)
          step3 : shape (CEH.transportContainer eq1) x
                 ≡ shape CGfun.containerNat (shape (CEG.transportContainer eqf) y)
          step3 = sym (shape-eq-from-≈M (CGfun.transport-nat eqf) y)
          step4 : shape (CEH.transportContainer eqg) (shape (CEH.transportContainer eq1) x)
                 ≡ shape (CEH.transportContainer eqg) (shape CGfun.containerNat (shape (CEG.transportContainer eqf) y))
          step4 = cong (shape (CEH.transportContainer eqg)) step3
          step5 : shape (CEG.transportContainer eqf) y ≡ UOG.pos-to-shape s' (onPos-f p)
          step5 = onPos-to-shape-f p
          step6 : shape (CEH.transportContainer eqg) (shape CGfun.containerNat (shape (CEG.transportContainer eqf) y))
                 ≡ shape (CEH.transportContainer eqg) (shape CGfun.containerNat (UOG.pos-to-shape s' (onPos-f p)))
          step6 = cong (λ z → shape (CEH.transportContainer eqg) (shape CGfun.containerNat z)) step5
          step7 : shape (CEH.transportContainer eqg) (shape CGfun.containerNat (UOG.pos-to-shape s' (onPos-f p)))
                 ≡ UOH.pos-to-shape (shape CGfun.containerNat s') (onPos-g (onPos-f p))
          step7 = onPos-to-shape-g (onPos-f p)
          step8 : UOH.pos-to-shape (shape CGfun.containerNat s') (onPos-g (onPos-f p))
                 ≡ UOH.pos-to-shape (shape compCF.containerNat s) (onPos-g (onPos-f p))
          step8 = refl
        in
        trans step2 (trans step4 (trans step6 (trans step7 step8)))
    }
    where
      open MorphismObject MOg renaming (onPos to onPos-g; onunfold-obj to onunfold-obj-g; onPos-to-shape to onPos-to-shape-g)
      open MorphismObject MOf renaming (onPos to onPos-f; onunfold-obj to onunfold-obj-f; onPos-to-shape to onPos-to-shape-f)
