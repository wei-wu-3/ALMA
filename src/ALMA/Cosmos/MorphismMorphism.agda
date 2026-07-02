------------------------------------------------------------------------
-- MorphismMorphism: compatibility of position maps with hom-actions
--
-- onActP : onPos commutes with the container position maps actPOf,
--          modulo the shape transport induced by the naturality of CF
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.MorphismMorphism where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (_⇒_; Container; shape; position)
open import Data.Container.Morphism using (id; _∘_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; cong; sym; subst-subst)

open import ALMA.Cosmos.Iso
open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ObjEquivFunctor
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.ContCatEquivFunctor using (ContCatEquivFunctor; compContCatEquivFunctor)
open import ALMA.Cosmos.UnfoldingObject
open import ALMA.Cosmos.UnfoldingMorphism
open import ALMA.Cosmos.MorphismObject

private
  trans-reflˡ : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → trans refl p ≡ p
  trans-reflˡ refl = refl
  trans-reflʳ : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → trans p refl ≡ p
  trans-reflʳ refl = refl
  shape-eq-trans : ∀ {s p} {C D : Container s p} {f g h : C ⇒ D}
                 → (eq1 : f ≈M g) (eq2 : g ≈M h) (x : Container.Shape C)
                 → shape-eq-from-≈M (≈M-trans eq1 eq2) x
                   ≡ trans (shape-eq-from-≈M eq1 x) (shape-eq-from-≈M eq2 x)
  shape-eq-trans _ _ _ = refl
  shape-eq-sym : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
               → (eq : f ≈M g) (x : Container.Shape C)
               → shape-eq-from-≈M (≈M-sym eq) x ≡ sym (shape-eq-from-≈M eq x)
  shape-eq-sym _ _ = refl
  shape-eq-assoc : ∀ {s p} {A B C D : Container s p}
                → {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
                → (x : Container.Shape A)
                → shape-eq-from-≈M (∘M-assoc {A = A} {B} {C} {D} {f} {g} {h}) x ≡ refl
  shape-eq-assoc _ = refl
  shape-eq-resp-ˡ : ∀ {s p} {A B C : Container s p}
                    → {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
                    → (eq : g₁ ≈M g₂) (x : Container.Shape A)
                    → shape-eq-from-≈M (∘M-resp-≈ˡ {f = f} eq) x
                      ≡ shape-eq-from-≈M eq (shape f x)
  shape-eq-resp-ˡ {g₁ = g₁} {g₂} {f} eq x =
    let
      open _≈M_ eq renaming (shape-eq to g-shape)
      lemma : trans (g-shape (shape f x)) refl ≡ g-shape (shape f x)
      lemma = trans-refl-right (g-shape (shape f x))
    in
    lemma
    where
      trans-refl-right : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → trans p refl ≡ p
      trans-refl-right refl = refl
  shape-eq-resp-ʳ : ∀ {s p} {A B C : Container s p}
                  → {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
                  → (eq : f₁ ≈M f₂) (x : Container.Shape A)
                  → shape-eq-from-≈M (∘M-resp-≈ʳ {g = g} eq) x
                    ≡ cong (shape g) (shape-eq-from-≈M eq x)
  shape-eq-resp-ʳ _ _ = refl
  onPos-subst-comm :
    ∀ {ℓ} {F G : ContCatEquiv ℓ} {CF : ContCatEquivFunctor F G}
    {X Y : Set (lsuc (lsuc ℓ))} {UOF : UnfoldingObject ℓ F X} {UOG : UnfoldingObject ℓ G Y}
    (MO : MorphismObject CF UOF UOG)
    {A : Category.Obj (ObjEquivCat.cat (ContCatEquiv.base F))}
    {s₁ s₂ : ShapeOf (ContCatEquiv.containerFunctor F) A}
    (eq : s₁ ≡ s₂)
    (p : PosOf (ContCatEquiv.containerFunctor F) s₁)
    → MorphismObject.onPos MO (subst (PosOf (ContCatEquiv.containerFunctor F)) eq p)
      ≡ subst (PosOf (ContCatEquiv.containerFunctor G))
              (cong (shape (ContCatEquivFunctor.containerNat CF)) eq)
              (MorphismObject.onPos MO p)
  onPos-subst-comm MO refl p = refl
  comp-nat-shape-eq :
    ∀ {ℓ} {F G H : ContCatEquiv ℓ}
    (g : ContCatEquivFunctor G H) (f : ContCatEquivFunctor F G)
    {A B : Category.Obj (ObjEquivCat.cat (ContCatEquiv.base F))}
    (h : Category._⇒_ (ObjEquivCat.cat (ContCatEquiv.base F)) A B)
    (s : ShapeOf (ContCatEquiv.containerFunctor F) A)
    → shape-eq-from-≈M (ContCatEquivFunctor.natural (compContCatEquivFunctor g f) h) s
      ≡ trans
          (cong (shape (ContCatEquivFunctor.containerNat g))
                (shape-eq-from-≈M (ContCatEquivFunctor.natural f h) s))
          (shape-eq-from-≈M
            (ContCatEquivFunctor.natural g
              (Functor.₁ (ObjEquivFunctor.baseFunctor (ContCatEquivFunctor.objEquivFunctor f)) h))
            (shape (ContCatEquivFunctor.containerNat f) s))
  comp-nat-shape-eq {F = F} {G} {H} g f {A} {B} h s =
    let
      module FCE = ContCatEquiv F
      module GCE = ContCatEquiv G
      module HCE = ContCatEquiv H
      module fCF = ContCatEquivFunctor f
      module gCF = ContCatEquivFunctor g
      fctr = FCE.containerFunctor
      gctr = GCE.containerFunctor
      hctr = HCE.containerFunctor
      fobj = ObjEquivFunctor.baseFunctor fCF.objEquivFunctor
      gobj = ObjEquivFunctor.baseFunctor gCF.objEquivFunctor
      module fobj = Functor fobj
      module gobj = Functor gobj
      module fctr = Functor fctr
      module gctr = Functor gctr
      module hctr = Functor hctr
      fN-A : fctr.₀ A ⇒ gctr.₀ (fobj.₀ A)
      fN-A = fCF.containerNat {A}
      fN-B : fctr.₀ B ⇒ gctr.₀ (fobj.₀ B)
      fN-B = fCF.containerNat {B}
      gN-fA : gctr.₀ (fobj.₀ A) ⇒ hctr.₀ (gobj.₀ (fobj.₀ A))
      gN-fA = gCF.containerNat {fobj.₀ A}
      gN-fB : gctr.₀ (fobj.₀ B) ⇒ hctr.₀ (gobj.₀ (fobj.₀ B))
      gN-fB = gCF.containerNat {fobj.₀ B}
      Fh : fctr.₀ A ⇒ fctr.₀ B
      Fh = fctr.₁ h
      Gfh : gctr.₀ (fobj.₀ A) ⇒ gctr.₀ (fobj.₀ B)
      Gfh = gctr.₁ (fobj.₁ h)
      Hgfh : hctr.₀ (gobj.₀ (fobj.₀ A)) ⇒ hctr.₀ (gobj.₀ (fobj.₀ B))
      Hgfh = hctr.₁ (gobj.₁ (fobj.₁ h))
      s1 : (gN-fB ∘ fN-B) ∘ Fh ≈M gN-fB ∘ (fN-B ∘ Fh)
      s1 = ∘M-assoc {f = Fh} {g = fN-B} {h = gN-fB}
      s2 : gN-fB ∘ (fN-B ∘ Fh) ≈M gN-fB ∘ (Gfh ∘ fN-A)
      s2 = ∘M-resp-≈ʳ {g = gN-fB} (fCF.natural h)
      s3 : gN-fB ∘ (Gfh ∘ fN-A) ≈M (gN-fB ∘ Gfh) ∘ fN-A
      s3 = ≈M-sym (∘M-assoc {f = fN-A} {g = Gfh} {h = gN-fB})
      s4 : (gN-fB ∘ Gfh) ∘ fN-A ≈M (Hgfh ∘ gN-fA) ∘ fN-A
      s4 = ∘M-resp-≈ˡ {f = fN-A} (gCF.natural (fobj.₁ h))
      s5 : (Hgfh ∘ gN-fA) ∘ fN-A ≈M Hgfh ∘ (gN-fA ∘ fN-A)
      s5 = ∘M-assoc {f = fN-A} {g = gN-fA} {h = Hgfh}
      rest2 = ≈M-trans s2 (≈M-trans s3 (≈M-trans s4 s5))
      rest3 = ≈M-trans s3 (≈M-trans s4 s5)
      rest4 = ≈M-trans s4 s5
      f-eq = shape-eq-from-≈M (fCF.natural h) s
      g-eq = shape-eq-from-≈M (gCF.natural (fobj.₁ h)) (shape fN-A s)
      step1 : shape-eq-from-≈M (≈M-trans s1 rest2) s ≡ shape-eq-from-≈M rest2 s
      step1 = trans (shape-eq-trans s1 rest2 s)
                   (trans-reflˡ (shape-eq-from-≈M rest2 s))
      step2 : shape-eq-from-≈M rest2 s ≡ trans (cong (shape gN-fB) f-eq) (shape-eq-from-≈M rest3 s)
      step2 = shape-eq-trans s2 rest3 s
      step3 : shape-eq-from-≈M rest3 s ≡ shape-eq-from-≈M rest4 s
      step3 = trans (shape-eq-trans s3 rest4 s)
                   (trans-reflˡ (shape-eq-from-≈M rest4 s))
      step4 : shape-eq-from-≈M rest4 s ≡ shape-eq-from-≈M s4 s
      step4 = trans (shape-eq-trans s4 s5 s)
                   (trans-reflʳ (shape-eq-from-≈M s4 s))
      step5 : shape-eq-from-≈M s4 s ≡ g-eq
      step5 = shape-eq-resp-ˡ {A = fctr.₀ A} {B = gctr.₀ (fobj.₀ A)} {C = hctr.₀ (gobj.₀ (fobj.₀ B))}
                              {g₁ = gN-fB ∘ Gfh} {g₂ = Hgfh ∘ gN-fA} {f = fN-A}
                              (gCF.natural (fobj.₁ h)) s
      final : shape-eq-from-≈M (≈M-trans s1 rest2) s ≡ trans (cong (shape gN-fB) f-eq) g-eq
      final = trans step1
              (trans step2
              (trans (cong (λ x → trans (cong (shape gN-fB) f-eq) x) step3)
              (trans (cong (λ x → trans (cong (shape gN-fB) f-eq) x) step4)
                     (cong (λ x → trans (cong (shape gN-fB) f-eq) x) step5))))
    in
    final

record MorphismMorphism {ℓ : Level}
  {CEF CEG : ContCatEquiv ℓ}
  {CF : ContCatEquivFunctor CEF CEG}
  {X Y : Set (lsuc (lsuc ℓ))}
  {UOF : UnfoldingObject ℓ CEF X}
  {UOG : UnfoldingObject ℓ CEG Y}
  (MO : MorphismObject CF UOF UOG)
  (UMF : UnfoldingMorphism ℓ CEF X UOF)
  (UMG : UnfoldingMorphism ℓ CEG Y UOG)
  : Set (lsuc ℓ) where
  private
    module CEF      = ContCatEquiv CEF
    module CEG      = ContCatEquiv CEG
    module CFstruct = ContCatEquivFunctor CF
    module CFobj    = ObjEquivFunctor CFstruct.objEquivFunctor
    module BF       = Functor CFobj.baseFunctor
    module UMF      = UnfoldingMorphism UMF
    module UMG      = UnfoldingMorphism UMG
    module MO       = MorphismObject MO
    module CatF     = Category (ObjEquivCat.cat CEF.base)
    module CatG     = Category (ObjEquivCat.cat CEG.base)
  field
    -- onPos ∘ actPOf(f) ≡ actPOf(BF.₁ f) ∘ onPos (via shape transport)
    onActP : ∀ {A B} (f : CatF._⇒_ A B) (s : ShapeOf CEF.containerFunctor A)
           → (p : PosOf CEF.containerFunctor (actSOf CEF.containerFunctor f s))
           → MO.onPos (actPOf CEF.containerFunctor f s p)
             ≡ actPOf CEG.containerFunctor (BF.₁ f) (shape CFstruct.containerNat s)
                 (subst (PosOf CEG.containerFunctor)
                        (shape-eq-from-≈M (CFstruct.natural f) s)
                        (MO.onPos p))

-- Identity MorphismMorphism
module _ {ℓ : Level}
  {CE : ContCatEquiv ℓ}
  {X : Set (lsuc (lsuc ℓ))}
  {UO : UnfoldingObject ℓ CE X}
  {UM : UnfoldingMorphism ℓ CE X UO}
  where
  idMorphismMorphism : MorphismMorphism (idMorphismObject {UO = UO}) UM UM
  idMorphismMorphism = record
    { onActP = λ f s p → refl
    }

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

-- Composition of MorphismMorphisms
module _ {ℓ : Level}
  {CEF CEG CEH : ContCatEquiv ℓ}
  {CF : ContCatEquivFunctor CEF CEG}
  {CG : ContCatEquivFunctor CEG CEH}
  {X Y Z : Set (lsuc (lsuc ℓ))}
  {UOF : UnfoldingObject ℓ CEF X}
  {UOG : UnfoldingObject ℓ CEG Y}
  {UOH : UnfoldingObject ℓ CEH Z}
  {UMF : UnfoldingMorphism ℓ CEF X UOF}
  {UMG : UnfoldingMorphism ℓ CEG Y UOG}
  {UMH : UnfoldingMorphism ℓ CEH Z UOH}
  where
  private
    module CEF = ContCatEquiv CEF
    module CEG = ContCatEquiv CEG
    module CEH = ContCatEquiv CEH
    module CF = ContCatEquivFunctor CF
    module CG = ContCatEquivFunctor CG
    compCF = compContCatEquivFunctor CG CF
    module compCF = ContCatEquivFunctor compCF
    module BFf = Functor (ObjEquivFunctor.baseFunctor CF.objEquivFunctor)
    module BFg = Functor (ObjEquivFunctor.baseFunctor CG.objEquivFunctor)
    Fctr = CEF.containerFunctor
    Gctr = CEG.containerFunctor
    Hctr = CEH.containerFunctor
  compMorphismMorphism :
      {MOg : MorphismObject CG UOG UOH}
      {MOf : MorphismObject CF UOF UOG}
      (MMg : MorphismMorphism MOg UMG UMH)
      (MMf : MorphismMorphism MOf UMF UMG)
      → MorphismMorphism (compMorphismObject MOg MOf) UMF UMH
  compMorphismMorphism {MOg = MOg} {MOf} MMg MMf = record
    { onActP = λ {A B} f s p →
        let
          open MorphismMorphism MMf renaming (onActP to onActP-f)
          open MorphismMorphism MMg renaming (onActP to onActP-g)
          step-f : onPos-f (actPOf Fctr f s p)
                   ≡ actPOf Gctr (BFf.₁ f) (shape CF.containerNat s)
                       (subst (PosOf Gctr) (shape-eq-from-≈M (CF.natural f) s) (onPos-f p))
          step-f = onActP-f f s p
          step-cong : onPos-g (onPos-f (actPOf Fctr f s p))
                      ≡ onPos-g (actPOf Gctr (BFf.₁ f) (shape CF.containerNat s)
                                  (subst (PosOf Gctr) (shape-eq-from-≈M (CF.natural f) s) (onPos-f p)))
          step-cong = cong onPos-g step-f
          f' = BFf.₁ f
          s' = shape CF.containerNat s
          p' = subst (PosOf Gctr) (shape-eq-from-≈M (CF.natural f) s) (onPos-f p)
          step-g : onPos-g (actPOf Gctr f' s' p')
                   ≡ actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
                       (subst (PosOf Hctr) (shape-eq-from-≈M (CG.natural f') s') (onPos-g p'))
          step-g = onActP-g f' s' p'
          step-subst : onPos-g p'
                       ≡ subst (PosOf Hctr)
                               (cong (shape CG.containerNat) (shape-eq-from-≈M (CF.natural f) s))
                               (onPos-g (onPos-f p))
          step-subst = onPos-subst-comm MOg (shape-eq-from-≈M (CF.natural f) s) (onPos-f p)
          eq-f = shape-eq-from-≈M (CF.natural f) s
          eq-g = shape-eq-from-≈M (CG.natural f') s'
          x = onPos-g (onPos-f p)
          subst-merge : subst (PosOf Hctr) eq-g (onPos-g p')
                        ≡ subst (PosOf Hctr) (trans (cong (shape CG.containerNat) eq-f) eq-g) x
          subst-merge = trans (cong (subst (PosOf Hctr) eq-g) step-subst)
                              (subst-subst (cong (shape CG.containerNat) eq-f))
          eq-comp = shape-eq-from-≈M (compCF.natural f) s
          eq-match : trans (cong (shape CG.containerNat) eq-f) eq-g ≡ eq-comp
          eq-match = sym (comp-nat-shape-eq CG CF f s)
          final-subst : subst (PosOf Hctr) eq-g (onPos-g p')
                        ≡ subst (PosOf Hctr) eq-comp x
          final-subst = trans subst-merge
                              (cong (λ e → subst (PosOf Hctr) e x) eq-match)
        in
        trans step-cong
        (trans step-g
        (cong (actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')) final-subst))
    }
    where
      open MorphismObject MOg renaming (onPos to onPos-g)
      open MorphismObject MOf renaming (onPos to onPos-f)
