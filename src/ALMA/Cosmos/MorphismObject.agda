------------------------------------------------------------------------
-- Object-level homomorphisms between unfolding systems
--
-- A MorphismObject witnesses the commutation of object/position mappings
-- with the container natural transformation, up to object isomorphism
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.MorphismObject where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open import Data.Container.Core using (shape)
open import Data.Container.Morphism using (id)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_; module Functor) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; module NaturalTransformation)
open import Categories.Morphism using (_≅_; module ≅)

open import ALMA.Cosmos.ContCategory using (ContCat; _≈M_)
open import ALMA.Cosmos.ContCatEquiv using (ContCatEquiv; ShapeCat)
open import ALMA.Cosmos.ContCatEquivFunctor
  using (ContCatEquivFunctor; idContCatEquivFunctor; compContCatEquivFunctor; module ShapeCatMorphism)
open import ALMA.Cosmos.Unfolding using (Unfolding; module Unfolding)
open import ALMA.Cosmos.ContCategoryLemmas using (shape-eq-from-≈M; ShapeOf; PosOf)

private
  F-map-iso : ∀ {o h e} {C D : Category o h e}
            → (F : Functor C D)
            → ∀ {A B} → _≅_ C A B → _≅_ D (Functor.₀ F A) (Functor.₀ F B)
  F-map-iso {D = D} F iso =
    let module D = Category D
        module F = Functor F
        open _≅_ iso
    in record
    { from = F.₁ from
    ; to   = F.₁ to
    ; iso  = record
      { isoˡ = D.Equiv.trans (D.Equiv.sym F.homomorphism)
               (D.Equiv.trans (F.F-resp-≈ isoˡ) F.identity)
      ; isoʳ = D.Equiv.trans (D.Equiv.sym F.homomorphism)
               (D.Equiv.trans (F.F-resp-≈ isoʳ) F.identity)
      }
    }

module _ {o h e o′ h′ : Level} {C D : Category o h e}
  {FC : Functor C (ContCat o′ h′)} {FD : Functor D (ContCat o′ h′)}
  {H : Functor C D} {α : NaturalTransformation FC (FD ∘F H)}
  {X Y : Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ h′))}
  (cf : ContCatEquivFunctor FC FD H α)
  (UF : Unfolding FC X) (UG : Unfolding FD Y) where
  record MorphismObject : Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ h′)) where
    constructor mk
    field
      unfoldIso : NaturalTransformation
                  (H ∘F Unfolding.unfoldFunctor UF)
                  ((Unfolding.unfoldFunctor UG) ∘F ShapeCatMorphism.S cf)

------------------------------------------------------------------------
-- 恒等 MorphismObject
------------------------------------------------------------------------
idMorphismObject : ∀ {o h e o′ h′} {C : Category o h e}
  {FC : Functor C (ContCat o′ h′)}
  {X : Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ h′))}
  {UF : Unfolding FC X}
  → MorphismObject (idContCatEquivFunctor FC) UF UF
idMorphismObject {C = C} {FC = FC} {UF = UF} = record
  { onPos = λ p → p
  ; onunfold-iso = λ s → ≅.refl
  ; onPos-to-shape = λ {A} {s} p →
      let
        ce : ContCatEquiv C FC
        ce = record {}
        module CE = ContCatEquiv C FC ce
        open ≡-Reasoning
      in begin
        shape (CE.transpCont ≅.refl) (shape _ (UF.pos-to-shape s p))
          ≡⟨ shape-eq-from-≈M CE.transpCont-refl _ ⟩
        shape (id (FC.₀ (UF.unfoldFunctor .₀ (A , s)))) (shape _ (UF.pos-to-shape s p))
          ≡⟨ refl ⟩
        UF.pos-to-shape s p
          ≡⟨ refl ⟩
        UF.pos-to-shape s p
      ∎
  }
  where open Categories.Morphism C using (_≅_)

------------------------------------------------------------------------
-- MorphismObject 复合
------------------------------------------------------------------------
compMorphismObject : ∀ {o h e o′ h′} {C D E : Category o h e}
  {FC : Functor C (ContCat o′ h′)}
  {FD : Functor D (ContCat o′ h′)}
  {FE : Functor E (ContCat o′ h′)}
  {bg : Functor D E}
  {bf : Functor C D}
  {ng : NaturalTransformation FD (FE ∘F bg)}
  {nf : NaturalTransformation FC (FD ∘F bf)}
  {X Y Z : Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ h′))}
  {cg : ContCatEquivFunctor FD FE bg ng}
  {cf : ContCatEquivFunctor FC FD bf nf}
  {UF : Unfolding FC X}
  {UG : Unfolding FD Y}
  {UH : Unfolding FE Z}
  → MorphismObject cg UG UH
  → MorphismObject cf UF UG
  → MorphismObject (compContCatEquivFunctor FC FD FE cg cf) UF UH
compMorphismObject {C = C} {D = D} {E = E} {bg = bg} {bf = bf} {ng = ng} {nf = nf} {cg = cg} {cf = cf} {UF = UF} {UG = UG} {UH = UH} mog mof = record
  { onPos = λ p → onPos-g (onPos-f p)
  ; onunfold-iso = λ {A} s →
      ≅.trans E
        (F-map-iso bg (onunfold-iso-f s))
        (onunfold-iso-g (shape (nf.η A) s))
  ; onPos-to-shape = λ {A} {s} p →
      let
        module bg = Functor bg
        module nf = NaturalTransformation nf
        module ng = NaturalTransformation ng
        module Sf = ShapeCatMorphism cf
        module Sg = ShapeCatMorphism cg

        ceE : ContCatEquiv E FE
        ceE = record {}
        ceD : ContCatEquiv D FD
        ceD = record {}
        module CEE = ContCatEquiv E FE
        module CED = ContCatEquiv D FD ceD
        open ≡-Reasoning

        s'     = shape (nf.η A) s
        eqf    = onunfold-iso-f s
        eqg    = onunfold-iso-g s'
        eq1    = F-map-iso bg eqf
        eq-comp = ≅.trans E eq1 eqg

        y = shape (nf.η (UF.unfoldFunctor .₀ (A , s))) (UF.pos-to-shape s p)
        x = shape (ng.η (bg.₀ (UF.unfoldFunctor .₀ (A , s)))) y

        -- 容器自然变换与同构传输的交换律（由自然性直接导出）
        nat-comm : shape (CEE.transpCont eq1) x
                 ≡ shape (ng.η (UG.unfoldFunctor .₀ (Sf.S .₀ (A , s))))
                         (shape (CED.transpCont eqf) y)
        nat-comm = sym (shape-eq-from-≈M (ng.commute (≅.from eqf)) y)
      in begin
        shape (CEE.transpCont eq-comp) (shape _ (UF.pos-to-shape s p))
          ≡⟨ shape-eq-from-≈M (CEE.transpCont-trans eq1 eqg) _ ⟩
        shape (CEE.transpCont eqg) (shape (CEE.transpCont eq1) x)
          ≡⟨ cong (shape (CEE.transpCont eqg)) nat-comm ⟩
        shape (CEE.transpCont eqg)
              (shape (ng.η (UG.unfoldFunctor .₀ (Sf.S .₀ (A , s))))
                     (shape (CED.transpCont eqf) y))
          ≡⟨ cong (shape (CEE.transpCont eqg))
                  (cong (shape (ng.η _)) (onPos-to-shape-f p)) ⟩
        shape (CEE.transpCont eqg)
              (shape (ng.η _) (UG.pos-to-shape s' (onPos-f p)))
          ≡⟨ onPos-to-shape-g (onPos-f p) ⟩
        UH.pos-to-shape (shape (ng.η _) s') (onPos-g (onPos-f p))
          ≡⟨ refl ⟩
        UH.pos-to-shape (shape _ s) (onPos-g (onPos-f p))
      ∎
  }
  where
    open MorphismObject mog renaming (onPos to onPos-g; onunfold-iso to onunfold-iso-g; onPos-to-shape to onPos-to-shape-g)
    open MorphismObject mof renaming (onPos to onPos-f; onunfold-iso to onunfold-iso-f; onPos-to-shape to onPos-to-shape-f)
    open Categories.Morphism using (_≅_; module ≅)