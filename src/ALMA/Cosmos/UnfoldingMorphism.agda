------------------------------------------------------------------------
-- Morphism-level structure for container-based unfolding systems
--
-- Lifts base-category morphisms to unfoldings and enforces functor laws
-- and position-action compatibility, all up to object equivalence transport
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.UnfoldingMorphism where

open import Agda.Primitive using (lsuc; Level)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Data.Container.Core using (Container; _⇒_; shape; position)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import ALMA.Cosmos.ObjEquivCat
open import ALMA.Cosmos.ContCategory
open import ALMA.Cosmos.ContCatEquiv
open import ALMA.Cosmos.UnfoldingObject

actSOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → Category._⇒_ C A B → ShapeOf F A → ShapeOf F B
actSOf F f = shape (Functor.₁ F f)
shape-eq-from-≈M : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
                  → f ≈M g → ∀ x → shape f x ≡ shape g x
shape-eq-from-≈M eq x = let open _≈M_ eq in shape-eq x
actS-resp-≈ : ∀ {o ℓ e s p} {C : Category o ℓ e}
            → (F : Functor C (ContCat s p))
            → {A B : Category.Obj C} {f g : Category._⇒_ C A B}
            → Category._≈_ C f g → ∀ s → actSOf F f s ≡ actSOf F g s
actS-resp-≈ F f≈ s = shape-eq-from-≈M (Functor.F-resp-≈ F f≈) s
actS-id-eq : ∀ {o ℓ e s p} {C : Category o ℓ e}
            → (F : Functor C (ContCat s p)) {A : Category.Obj C}
            → ∀ s → actSOf F (Category.id C {A}) s ≡ s
actS-id-eq F s = shape-eq-from-≈M (Functor.identity F) s
actS-comp-eq : ∀ {o ℓ e s p} {C : Category o ℓ e}
              → (F : Functor C (ContCat s p))
              → {A B Z : Category.Obj C}
              → {f : Category._⇒_ C A B} {g : Category._⇒_ C B Z}
              → ∀ s → actSOf F (Category._∘_ C g f) s ≡ actSOf F g (actSOf F f s)
actS-comp-eq F s = shape-eq-from-≈M (Functor.homomorphism F) s
actPOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → (f : Category._⇒_ C A B) (s : ShapeOf F A)
        → PosOf F (actSOf F f s) → PosOf F s
actPOf F f s = position (Functor.₁ F f) {s}

record UnfoldingMorphism (ℓ : Level) (CE : ContCatEquiv ℓ) (X : Set (lsuc (lsuc ℓ)))
                         (UO : UnfoldingObject ℓ CE X) : Set (lsuc (lsuc ℓ)) where
  private
    module CE′ = ContCatEquiv CE
    module OE  = ObjEquivCat CE′.base
    module Cat = Category OE.cat
  open UnfoldingObject UO
  field
    unfold-hom : ∀ {A B} (f : Cat._⇒_ A B) (s : ShapeOf CE′.containerFunctor A)
                 → unfold-obj s Cat.⇒ unfold-obj (actSOf CE′.containerFunctor f s)
    unfold-hom-resp-≈ : ∀ {A B} {f f' : Cat._⇒_ A B} {s s' : ShapeOf CE′.containerFunctor A}
                      → (f≈ : f Cat.≈ f') (s≡ : s ≡ s')
                      → OE.transport (unfold-obj-resp-≈ s≡)
                                     (unfold-obj-resp-≈ (trans (actS-resp-≈ CE′.containerFunctor f≈ s)
                                                               (cong (actSOf CE′.containerFunctor f') s≡)))
                                     (unfold-hom f s)
                        Cat.≈ unfold-hom f' s'
    unfold-hom-id : ∀ {A} (s : ShapeOf CE′.containerFunctor A)
                  → unfold-hom Cat.id s
                    Cat.≈ OE.transport (IsEquivalence.refl OE.≈ₒ-isEquiv)
                                       (IsEquivalence.sym OE.≈ₒ-isEquiv (unfold-obj-resp-≈ (actS-id-eq CE′.containerFunctor s)))
                                       Cat.id
    unfold-hom-comp : ∀ {A B C} {f : Cat._⇒_ A B} {g : Cat._⇒_ B C} (s : ShapeOf CE′.containerFunctor A)
                    → unfold-hom (g Cat.∘ f) s
                      Cat.≈ OE.transport (IsEquivalence.refl OE.≈ₒ-isEquiv)
                                         (IsEquivalence.sym OE.≈ₒ-isEquiv (unfold-obj-resp-≈ (actS-comp-eq CE′.containerFunctor s)))
                                         (unfold-hom g (actSOf CE′.containerFunctor f s) Cat.∘ unfold-hom f s)
    pos-actS-compat : ∀ {A B} (f : Cat._⇒_ A B) (s : ShapeOf CE′.containerFunctor A)
                    → (p : PosOf CE′.containerFunctor (actSOf CE′.containerFunctor f s))
                    → pos-to-shape (actSOf CE′.containerFunctor f s) p
                      ≡ actSOf CE′.containerFunctor (unfold-hom f s) (pos-to-shape s (actPOf CE′.containerFunctor f s p))
