------------------------------------------------------------------------
-- Cumulative Hierarchy of Cosmoi — Concrete Instances
-- 宇宙的累积层级 —— 具体实例
--
-- Provides concrete instances of EmbeddingData, UniformEmbeddingFamily,
-- FunctorialEmbeddingFamily, and LambekConsistency for the terminal
-- category UnitCat and for FinCat n, together with the hierarchy
-- constructions based on them.  Also contains an experimental module
-- StrictLift for level-raising.
-- 为终范畴 UnitCat 及 FinCat n 提供 EmbeddingData、UniformEmbeddingFamily、
-- FunctorialEmbeddingFamily 和 LambekConsistency 的具体实例，
-- 以及基于它们的层级构造。 还包含一个实验性的层级提升模块 StrictLift。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.CumulativeHierarchyInstances where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Nat using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality.Core using (sym; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈M-refl)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out; UnitCat; UnitContainerFunctor; UnitCosmos)
open import ALMA.Cosmos.Terminal using (_≈C_)
open import ALMA.Cosmos.CumulativeHierarchy

-- Embedding data for the terminal category: the unique morphism serves
-- as retraction, and all morphisms are equal
-- 终范畴的嵌入数据：唯一态射作为收缩，且所有态射相等
UnitCat-EmbeddingData : ∀ {ℓ} {FC : Functor (UnitCat {ℓ}) (ContCat ℓ ℓ)}
                    → (x : Cosmos (UnitCat {ℓ}) FC) → EmbeddingData x
UnitCat-EmbeddingData {ℓ} =
  mkEmbeddingData (λ _ _ → Category.id (UnitCat {ℓ}))
                  (λ _ _ → Category.Equiv.refl (UnitCat {ℓ}))

UnitCat-EmbeddingFamily : ∀ {ℓ} {FC : Functor (UnitCat {ℓ}) (ContCat ℓ ℓ)}
                        → EmbeddingFamily {C = UnitCat {ℓ}} {FC = FC}
UnitCat-EmbeddingFamily = record { getData = UnitCat-EmbeddingData }

UnitCat-UniformEmbeddingFamily : ∀ {ℓ} {FC : Functor (UnitCat {ℓ}) (ContCat ℓ ℓ)}
  → UniformEmbeddingFamily {C = UnitCat {ℓ}} {FC = FC}
UnitCat-UniformEmbeddingFamily = record
  { family          = UnitCat-EmbeddingFamily
  ; next-consistent = λ _ _ → refl
  }

-- Unit hierarchy
-- 单位层级
module UnitHierarchy {ℓ : Level} where
  private
    UCat = UnitCat {ℓ}
    UFC  = UnitContainerFunctor {ℓ}

  Layer₀ : Layer ℓ ℓ ℓ ℓ ℓ
  Layer₀ = record { C = UCat ; FC = UFC }

  Layer₁ : Layer ℓ ℓ ℓ ℓ ℓ
  Layer₁ = step Layer₀

  Layer₂ : Layer ℓ ℓ ℓ ℓ ℓ
  Layer₂ = step Layer₁

  U₀ = Cosmos (C Layer₀) (FC Layer₀)
  U₁ = Cosmos (C Layer₁) (FC Layer₁)
  U₂ = Cosmos (C Layer₂) (FC Layer₂)

  trivial₀ : Collapsible UCat
  trivial₀ _ _ = tt

  -- BuildUniform provides a uniform family for any layer with a unique
  -- object equality and collapsible morphisms
  -- BuildUniform 为具有唯一对象相等和可坍缩的任意层级提供一致族
  module BuildUniform (L : Layer ℓ ℓ ℓ ℓ ℓ)
    (obj-unique : ∀ (X Y : Category.Obj (C L)) → X ≡ Y)
    (collapse : Collapsible (C L)) where
    private
      module CL = Category (C L)
    retract : ∀ (x : Cosmos (C L) (FC L)) {A : CL.Obj} (s : ShapeOf (FC L) A)
            → CL._⇒_ (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A
    retract x {A} s =
      subst (λ X → X CL.⇒ A)
            (obj-unique A (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)))
            (CL.id {A = A})
    uniform : UniformEmbeddingFamily {C = C L} {FC = FC L}
    uniform = record
      { family = record
        { getData = mkEmbeddingData retract collapse }
      ; next-consistent = λ _ _ → refl
      }

  obj-unique₀ : ∀ (X Y : Category.Obj UCat) → X ≡ Y
  obj-unique₀ _ _ = refl

  obj-unique₁ : ∀ (X Y : Category.Obj (C Layer₁)) → X ≡ Y
  obj-unique₁ _ _ = refl

  obj-unique₂ : ∀ (X Y : Category.Obj (C Layer₂)) → X ≡ Y
  obj-unique₂ _ _ = refl

  uniform₀ = BuildUniform.uniform Layer₀ obj-unique₀ trivial₀
  uniform₁ = BuildUniform.uniform Layer₁ obj-unique₁
               (collapsible→ShapeCat-collapsible {C = C Layer₀} {FC = FC Layer₀} trivial₀)
  uniform₂ = BuildUniform.uniform Layer₂ obj-unique₂
               (collapsible→ShapeCat-collapsible
                {C = C Layer₁} {FC = FC Layer₁}
                (collapsible→ShapeCat-collapsible {C = C Layer₀} {FC = FC Layer₀} trivial₀))

  embed₀₁ : U₀ → U₁
  embed₀₁ = EmbeddingFamily.embed′ (UniformEmbeddingFamily.family uniform₀)

  embed₁₂ : U₁ → U₂
  embed₁₂ = EmbeddingFamily.embed′ (UniformEmbeddingFamily.family uniform₁)

  embed₀₂ : U₀ → U₂
  embed₀₂ x = embed₁₂ (embed₀₁ x)

  unit₀ : U₀
  unit₀ = UnitCosmos {ℓ}

  unit₁ : U₁
  unit₁ = embed₀₁ unit₀

  unit₂ : U₂
  unit₂ = embed₁₂ unit₁

  embed₀₂-unit : embed₀₂ unit₀ ≡ unit₂
  embed₀₂-unit = refl

  private
    resp-≈C : ∀ {x y : U₀} → x ≈C y → embed₀₁ x ≈C embed₀₁ y
    resp-≈C x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
    resp-≈C x≈y ._≈C_.pos-to-shape-eq _ _ = refl
    resp-≈C x≈y ._≈C_.unfold-next-eq s = resp-≈C (_≈C_.unfold-next-eq x≈y s)

    resp-≈C₁ : ∀ {x y : U₁} → x ≈C y → embed₁₂ x ≈C embed₁₂ y
    resp-≈C₁ x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
    resp-≈C₁ x≈y ._≈C_.pos-to-shape-eq _ _ = refl
    resp-≈C₁ x≈y ._≈C_.unfold-next-eq s = resp-≈C₁ (_≈C_.unfold-next-eq x≈y s)

  functorial₀ : FunctorialEmbeddingFamily {C = C Layer₀} {FC = FC Layer₀}
  functorial₀ = record { uniform = uniform₀ ; embed′-resp-≈C = resp-≈C }

  functorial₁ : FunctorialEmbeddingFamily {C = C Layer₁} {FC = FC Layer₁}
  functorial₁ = record { uniform = uniform₁ ; embed′-resp-≈C = resp-≈C₁ }

-- FinCatHierarchy
-- FinCat 层级
module FinCatHierarchy where
  open import Data.Container.Core using (Container)

  -- FinCat n: category with n objects and unique morphisms between any two
  -- FinCat n：具有 n 个对象且任意两对象间有唯一态射的范畴
  FinCat : (n : ℕ) → Category lzero lzero lzero
  FinCat n = record
    { Obj = Fin n
    ; _⇒_ = λ _ _ → ⊤
    ; _≈_ = λ _ _ → ⊤
    ; id = tt
    ; _∘_ = λ _ _ → tt
    ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    ; ∘-resp-≈ = λ _ _ → tt
    ; assoc = tt ; sym-assoc = tt ; identityˡ = tt ; identityʳ = tt ; identity² = tt
    }

  -- Container with shape and position both Fin 2
  -- 形状与位置均为 Fin 2 的容器
  FinContainer : Container lzero lzero
  FinContainer = record { Shape = Fin 2 ; Position = λ _ → Fin 2 }

  -- Constant functor from FinCat n to ContCat picking out FinContainer
  -- 从 FinCat n 到 ContCat 的常值函子，选取 FinContainer
  FinFC : (n : ℕ) → Functor (FinCat n) (ContCat lzero lzero)
  FinFC n = record
    { F₀ = λ _ → FinContainer
    ; F₁ = λ _ → Category.id (ContCat lzero lzero)
    ; identity = ≈M-refl
    ; homomorphism = ≈M-refl
    ; F-resp-≈ = λ _ → ≈M-refl
    }

  FinCat-collapsible : (n : ℕ) → Collapsible (FinCat n)
  FinCat-collapsible n _ _ = tt

  Fin-EmbeddingData : (n : ℕ) (x : Cosmos (FinCat n) (FinFC n)) → EmbeddingData x
  Fin-EmbeddingData n = mkEmbeddingData (λ _ _ → tt) (λ _ _ → tt)

  Fin-EmbeddingFamily : (n : ℕ) → EmbeddingFamily {C = FinCat n} {FC = FinFC n}
  Fin-EmbeddingFamily n = record { getData = Fin-EmbeddingData n }

  Fin-UniformEmbeddingFamily : (n : ℕ) → UniformEmbeddingFamily {C = FinCat n} {FC = FinFC n}
  Fin-UniformEmbeddingFamily n = record
    { family = Fin-EmbeddingFamily n
    ; next-consistent = λ _ _ → refl
    }

  embedFin : (n : ℕ) → Cosmos (FinCat n) (FinFC n)
           → Cosmos (ShapeCat (FinCat n) (FinFC n)) (FC∘π (FinFC n))
  embedFin n x = embed x (Fin-EmbeddingData n x)

  private
    subst-FinFCπ : ∀ {n} {X Y : Category.Obj (ShapeCat (FinCat n) (FinFC n))}
                 → (eq : X ≡ Y) (z : Fin 2)
                 → subst (ShapeOf (FC∘π (FinFC n))) eq z ≡ z
    subst-FinFCπ refl z = refl

    subst-FinFC : ∀ {n} {X Y : Fin n} → (eq : X ≡ Y) (z : Fin 2)
               → subst (ShapeOf (FinFC n)) eq z ≡ z
    subst-FinFC refl z = refl

    Fin-resp-≈C : (n : ℕ) {x y : Cosmos (FinCat n) (FinFC n)}
      → x ≈C y
      → _≈C_ {C = ShapeCat (FinCat n) (FinFC n)} {FC = FC∘π (FinFC n)}
            (embedFin n x) (embedFin n y)
    Fin-resp-≈C n {x} {y} = go x y
      where
        go : (x y : Cosmos (FinCat n) (FinFC n)) → x ≈C y
           → _≈C_ {C = ShapeCat (FinCat n) (FinFC n)} {FC = FC∘π (FinFC n)}
                  (embedFin n x) (embedFin n y)
        go x y x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
        go x y x≈y ._≈C_.pos-to-shape-eq {A} s p =
          let
            A₀     = proj₁ A
            eq₀    = _≈C_.unfoldFunctor₀-eq x≈y {A = A₀} s
            pts-eq = _≈C_.pos-to-shape-eq x≈y {A = A₀} s p
            x-pts  = Unfolding.pos-to-shape (out x) {A = A₀} s p
            y-pts  = Unfolding.pos-to-shape (out y) {A = A₀} s p
          in
          begin
            subst (ShapeOf (FC∘π (FinFC n)))
              (go x y x≈y ._≈C_.unfoldFunctor₀-eq {A = A} s)
              (Unfolding.pos-to-shape (out (embedFin n x)) {A = A} s p)
              ≡⟨ subst-FinFCπ (go x y x≈y ._≈C_.unfoldFunctor₀-eq {A = A} s) _ ⟩
            Unfolding.pos-to-shape (out (embedFin n x)) {A = A} s p
              ≡⟨ refl ⟩
            x-pts
              ≡⟨ sym (subst-FinFC eq₀ x-pts) ⟩
            subst (ShapeOf (FinFC n)) eq₀ x-pts
              ≡⟨ pts-eq ⟩
            y-pts
              ≡⟨ sym refl ⟩
            Unfolding.pos-to-shape (out (embedFin n y)) {A = A} s p
          ∎
        go x y x≈y ._≈C_.unfold-next-eq {A} s =
          let
            A₀ = proj₁ A
          in
          go (Unfolding.unfold-next (out x) {A = A₀} s)
             (Unfolding.unfold-next (out y) {A = A₀} s)
             (_≈C_.unfold-next-eq x≈y {A = A₀} s)

  Fin-FunctorialEmbeddingFamily : (n : ℕ) → FunctorialEmbeddingFamily {C = FinCat n} {FC = FinFC n}
  Fin-FunctorialEmbeddingFamily n = record
    { uniform = Fin-UniformEmbeddingFamily n
    ; embed′-resp-≈C = Fin-resp-≈C n
    }

  Fin-LambekConsistency : (n : ℕ) → LambekConsistency (Fin-UniformEmbeddingFamily n)
  Fin-LambekConsistency n = mkLambekConsistency (Fin-UniformEmbeddingFamily n)

  module Fin2Hierarchy where
    Layer₀ : Layer lzero lzero lzero lzero lzero
    Layer₀ = record { C = FinCat 2 ; FC = FinFC 2 }

    Layer₁ : Layer lzero lzero lzero lzero lzero
    Layer₁ = step Layer₀

    U₀ = Cosmos (C Layer₀) (FC Layer₀)
    U₁ = Cosmos (C Layer₁) (FC Layer₁)

    embed₀₁ : U₀ → U₁
    embed₀₁ = embedFin 2

    collapse₁ : Collapsible (C Layer₁)
    collapse₁ _ _ = tt

-- StrictLift
-- 严格层级提升
module StrictLift where
  open import Data.Container.Core using (Container)
  open import Level using (Lift; lift)

  -- LiftContainer lifts a container's shape and position types by given levels
  -- LiftContainer 按给定层级提升容器的形状和位置类型
  LiftContainer : ∀ {s p : Level} (s′ p′ : Level) → Container s p
                → Container (s ⊔ s′) (p ⊔ p′)
  LiftContainer {s} {p} s′ p′ C = record
    { Shape    = Lift s′ (Container.Shape C)
    ; Position = λ { (lift sh) → Lift p′ (Container.Position C sh) }
    }

  record StrictLayer (o h e s p : Level) : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
    field
      C  : Category o h e
      FC : Functor C (ContCat s p)

  open StrictLayer public

  -- strictStep steps a strict layer while also raising the container levels
  -- strictStep 在步进严格层级的同时提升容器层级
  strictStep : ∀ {o h e s p s′ p′ : Level}
             → (liftFC : ∀ {o′ h′ e′} {C′ : Category o′ h′ e′}
                       → Functor C′ (ContCat s p)
                       → Functor C′ (ContCat (s ⊔ s′) (p ⊔ p′)))
             → StrictLayer o h e s p
             → StrictLayer (o ⊔ s) (h ⊔ s) e (s ⊔ s′) (p ⊔ p′)
  strictStep liftFC L = record
    { C  = ShapeCat (StrictLayer.C L) (StrictLayer.FC L)
    ; FC = liftFC (FC∘π (StrictLayer.FC L))
    }

  record LiftsMorphisms (s′ p′ : Level)
    {o h e s p : Level} {C : Category o h e}
    (FC : Functor C (ContCat s p)) : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ s′ ⊔ p′)) where
    field
      liftedFC : Functor C (ContCat (s ⊔ s′) (p ⊔ p′))

  canonicalLiftFC : ∀ {s p s′ p′ : Level}
    → (∀ {o h e} {C : Category o h e} (FC : Functor C (ContCat s p))
       → LiftsMorphisms s′ p′ FC)
    → ∀ {o′ h′ e′} {C′ : Category o′ h′ e′}
    → Functor C′ (ContCat s p)
    → Functor C′ (ContCat (s ⊔ s′) (p ⊔ p′))
  canonicalLiftFC lm FC = LiftsMorphisms.liftedFC (lm FC)
