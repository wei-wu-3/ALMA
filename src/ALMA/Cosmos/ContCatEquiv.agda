------------------------------------------------------------------------
-- ContCatEquiv: container isomorphisms transport along isos in C
-- ContCatEquivEmbedding: lift this transport to natural transformations
-- via the embedding ContCat → [Setoids, Setoids]
-- ShapeCat: Grothendieck construction of the shape functor
--
-- 分别定义：容器同构沿 C 中同构的传输结构 ContCatEquiv、
-- 通过容器嵌入将传输提升为自然变换的 ContCatEquivEmbedding、
-- 形状范畴 ShapeCat（由形状函子的 Grothendieck 构造得到）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCatEquiv where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; shape)
open import Data.Container.Morphism using (id; _∘_)
open import Data.Container.Relation.Binary.Pointwise as PW using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Elements using (Elements)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)

open import ALMA.Cosmos.ContCategory
  using (_≈M_; ≈M-sym; ≈M-trans; ∘M-assoc; ∘M-identityʳ; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ; ContCat; module ≈M-Reasoning)
open import ALMA.Cosmos.ContFunctor using (ContEmbedding; ⟦_⟧)

-- ContCatEquiv: container isomorphism transport along isomorphisms
-- 沿同构的容器传输结构（容器态射升级为容器同构）
module _ {o h e s p : Level}
         (C : Category o h e)
         (containerFunctor : Functor C (ContCat s p)) where
  -- Parameterised record: packages the source category C and the
  -- functor containerFunctor as module context; has no fields, so
  -- instantiation is trivial (record {})
  -- 参数化 record：将源范畴 C 与函子 containerFunctor 封装为模块上下文；
  -- 无字段，故实例化是平凡的（record {}）
  record ContCatEquiv : Set where

    -- The core groupoid of C
    -- C 的核心广群
    private
      module C = Category C
      open Functor containerFunctor
      open import Categories.Category.Construction.Core C using (Core)
    CoreC = Core

    -- Inclusion (forgetful) functor from the core to the original category
    -- 从核心广群到原范畴的包含（遗忘）函子
    open import Categories.Morphism (ContCat s p) renaming (_≅_ to ContIso)
    open ContIso renaming (from to contFrom)
    open import Categories.Morphism C using (_≅_) renaming (module ≅ to C≅)
    open _≅_ using (from; to)
    open import Categories.Morphism.IsoEquiv C using (_≃_; module _≃_)
    Core→C : Functor CoreC C
    Core→C = record
      { F₀ = λ X → X
      ; F₁ = _≅_.from
      ; identity     = C.Equiv.refl
      ; homomorphism = λ {_ _ _ f g} → C.Equiv.refl
      ; F-resp-≈     = λ {_ _ f g} f≃g → _≃_.from-≈ f≃g
      }

    -- Transport functor along isomorphisms (now a composition of standard functors)
    -- 沿同构的传输函子（此处为标准函子的复合）
    transportFunctor : Functor CoreC (ContCat s p)
    transportFunctor = containerFunctor ∘F Core→C

    -- Coherence theorems: all come for free from the functor laws
    -- 融贯性定理：均由函子定律直接得出
    private
      module TF = Functor transportFunctor
    transpCont-refl : ∀ {A} → TF.F₁ (C≅.refl {A}) ≈M id (F₀ A)
    transpCont-refl = TF.identity
    transpCont-sym : ∀ {A B} (eq : A ≅ B) →
      TF.F₁ (C≅.sym eq) ∘ TF.F₁ eq ≈M id (F₀ A)
    transpCont-sym eq = ≈M-trans
      (≈M-sym (TF.homomorphism {f = eq} {g = C≅.sym eq}))
      (≈M-trans (F-resp-≈ (_≅_.isoˡ eq)) TF.identity)
    transpCont-trans : ∀ {A₁ A₂ A₃} (eq1 : A₁ ≅ A₂) (eq2 : A₂ ≅ A₃) →
      TF.F₁ (C≅.trans eq1 eq2) ≈M (TF.F₁ eq2 ∘ TF.F₁ eq1)
    transpCont-trans eq1 eq2 = TF.homomorphism {f = eq1} {g = eq2}

    -- Transport produces a container isomorphism (ContIso)
    -- 传输产生容器同构 (ContIso)
    transpIso : ∀ {A₁ A₂} → A₁ ≅ A₂ → ContIso (F₀ A₁) (F₀ A₂)
    transpIso eq = record
      { from = TF.F₁ eq
      ; to   = TF.F₁ (C≅.sym eq)
      ; iso  = record
        { isoˡ = transpCont-sym eq
        ; isoʳ = transpCont-sym (C≅.sym eq)
        }
      }

    -- Transport of morphisms in C along isomorphisms
    -- 沿同构传输 C 中的态射
    transportMorphism : ∀ {A₁ A₂ B₁ B₂} (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂) 
                      → (A₁ C.⇒ B₁) → (A₂ C.⇒ B₂)
    transportMorphism eqA eqB f = from eqB C.∘ f C.∘ to eqA

    -- Naturality of container transport with respect to morphism transport
    -- 容器传输关于态射传输的自然性
    module _ where
      open ≈M-Reasoning
      act-natural : ∀ {A₁ A₂ B₁ B₂} (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂) (f : A₁ C.⇒ B₁)
        → (contFrom (transpIso eqB) ∘ F₁ f)
          ≈M (F₁ (transportMorphism eqA eqB f) ∘ contFrom (transpIso eqA))
      act-natural {A₁} {A₂} {B₁} {B₂} eqA eqB f = ≈M-sym R≈L
        where
          FtA  = contFrom (transpIso eqA)
          Ff   = F₁ f
          FtB  = contFrom (transpIso eqB)
          Ff∘to = F₁ (f C.∘ to eqA)
          R≈L : F₁ (transportMorphism eqA eqB f) ∘ FtA ≈M FtB ∘ Ff
          R≈L = begin
            F₁ (transportMorphism eqA eqB f) ∘ FtA
              ≈⟨ ∘M-resp-≈ˡ {f = FtA} (homomorphism {f = f C.∘ to eqA} {g = from eqB}) ⟩
            (FtB ∘ Ff∘to) ∘ FtA
              ≈⟨ ∘M-assoc {f = FtA} {g = Ff∘to} {h = FtB} ⟩
            FtB ∘ (Ff∘to ∘ FtA)
              ≈⟨ ∘M-resp-≈ʳ {g = FtB}
                  (∘M-resp-≈ˡ {f = FtA} (homomorphism {f = to eqA} {g = f})) ⟩
            FtB ∘ ((Ff ∘ F₁ (to eqA)) ∘ FtA)
              ≈⟨ ∘M-resp-≈ʳ {g = FtB}
                  (∘M-assoc {f = FtA} {g = F₁ (to eqA)} {h = Ff}) ⟩
            FtB ∘ (Ff ∘ (F₁ (to eqA) ∘ FtA))
              ≈⟨ ∘M-resp-≈ʳ {g = FtB}
                  (∘M-resp-≈ʳ {g = Ff} (transpCont-sym eqA)) ⟩
            FtB ∘ (Ff ∘ id (F₀ _))
              ≈⟨ ∘M-resp-≈ʳ {g = FtB} (∘M-identityʳ {f = Ff}) ⟩
            FtB ∘ Ff
              ∎

-- ContCatEquivEmbedding: transport lifted to natural transformations
-- 将同构传输通过容器嵌入提升为自然变换
module ContCatEquivEmbedding {o h e s p} (ℓ′ : Level)
         (C : Category o h e)
         (F : Functor C (ContCat s p)) where
  private
    module CF = Functor F
    CCE : ContCatEquiv C F
    CCE = record {}
    -- Target category: endofunctor category [Setoids, Setoids]
    -- 目标范畴：自函子范畴 [Setoids, Setoids]
    Tgt = Functors (Setoids (p ⊔ ℓ′) (p ⊔ ℓ′)) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′))
    module TgtCat = Category Tgt
    -- Combinators for natural transformation equivalence
    -- 自然变换等价组合子
    open TgtCat using (_≈_) renaming (_∘_ to _∙_; id to idF)
    -- Import transport structure from ContCatEquiv
    -- 从 ContCatEquiv 导入传输结构
    open ContCatEquiv CCE
      using (transportFunctor; transpIso; transpCont-sym; transpCont-refl; transpCont-trans; CoreC)
    open import Categories.Morphism (ContCat s p) renaming (_≅_ to ContIso)
    open ContIso using (from)
    open import Categories.Morphism C using (_≅_) renaming (module ≅ to C≅)
    -- Explicitly instantiate the polynomial functor interpretation
    -- 显式实例化多项式函子解释
    ⟦_⟧′ : Container s p → Functor (Setoids (p ⊔ ℓ′) (p ⊔ ℓ′)) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′))
    ⟦_⟧′ = ⟦_⟧ {s = s} {p = p} {ℓ = ℓ′}

  -- Container embedding functor ContCat → [Setoids, Setoids]
  -- 容器嵌入函子 ContCat → [Setoids, Setoids]
  ContEmb = ContEmbedding {s = s} {p = p} {ℓ = ℓ′}
  open Functor ContEmb

  -- Lifted transport functor: CoreC → [Setoids, Setoids]
  -- 提升的传输函子：CoreC → [Setoids, Setoids]
  liftedTransport : Functor CoreC Tgt
  liftedTransport = ContEmb ∘F transportFunctor

  -- Natural transformation induced by transport along isomorphism
  -- 沿同构传输的自然变换
  transpNat : ∀ {A B} (iso : A ≅ B) → NaturalTransformation ⟦ CF.F₀ A ⟧′ ⟦ CF.F₀ B ⟧′
  transpNat iso = F₁ (from (transpIso iso))

  transpNat-refl : ∀ {A} → transpNat (C≅.refl {A}) ≈ idF
  transpNat-refl {A} {X} {x = (s , k)} =
    let open _≈M_ (transpCont-refl {A = A}) using (shape-eq; pos-eq)
    in shape-eq s PW., λ p → Setoid.reflexive X (cong k (pos-eq s p))

  transpNat-sym : ∀ {A B} (eq : A ≅ B) → transpNat (C≅.sym eq) ∙ transpNat eq ≈ idF
  transpNat-sym {A} {B} eq {X} {x = (s , k)} =
    let open _≈M_ (transpCont-sym eq) using (shape-eq; pos-eq)
    in shape-eq s PW., λ p → Setoid.reflexive X (cong k (pos-eq s p))

  transpNat-trans : ∀ {A B C} (eq1 : A ≅ B) (eq2 : B ≅ C) →
                    transpNat (C≅.trans eq1 eq2) ≈ (transpNat eq2 ∙ transpNat eq1)
  transpNat-trans {A} {B} {C} eq1 eq2 {X} {x = (s , k)} =
    let open _≈M_ (transpCont-trans eq1 eq2) using (shape-eq; pos-eq)
    in shape-eq s PW., λ p → Setoid.reflexive X (cong k (pos-eq s p))

-- ShapeCat: the category of shapes (Grothendieck construction)
-- 形状范畴（Grothendieck 构造）
module _ {o h e s p} (C : Category o h e) (F : Functor C (ContCat s p)) where
  open Functor F
  -- Functor forgetting positions, retaining only shapes
  -- 遗忘位置、仅保留形状的函子
  ShapeForget : Functor (ContCat s p) (Sets s)
  ShapeForget = record
    { F₀           = λ Ctr → Data.Container.Core.Shape Ctr
    ; F₁           = λ f → shape f
    ; identity     = λ _ → refl
    ; homomorphism = λ _ → refl
    ; F-resp-≈     = λ f≈g x → _≈M_.shape-eq f≈g x
    }
  -- The shape functor: extracts the shape set from the container functor
  -- 形状函子：从容器函子中提取形状集
  shapeFunctor : Functor C (Sets s)
  shapeFunctor = ShapeForget ∘F F
  -- The category of shapes over C (Grothendieck construction / Elements)
  -- C 上的形状范畴（Grothendieck 构造 / Elements 构造）
  ShapeCat : Category (o ⊔ s) (h ⊔ s) e
  ShapeCat = Elements shapeFunctor
