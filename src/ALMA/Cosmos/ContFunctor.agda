------------------------------------------------------------------------
-- Containers as polynomial functors on Setoids
-- 容器作为 Setoids 上的多项式函子
--
-- Builds functor ⟦ C ⟧ and embedding ContCat → [Setoids, Setoids]
-- Proves preservation of identity, composition, and the equivalence _≈M_
-- Note: faithfulness holds by definition (projection + β-reduction)
-- 构造函子 ⟦ C ⟧ 及嵌入 ContCat → [Setoids, Setoids]，
-- 证明恒等态射、复合及等价关系 _≈M_ 的保持性；
-- 注：忠实性由定义直接成立（投影 + β-归约）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContFunctor where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; map; _⇒_)
open import Data.Container.Morphism renaming (id to idCont; _∘_ to _∘Cont_)
open import Data.Container.Relation.Binary.Equality.Setoid using (setoid)
open import Data.Container.Relation.Binary.Pointwise as PW using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper; id; _∘ᵥ_)

open import ALMA.Cosmos.ContCategory using (_≈M_; ContCat)

-- For a fixed container C, builds the polynomial functor ⟦ C ⟧ : Setoids → Setoids
-- 对固定容器 C，构造多项式函子 ⟦ C ⟧ : Setoids → Setoids
module _ {s p ℓ′ : Level} where
  -- Parameterised record: packages C and level parameters as module
  -- context; has no fields, so instantiation is trivial (record {})
  -- 参数化 record：将 C 与层级参数封装为模块上下文；
  -- 无字段，故实例化是平凡的（record {}）
  record ContFunctor (C : Container s p) : Set where

    private
      module Src = Category (Setoids ℓ′ ℓ′) renaming
        ( id to idS ; _∘_ to _∘S_ ; _⇒_ to _⇒S_ ; _≈_ to _≈S_ )
      module Tgt = Category (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)) renaming
        ( id to idT ; _∘_ to _∘T_ ; _⇒_ to _⇒T_ ; _≈_ to _≈T_ )
    -- Object mapping: interpret C as a setoid-valued functor
    -- 对象映射：将 C 解释为取值于 Setoids 的函子
    ⟦_⟧ₛ : Setoid ℓ′ ℓ′ → Setoid (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)
    ⟦_⟧ₛ A = setoid A C
    -- Morphism mapping: lift a setoid function to the container extension
    -- 态射映射：将集合间的函数提升为容器扩张上的函数
    mapₛ : {A B : Setoid ℓ′ ℓ′} → A Src.⇒S B → ⟦ A ⟧ₛ Tgt.⇒T ⟦ B ⟧ₛ
    mapₛ {A} {B} f = record
      { to   = map {C = C} {X = Setoid.Carrier A} {Y = Setoid.Carrier B} (Func.to f)
      ; cong = λ { (sh , ps) → sh , λ p → Func.cong f (ps p) }
      }
    -- Preservation of identity: mapₛ (id) ≈ id
    -- 恒等态射的保持：mapₛ (id) ≈ id
    map-id≗ : {A : Setoid ℓ′ ℓ′} → mapₛ (Src.idS {A}) Tgt.≈T Tgt.idT {A = ⟦_⟧ₛ A}
    map-id≗ {A} {x = (s , h)} =
      refl PW., λ p → Setoid.refl A {x = h p}
    -- Preservation of composition: mapₛ (g ∘ f) ≈ mapₛ g ∘ mapₛ f
    -- 复合的保持：mapₛ (g ∘ f) ≈ mapₛ g ∘ mapₛ f
    map-∘≗ : {A B D : Setoid ℓ′ ℓ′} {f : A Src.⇒S B} {g : B Src.⇒S D} →
             mapₛ (g Src.∘S f) Tgt.≈T (mapₛ g Tgt.∘T mapₛ f)
    map-∘≗ {A} {B} {D} {f = f} {g = g} {x = (s , h)} =
      refl PW., λ p → Setoid.refl D {x = Func.to g (Func.to f (h p))}
    -- Preservation of equivalence: f ≈ g → mapₛ f ≈ mapₛ g
    -- 等价的保持：f ≈ g → mapₛ f ≈ mapₛ g
    map-resp-≗ : {A B : Setoid ℓ′ ℓ′} {f g : A Src.⇒S B} →
                 f Src.≈S g → mapₛ f Tgt.≈T mapₛ g
    map-resp-≗ {A} {B} {f} {g} f≈g {x = (s , h)} =
      refl PW., λ p → f≈g {x = h p}
    -- Assemble the polynomial functor ⟦ C ⟧ : Setoids → Setoids
    -- 组装多项式函子 ⟦ C ⟧ : Setoids → Setoids
    functor : Functor (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′))
    functor = record
      { F₀           = ⟦_⟧ₛ
      ; F₁           = mapₛ
      ; identity     = λ {A} → map-id≗ {A = A}
      ; homomorphism = λ {A} {B} {D} {f} {g} → map-∘≗ {A = A} {B = B} {D = D} {f = f} {g = g}
      ; F-resp-≈     = λ {A} {B} {f} {g} f≈g → map-resp-≗ {A = A} {B = B} {f = f} {g = g} f≈g
      }

  private
    module FuncCat = Category (Functors (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)))
  -- The polynomial functor ⟦ C ⟧ associated to a container C
  -- 容器 C 所对应的多项式函子 ⟦ C ⟧
  ⟦_⟧ : Container s p → Functor (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′))
  ⟦ C ⟧ = ContFunctor.functor {C = C} (record {})
  -- Lift a container morphism m : C ⇒ D to a natural transformation ⟦ C ⟧ ⟹ ⟦ D ⟧
  -- 将容器态射 m : C ⇒ D 提升为自然变换 ⟦ C ⟧ ⟹ ⟦ D ⟧
  mapNT : {C D : Container s p} → (C ⇒ D) → NaturalTransformation ⟦ C ⟧ ⟦ D ⟧
  mapNT {C} {D} m = ntHelper record
    { η = λ X → record
      { to   = λ { (s , k) → let open _⇒_ m in (shape s , k ∘ position) }
      ; cong = λ { (refl PW., eq) → let open _⇒_ m in refl PW., λ p → eq (position p) }
      }
    -- Naturality: η_Y ∘ ⟦ C ⟧ f ≈ ⟦ D ⟧ f ∘ η_X
    -- 自然性：η_Y ∘ ⟦ C ⟧ f ≈ ⟦ D ⟧ f ∘ η_X
    ; commute = λ {X Y} f {x} →
        let open _⇒_ m
            (s , k) = x
        in refl PW., λ p → Setoid.refl Y {x = Func.to f (k (position p))}
    }
  -- Identity preservation: mapNT (id C) ≈ id
  -- 恒等态射的保持：mapNT (id C) ≈ id
  mapNT-id : {C : Container s p}
           → mapNT (idCont C) FuncCat.≈ id
  mapNT-id {C} {X} {x = (s , k)} =
    refl PW., λ p → Setoid.refl X {x = k p}
  -- Composition preservation: mapNT (m ∘ n) ≈ mapNT m ∘ᵥ mapNT n
  -- 复合的保持：mapNT (m ∘ n) ≈ mapNT m ∘ᵥ mapNT n
  mapNT-∘ : {C D E : Container s p} {m : D ⇒ E} {n : C ⇒ D}
          → mapNT (m ∘Cont n) FuncCat.≈ (mapNT m ∘ᵥ mapNT n)
  mapNT-∘ {C} {D} {E} {m} {n} {X} {x = (s , k)} =
    refl PW., λ p → Setoid.refl X
  -- Equivalence preservation: m ≈M n → mapNT m ≈ mapNT n
  -- 等价的保持：m ≈M n → mapNT m ≈ mapNT n
  mapNT-resp-≈ : {C D : Container s p} {m n : C ⇒ D}
               → m ≈M n → mapNT m FuncCat.≈ mapNT n
  mapNT-resp-≈ {C} {D} {m} {n} eq {X} {x = (s , k)} =
    eq.shape-eq s PW., λ q → Setoid.reflexive X (cong k (eq.pos-eq s q))
    where module eq = _≈M_ eq
  -- The embedding functor ContCat → [Setoids, Setoids]
  -- 嵌入函子 ContCat → [Setoids, Setoids]
  ContEmbedding : Functor (ContCat s p) (Functors (Setoids ℓ′ ℓ′) (Setoids (s ⊔ p ⊔ ℓ′) (s ⊔ p ⊔ ℓ′)))
  ContEmbedding = record
    { F₀        = ⟦_⟧
    ; F₁        = mapNT
    ; identity  = λ {A} {X} {x} → mapNT-id {C = A} {X} {x}
    ; homomorphism = λ {X Y Z f g} {S} {x} → mapNT-∘ {m = g} {n = f} {S} {x}
    ; F-resp-≈  = λ {A B f g} eq {X} {x} → mapNT-resp-≈ eq {X} {x}
    }
