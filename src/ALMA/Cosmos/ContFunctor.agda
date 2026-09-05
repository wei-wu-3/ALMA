------------------------------------------------------------------------
-- Containers as polynomial functors on Setoids
-- 容器作为 Setoids 上的多项式函子
--
-- Builds functor ⟦ C ⟧ and embedding ContCat → [Setoids, Setoids]
-- Proves preservation of identity, composition, and the equivalence _≈M_
-- Note: faithfulness is obtained by choosing a test object and using projection and β-reduction
-- 构造函子 ⟦ C ⟧ 及嵌入 ContCat → [Setoids, Setoids]，
-- 证明恒等态射、复合及等价关系 _≈M_ 的保持性；
-- 注：忠实性可由选取测试对象并利用投影与 β-归约得证
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContFunctor where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence) renaming (setoid to discreteSetoid)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func; _⇔_; mk⇔)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; map; _⇒_)
open import Data.Container.Morphism renaming (id to idCont; _∘_ to _∘Cont_)
open import Data.Container.Relation.Binary.Equality.Setoid using (setoid)
open import Data.Container.Relation.Binary.Pointwise as PW using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core
  using (NaturalTransformation; ntHelper; _∘ᵥ_)
  renaming (id to idNT)

open import ALMA.Cosmos.ContCategory using (_≈M_; ContCat)

-- For a fixed container C, builds the polynomial functor ⟦ C ⟧ : Setoids → Setoids
-- 对固定容器 C，构造多项式函子 ⟦ C ⟧ : Setoids → Setoids
module _ {s p ℓ : Level} where

  -- The level of the source and target setoids.
  -- 源与目标 Setoids 的层级。
  -- The source level only needs to host the position types (p) plus
  -- an arbitrary extra level ℓ for greater generality.
  -- 源层级只需容纳位置类型（p）并额外加上任意层级 ℓ 以保持一般性。
  srcLevel = p ⊔ ℓ

  -- The target level needs to host shapes (s), positions (p), and ℓ.
  -- 目标层级需容纳形状（s）、位置（p）以及 ℓ。
  tgtLevel = s ⊔ p ⊔ ℓ

  -- The endofunctor category [Setoids, Setoids] on appropriate levels.
  -- 相应层级上的自函子范畴 [Setoids, Setoids]。
  EndoFunctors = Functors (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)

  -- The category of endofunctors, used for natural transformation equivalence.
  -- 自函子范畴，用于自然变换等价。
  module FuncCat = Category EndoFunctors

  -- Parameterised record: packages C and level parameters as module context.
  -- 参数化 record：将 C 与层级参数封装为模块上下文。
  record ContFunctor (C : Container s p) : Set where
    private
      module Src = Category (Setoids srcLevel srcLevel) renaming
        ( id to idS ; _∘_ to _∘S_ ; _⇒_ to _⇒S_ ; _≈_ to _≈S_ )
      module Tgt = Category (Setoids tgtLevel tgtLevel) renaming
        ( id to idT ; _∘_ to _∘T_ ; _⇒_ to _⇒T_ ; _≈_ to _≈T_ )

      -- Object mapping: interpret C as a setoid-valued functor.
      -- 对象映射：将 C 解释为取值于 Setoids 的函子。
      ⟦_⟧ₛ : Setoid srcLevel srcLevel → Setoid tgtLevel tgtLevel
      ⟦_⟧ₛ A = setoid A C

      -- Morphism mapping: lift a setoid function to the container extension.
      -- 态射映射：将 setoid 态射提升为容器扩张上的 setoid 态射。
      mapₛ : {A B : Setoid srcLevel srcLevel} → A Src.⇒S B → ⟦ A ⟧ₛ Tgt.⇒T ⟦ B ⟧ₛ
      mapₛ {A} {B} f = record
        { to   = map {C = C} {X = Setoid.Carrier A} {Y = Setoid.Carrier B} (Func.to f)
        ; cong = λ { (sh , ps) → sh , λ p → Func.cong f (ps p) }
        }

      -- Preservation of identity: mapₛ (id) ≈ id.
      -- 恒等态射的保持：mapₛ (id) ≈ id。
      map-id≗ : {A : Setoid srcLevel srcLevel} → mapₛ (Src.idS {A}) Tgt.≈T Tgt.idT {A = ⟦_⟧ₛ A}
      map-id≗ {A} {x = (s , h)} = refl PW., λ p → Setoid.refl A {x = h p}

      -- Preservation of composition: mapₛ (g ∘ f) ≈ mapₛ g ∘ mapₛ f.
      -- 复合的保持：mapₛ (g ∘ f) ≈ mapₛ g ∘ mapₛ f。
      map-∘≗ : {A B D : Setoid srcLevel srcLevel} {f : A Src.⇒S B} {g : B Src.⇒S D} →
               mapₛ (g Src.∘S f) Tgt.≈T (mapₛ g Tgt.∘T mapₛ f)
      map-∘≗ {A} {B} {D} {f = f} {g = g} {x = (s , h)} =
        refl PW., λ p → Setoid.refl D {x = Func.to g (Func.to f (h p))}

      -- Preservation of equivalence: f ≈ g → mapₛ f ≈ mapₛ g.
      -- 等价的保持：f ≈ g → mapₛ f ≈ mapₛ g。
      map-resp-≗ : {A B : Setoid srcLevel srcLevel} {f g : A Src.⇒S B} →
                   f Src.≈S g → mapₛ f Tgt.≈T mapₛ g
      map-resp-≗ {A} {B} {f} {g} f≈g {x = (s , h)} =
        refl PW., λ p → f≈g {x = h p}

    -- Assemble the polynomial functor ⟦ C ⟧ : Setoids → Setoids.
    -- 组装多项式函子 ⟦ C ⟧ : Setoids → Setoids。
    functor : Functor (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)
    functor = record
      { F₀           = ⟦_⟧ₛ
      ; F₁           = mapₛ
      ; identity     = λ {A} → map-id≗ {A = A}
      ; homomorphism = λ {A} {B} {D} {f} {g} → map-∘≗ {A = A} {B = B} {D = D} {f = f} {g = g}
      ; F-resp-≈     = λ {A} {B} {f} {g} f≈g → map-resp-≗ {A = A} {B = B} {f = f} {g = g} f≈g
      }

  -- The polynomial functor ⟦ C ⟧ associated to a container C.
  -- 容器 C 所对应的多项式函子 ⟦ C ⟧。
  ⟦_⟧ : Container s p → Functor (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)
  ⟦ C ⟧ = ContFunctor.functor {C = C} (record {})

  -- Lift a container morphism m : C ⇒ D to a natural transformation ⟦ C ⟧ ⟹ ⟦ D ⟧.
  -- 将容器态射 m : C ⇒ D 提升为自然变换 ⟦ C ⟧ ⟹ ⟦ D ⟧。
  mapNT : {C D : Container s p} → (C ⇒ D) → NaturalTransformation ⟦ C ⟧ ⟦ D ⟧
  mapNT {C} {D} m = ntHelper record
    { η = λ X → record
      { to   = λ { (s , k) → let open _⇒_ m in (shape s , k ∘ position) }
      ; cong = λ { (refl PW., eq) → let open _⇒_ m in refl PW., λ p → eq (position p) }
      }
    -- Naturality: η_Y ∘ ⟦ C ⟧ f ≈ ⟦ D ⟧ f ∘ η_X.
    -- 自然性：η_Y ∘ ⟦ C ⟧ f ≈ ⟦ D ⟧ f ∘ η_X。
    ; commute = λ {X Y} f {x} →
        let open _⇒_ m
            (s , k) = x
        in refl PW., λ p → Setoid.refl Y {x = Func.to f (k (position p))}
    }

  -- Identity preservation: mapNT (id C) ≈ id.
  -- 恒等态射的保持：mapNT (id C) ≈ id。
  mapNT-id : {C : Container s p} → mapNT (idCont C) FuncCat.≈ idNT
  mapNT-id {C} {X} {x = (s , k)} = refl PW., λ p → Setoid.refl X {x = k p}

  -- Composition preservation: mapNT (m ∘ n) ≈ mapNT m ∘ᵥ mapNT n.
  -- 复合的保持：mapNT (m ∘ n) ≈ mapNT m ∘ᵥ mapNT n。
  mapNT-∘ : {C D E : Container s p} {m : D ⇒ E} {n : C ⇒ D}
          → mapNT (m ∘Cont n) FuncCat.≈ (mapNT m ∘ᵥ mapNT n)
  mapNT-∘ {C} {D} {E} {m} {n} {X} {x = (s , k)} =
    refl PW., λ p → Setoid.refl X

  -- Equivalence preservation: m ≈M n → mapNT m ≈ mapNT n.
  -- 等价的保持：m ≈M n → mapNT m ≈ mapNT n。
  mapNT-resp-≈ : {C D : Container s p} {m n : C ⇒ D}
               → m ≈M n → mapNT m FuncCat.≈ mapNT n
  mapNT-resp-≈ {C} {D} {m} {n} eq {X} {x = (s , k)} =
    eq.shape-eq s PW., λ q → Setoid.reflexive X (cong k (eq.pos-eq s q))
    where module eq = _≈M_ eq

  -- The embedding functor ContCat → [Setoids, Setoids].
  -- 嵌入函子 ContCat → [Setoids, Setoids]。
  ContEmbedding : Functor (ContCat s p) EndoFunctors
  ContEmbedding = record
    { F₀         = ⟦_⟧
    ; F₁         = mapNT
    ; identity   = λ {A} {X} {x} → mapNT-id {C = A} {X} {x}
    ; homomorphism = λ {X Y Z f g} {S} {x} → mapNT-∘ {m = g} {n = f} {S} {x}
    ; F-resp-≈  = λ {A B f g} eq {X} {x} → mapNT-resp-≈ eq {X} {x}
    }

  -- Faithfulness of the embedding: mapNT m ≈ mapNT n → m ≈M n.
  -- 嵌入函子的忠实性：mapNT m ≈ mapNT n → m ≈M n。
  --
  -- For each shape s, take the discrete setoid on Lift srcLevel (Position C s)
  -- as test object, and plug k = lift into the naturality equality.
  -- The shape component yields shape-eq directly; the position component,
  -- after applying cong lower, yields exactly pos-eq up to transport.
  -- 对每个形状 s，取 Lift srcLevel (Position C s) 上的离散 setoid 作为测试对象，
  -- 代入 k = lift。形状分量直接给出 shape-eq；位置分量经 cong lower
  -- 后恰好给出在替换（transport）意义下的 pos-eq。
  ContEmbedding-faithful : {C D : Container s p} {m n : C ⇒ D}
                          → mapNT m FuncCat.≈ mapNT n → m ≈M n
  ContEmbedding-faithful {C} {D} {m} {n} nt-eq =
    record
      { shape-eq = λ s → PW.Pointwise.shape (get-eq s)
      ; pos-eq   = λ s q → cong lower (PW.Pointwise.position (get-eq s) q)
      }
    where
      get-eq : (s : Shape C) → _
      get-eq s = nt-eq {discreteSetoid (Lift srcLevel (Position C s))} { (s , lift) }

  -- Equivalence between container‑morphism equality and natural‑transformation equality
  -- 容器态射等价与导出自然变换等价之间的双向等价关系
  --
  -- Forward direction (to):
  --   If the lifted natural‑transformations are equal for all setoid‑objects,
  --   then the original container morphisms are equal under _≈M_.
  --   This is faithfulness of the embedding functor ContEmbedding.
  -- 正向（to）：
  --   若提升得到的两个自然变换在所有 Setoid 对象上均相等，
  --   则原始容器态射满足容器等价关系 _≈M_。
  --   该方向证明嵌入函子 ContEmbedding 具有忠实性。
  --
  -- Backward direction (from):
  --   If two container morphisms satisfy _≈M_, then their lifted natural‑transformations
  --   are point‑wise equal over every setoid object.
  --   This is equivalence‑preservation of the embedding functor.
  -- 反向（from）：
  --   若两个容器态射满足容器等价 _≈M_，则它们导出的自然变换
  --   在任意 Setoid 对象上分量相等。
  --   该方向证明嵌入函子保持态射等价关系。
  mapNT-iff-≈M : {C D : Container s p} {m n : C ⇒ D}
               → (mapNT m FuncCat.≈ mapNT n) ⇔ (m ≈M n)
  mapNT-iff-≈M = mk⇔ ContEmbedding-faithful mapNT-resp-≈
