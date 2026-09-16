------------------------------------------------------------------------
-- FinCatInnerSewing — inner-preserving strict embedding and its iteration
-- FinCat 内层缝合 —— 保内层严格嵌入及其迭代
--
-- Defines the inner-preserving strict embedding, proves EmbeddingData
-- propagates along it, registers it as inner-rule, and iterates it on
-- the FinCat 2 tower
-- 定义保内层严格嵌入，证明 EmbeddingData 沿其传播，将其注册为
-- inner-rule，并在 FinCat 2 塔上迭代
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCatInnerSewing where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁; proj₂; _,_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.CumulativeHierarchy
  using (EmbeddingData; mkEmbeddingData; ShapeCat-id-comm)
open import ALMA.Cosmos.StrictLift
  using (StrictLayer; strictStep-suc; EmbeddingRule; strictEmbed-bridge; strictEmbed-compat)
open import ALMA.Cosmos.CumulativeHierarchyInstances using (module FinCatHierarchy)
open FinCatHierarchy using (FinCat; FinFC)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (LayerIdx; idxAt)

-- Local helpers for the inner-direction compatibility proofs
-- 内层方向相容性证明的局部辅助
private
  module InnerStrict
    {o h e s p : Level} {L : StrictLayer o h e s p}
    {x : Cosmos (StrictLayer.C L) (StrictLayer.FC L)}
    (ed : EmbeddingData x) where

    open EmbeddingData ed
    open ≡-Reasoning

    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    FC'  = StrictLayer.FC (strictStep-suc L)
    UXv  = out x
    module UX   = Unfolding UXv
    module SCat = Category (ShapeCat C_L FC_L)

    -- pos-to-shape compatibility at the lifted layer
    -- 提升层的 pos-to-shape 相容性
    pos-compat
      : ∀ {A B : SCat.Obj}
          {s : ShapeOf FC' A} {t : ShapeOf FC' B}
          (g : A SCat.⇒ B) (p : actSOf FC' {A = A} {B = B} g s ≡ t)
          (p₁ : PosOf FC' {A = B} (actSOf FC' {A = A} {B = B} g s))
        → actSOf FC_L (EmbeddingData.retract ed (lower t))
            (UX.pos-to-shape (lower t)
               (lower (subst (PosOf FC' {A = B}) p p₁)))
          ≡ actSOf FC_L (proj₁ g)
              (actSOf FC_L (EmbeddingData.retract ed (lower s))
                 (UX.pos-to-shape (lower s)
                    (actPOf FC_L (proj₁ g) (lower s) (lower p₁))))
    pos-compat {A} {B} {s} {t} g p p₁ = begin
        actSOf FC_L (EmbeddingData.retract ed (lower t))
          (UX.pos-to-shape (lower t)
             (lower (subst (PosOf FC' {A = B}) p p₁)))
          ≡⟨ cong (actSOf FC_L (EmbeddingData.retract ed (lower t)))
                  (cong (UX.pos-to-shape (lower t))
                        (strictEmbed-bridge L x ed g p p₁)) ⟩
        actSOf FC_L (EmbeddingData.retract ed (lower t))
          (UX.pos-to-shape (lower t)
             (subst (PosOf FC_L) (cong lower p) (lower p₁)))
          ≡⟨ strictEmbed-compat L x ed (proj₁ g) (cong lower p) (lower p₁) ⟩
        actSOf FC_L (proj₁ g)
          (actSOf FC_L (EmbeddingData.retract ed (lower s))
             (UX.pos-to-shape (lower s)
                (actPOf FC_L (proj₁ g) (lower s) (lower p₁))))
      ∎

-- The inner-preserving unfold functor: F₀ = π' (first-component projection)
-- 保内层展开函子：F₀ = π'（第一分量投影）
strictEmbed-unfoldFunctor-inner
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → Functor (ShapeCat (StrictLayer.C (strictStep-suc L))
                      (StrictLayer.FC (strictStep-suc L)))
            (ShapeCat (StrictLayer.C L) (StrictLayer.FC L))
strictEmbed-unfoldFunctor-inner L = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl (StrictLayer.C L)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                     Category.Equiv.refl (StrictLayer.C L)
  ; F-resp-≈     = λ ff≈gg → ff≈gg
  }

-- Inner-preserving strict embedding
-- 保内层严格嵌入
strictEmbed-inner
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (strictStep-suc L))
           (StrictLayer.FC (strictStep-suc L))
strictEmbed-inner L x ed .out = record
  { unfoldFunctor   = strictEmbed-unfoldFunctor-inner L
  ; unfold-next     = λ { {A} u →
      strictEmbed-inner L
        (UX.unfold-next {A = proj₁ A} (lower u))
        (EmbeddingData.next ed {A = proj₁ A} (lower u)) }
  ; pos-to-shape    = λ {A} s p →
      lift (actSOf FC_L (EmbeddingData.retract ed (lower s))
                   (UX.pos-to-shape (lower s) (lower p)))
  ; pos-actS-compat = λ {A} {B} {s} {t} f p p₁ →
      cong lift (InnerStrict.pos-compat {L = L} {x = x} ed f p p₁)
  }
  where
    FC_L = StrictLayer.FC L
    UXv  = out x
    module UX = Unfolding UXv

-- EmbeddingData propagates along the inner strict embedding
-- EmbeddingData 沿内层严格嵌入传播
module _ {o h e s p : Level} (L : StrictLayer o h e s p) where
  private
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    module C' = Category (ShapeCat C_L FC_L)

  -- Since F₀ (A, s) = A definitionally, retract = C'.id is well-typed,
  -- and retract-natural reduces to the unit laws of C'
  -- 因 F₀ (A, s) = A 定义性成立，retract = C'.id 类型正确，
  -- retract-natural 归约为 C' 的单位律
  strictEmbed-inner-self-embedding
    : (x : Cosmos C_L FC_L)
    → (ed : EmbeddingData x)
    → EmbeddingData (strictEmbed-inner L x ed)
  strictEmbed-inner-self-embedding x ed .EmbeddingData.retract =
    λ _ → C'.id
  strictEmbed-inner-self-embedding x ed
    .EmbeddingData.retract-natural {A} {B} {s} {t} f eq =
    ShapeCat-id-comm {C = C_L} {FC = FC_L} A B f
  strictEmbed-inner-self-embedding x ed
    .EmbeddingData.next {A} s =
    strictEmbed-inner-self-embedding
      (Unfolding.unfold-next (out x) {A = proj₁ A} (lower s))
      (EmbeddingData.next ed {A = proj₁ A} (lower s))

-- The inner-preserving rule
-- 保内层规则
inner-rule : EmbeddingRule
inner-rule .EmbeddingRule.Embed = strictEmbed-inner

-- Iterated inner embedding on the FinCat 2 tower
-- FinCat 2 塔上的迭代内层嵌入
module FinCatInnerSewing where

  -- Layer index and layers
  -- 层索引与层
  finIdx : LayerIdx
  finIdx = record { o = lzero ; h = lzero ; e = lzero ; s = lzero ; p = lzero }

  finLayer₀ : StrictLayer lzero lzero lzero lzero lzero
  finLayer₀ = record { C = FinCat 2 ; FC = FinFC 2 }

  finLayer : (n : ℕ)
           → StrictLayer (LayerIdx.o (idxAt finIdx n))
                         (LayerIdx.h (idxAt finIdx n))
                         (LayerIdx.e (idxAt finIdx n))
                         (LayerIdx.s (idxAt finIdx n))
                         (LayerIdx.p (idxAt finIdx n))
  finLayer zero    = finLayer₀
  finLayer (suc n) = strictStep-suc (finLayer n)

  -- Iteration of strictEmbed-inner: each step returns the resulting
  -- cosmos together with its EmbeddingData, which propagates
  -- unconditionally along the inner direction
  -- strictEmbed-inner 的迭代：每步返回所得宇宙及其 EmbeddingData，
  -- 后者沿内层方向无条件传播
  iterEmbed-inner
    : (n : ℕ)
    → (x : Cosmos (StrictLayer.C finLayer₀) (StrictLayer.FC finLayer₀))
    → (ed : EmbeddingData x)
    → Σ (Cosmos (StrictLayer.C (finLayer n)) (StrictLayer.FC (finLayer n)))
        (λ y → EmbeddingData y)
  iterEmbed-inner zero    x ed = x , ed
  iterEmbed-inner (suc n) x ed =
    let y , ed-y = iterEmbed-inner n x ed
    in strictEmbed-inner (finLayer n) y ed-y
       , strictEmbed-inner-self-embedding (finLayer n) y ed-y

  -- Definitional unfolding at suc
  -- 在 suc 处的定义性展开
  iterEmbed-inner-suc
    : (n : ℕ)
      (x : Cosmos (StrictLayer.C finLayer₀) (StrictLayer.FC finLayer₀))
      (ed : EmbeddingData x)
    → iterEmbed-inner (suc n) x ed
      ≡ ( strictEmbed-inner (finLayer n)
            (proj₁ (iterEmbed-inner n x ed))
            (proj₂ (iterEmbed-inner n x ed))
        , strictEmbed-inner-self-embedding (finLayer n)
            (proj₁ (iterEmbed-inner n x ed))
            (proj₂ (iterEmbed-inner n x ed)) )
  iterEmbed-inner-suc n x ed = refl

  -- Projections of the iteration
  -- 迭代的两个投影
  iterEmbed-inner-cosmos
    : (n : ℕ)
    → (x : Cosmos (StrictLayer.C finLayer₀) (StrictLayer.FC finLayer₀))
    → (ed : EmbeddingData x)
    → Cosmos (StrictLayer.C (finLayer n)) (StrictLayer.FC (finLayer n))
  iterEmbed-inner-cosmos n x ed = proj₁ (iterEmbed-inner n x ed)

  iterEmbed-inner-data
    : (n : ℕ)
    → (x : Cosmos (StrictLayer.C finLayer₀) (StrictLayer.FC finLayer₀))
    → (ed : EmbeddingData x)
    → EmbeddingData (iterEmbed-inner-cosmos n x ed)
  iterEmbed-inner-data n x ed = proj₂ (iterEmbed-inner n x ed)

  -- Layer-0 EmbeddingData, available since FinCat 2 has _⇒_ = ⊤
  -- 第 0 层的 EmbeddingData，因 FinCat 2 的 _⇒_ = ⊤ 而可用
  fin-EmbeddingData₀
    : (x : Cosmos (FinCat 2) (FinFC 2))
    → EmbeddingData x
  fin-EmbeddingData₀ = mkEmbeddingData (λ _ _ → tt) (λ _ _ → refl)
