------------------------------------------------------------------------
-- Diagnostic result: the outer-preserving strict embedding (outer-rule)
-- is NOT pointwise equal to the dependent embedding dep-embed at every
-- layer of the FinCat 2 tower. The mismatch is witnessed by a single
-- shape of Fin 2, and lifted to all n by iterating dep-embed
-- This module has no downstream users; it records why the `embed-eq`
-- parameter of FinCat2Colimit.WithSurjectivity is not satisfiable for
-- R = outer-rule
-- 诊断性结果：保外层严格嵌入（outer-rule）在 FinCat 2 塔的每一层上
-- 都与依赖嵌入 dep-embed 不逐点相等。不匹配性由 Fin 2 的一个形状见证，
-- 并通过迭代 dep-embed 提升到所有 n
-- 本模块没有下游使用方；它的存在是为记录：为何
-- FinCat2Colimit.WithSurjectivity 的 `embed-eq` 参数在 R = outer-rule 下
-- 不可满足
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2EmbeddingMismatch where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategoryLemmas using (actSOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.CumulativeHierarchy using (EmbeddingData; mkEmbeddingData)
open import ALMA.Cosmos.StrictLift using
  (strictStep-suc; StrictLayer; EmbeddingRule; outer-rule; strictEmbed)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (Tower)
open import ALMA.Cosmos.FinCat2Witness
  using (TwoObjLayer; twoTower; zero≠suc-fzero; cosmos-const0)
open import ALMA.Cosmos.FinCat2TowerLemmas
  using (proj-obj; embed-obj; embed-shape; shape-singleton-at)
open import ALMA.Cosmos.FinCat2Colimit using (dep-embed; pos-inhabited-tower)

-- EmbeddingData for cosmos-const0
-- cosmos-const0 的 EmbeddingData
ed-const0 : EmbeddingData cosmos-const0
ed-const0 = mkEmbeddingData
  (λ _ _ → tt)
  (λ _ _ → refl)
  cosmos-const0

-- Witness shape at layer 1
-- 第 1 层的见证形状
z : Category.Obj
      (ShapeCat (StrictLayer.C (strictStep-suc TwoObjLayer))
                (StrictLayer.FC (strictStep-suc TwoObjLayer)))
z = ((fsuc fzero , lift tt) , lift (lift tt))

-- Layer-0 mismatch
-- Transport the mismatch along an assumed pointwise equality
-- 第 0 层不匹配
-- 把不匹配性沿假设的逐点相等性传输
apply-eq
  : EmbeddingRule.Embed outer-rule TwoObjLayer ≡ dep-embed 0
  → EmbeddingRule.Embed outer-rule TwoObjLayer cosmos-const0 ed-const0
    ≡ dep-embed 0 cosmos-const0 ed-const0
apply-eq eq = cong (λ f → f cosmos-const0 ed-const0) eq

-- The two unfoldFunctor.F₀ images at z coincide
-- 两个 unfoldFunctor.F₀ 在 z 处重合
eq-obj
  : (eq : EmbeddingRule.Embed outer-rule TwoObjLayer ≡ dep-embed 0)
  → Unfolding.unfoldFunctor
      (out (EmbeddingRule.Embed outer-rule TwoObjLayer cosmos-const0 ed-const0))
      .Functor.F₀ z
    ≡ Unfolding.unfoldFunctor
        (out (dep-embed 0 cosmos-const0 ed-const0))
        .Functor.F₀ z
eq-obj eq = cong (λ c → Unfolding.unfoldFunctor (out c) .Functor.F₀ z)
                 (apply-eq eq)

-- Their first components coincide
-- 二者第一分量重合
eq-first
  : (eq : EmbeddingRule.Embed outer-rule TwoObjLayer ≡ dep-embed 0)
  → proj₁ (Unfolding.unfoldFunctor
             (out (EmbeddingRule.Embed outer-rule TwoObjLayer cosmos-const0 ed-const0))
             .Functor.F₀ z)
    ≡ proj₁ (Unfolding.unfoldFunctor
               (out (dep-embed 0 cosmos-const0 ed-const0))
               .Functor.F₀ z)
eq-first eq = cong proj₁ (eq-obj eq)

-- Left first component evaluates to fsuc fzero
-- 左侧第一分量求值为 fsuc fzero
lhs-first
  : proj₁ (Unfolding.unfoldFunctor
             (out (EmbeddingRule.Embed outer-rule TwoObjLayer cosmos-const0 ed-const0))
             .Functor.F₀ z)
    ≡ fsuc fzero
lhs-first = refl

-- Right first component evaluates to fzero
-- 右侧第一分量求值为 fzero
rhs-first
  : proj₁ (Unfolding.unfoldFunctor
             (out (dep-embed 0 cosmos-const0 ed-const0))
             .Functor.F₀ z)
    ≡ fzero
rhs-first = refl

-- Layer-0 mismatch: outer-rule is not pointwise equal to dep-embed at layer 0
-- Chain: fzero ≡ (right first) ≡ (eq) ≡ (left first) ≡ fsuc fzero
-- 第 0 层不匹配：outer-rule 在层 0 上不与 dep-embed 逐点相等
-- 链：fzero ≡（右侧第一分量）≡（假设等式）≡（左侧第一分量）≡ fsuc fzero
embed-eq-false-zero
    : ¬ (EmbeddingRule.Embed outer-rule TwoObjLayer ≡ dep-embed 0)
embed-eq-false-zero eq =
  zero≠suc-fzero (begin
    fzero
      ≡˘⟨ rhs-first ⟩
    proj₁ (Unfolding.unfoldFunctor
             (out (dep-embed 0 cosmos-const0 ed-const0))
             .Functor.F₀ z)
      ≡˘⟨ eq-first eq ⟩
    proj₁ (Unfolding.unfoldFunctor
             (out (EmbeddingRule.Embed outer-rule TwoObjLayer
                                       cosmos-const0 ed-const0))
             .Functor.F₀ z)
      ≡⟨ lhs-first ⟩
    fsuc fzero
    ∎)

-- Iterated construction, lifting the mismatch to all n
-- EmbeddingData for dep-embed k y ed
-- 迭代构造：把不匹配性提升到所有 n
-- dep-embed k y ed 的 EmbeddingData
ed-for : ∀ k
  (y  : Cosmos (StrictLayer.C (Tower.layer twoTower k))
              (StrictLayer.FC (Tower.layer twoTower k)))
  (ed : EmbeddingData y)
  → EmbeddingData (dep-embed k y ed)
ed-for k y ed .EmbeddingData.retract {A} s =
  ( EmbeddingData.retract ed (proj₂ A)
  , shape-singleton-at k (proj₁ A)
      (actSOf (StrictLayer.FC (Tower.layer twoTower k))
        (EmbeddingData.retract ed (proj₂ A))
        (Unfolding.pos-to-shape (out y) (proj₂ A)
            (pos-inhabited-tower k (proj₁ A) (proj₂ A))))
      (proj₂ A) )
ed-for k y ed .EmbeddingData.retract-natural {A} {B} {s} {t} f eq =
  EmbeddingData.retract-natural ed (proj₁ f) (proj₂ f)
ed-for k y ed .EmbeddingData.next {A} s =
  ed-for k
    (Unfolding.unfold-next (out y) {A = proj₁ A} (proj₂ A))
    (EmbeddingData.next ed {A = proj₁ A} (proj₂ A))

-- Iterated const0 cosmos and its embedding data
-- 迭代的 const0 宇宙及其嵌入数据
mutual
  const0-n : ∀ k
    → Cosmos (StrictLayer.C (Tower.layer twoTower k))
            (StrictLayer.FC (Tower.layer twoTower k))
  const0-n zero    = cosmos-const0
  const0-n (suc k) = dep-embed k (const0-n k) (ed-base k)

  ed-base : ∀ k → EmbeddingData (const0-n k)
  ed-base zero    = ed-const0
  ed-base (suc k) = ed-for k (const0-n k) (ed-base k)

-- proj-obj is a left inverse of embed-obj
-- proj-obj 是 embed-obj 的左逆
proj-obj∘embed-obj : ∀ k (a : Fin 2) → proj-obj k (embed-obj k a) ≡ a
proj-obj∘embed-obj zero    a = refl
proj-obj∘embed-obj (suc k) a = proj-obj∘embed-obj k a

-- Left first component projects to fzero
-- 左侧第一分量投影为 fzero
fzero-lemma : ∀ k
  → proj-obj k
      (Unfolding.unfoldFunctor (out (const0-n k)) .Functor.F₀
        (embed-obj k (fsuc fzero), embed-shape k (embed-obj k (fsuc fzero))))
    ≡ fzero
fzero-lemma zero    = refl
fzero-lemma (suc k) = fzero-lemma k

-- Right first component projects to fsuc fzero
-- 右侧第一分量投影为 fsuc fzero
fsuc-lemma : ∀ k
  → proj-obj k (proj₁ (embed-obj (suc k) (fsuc fzero))) ≡ fsuc fzero
fsuc-lemma zero    = refl
fsuc-lemma (suc k) =
  proj-obj∘embed-obj (suc k) (fsuc fzero)

-- Mismatch at every layer: outer-rule ≠ dep-embed pointwise
-- Chain: fzero ≡ (right) ≡ (eq) ≡ (left) ≡ fsuc fzero
-- 每一层上的不匹配：outer-rule 与 dep-embed 不逐点相等
-- 链：fzero ≡（右侧）≡（假设等式）≡（左侧）≡ fsuc fzero
embed-eq-false
  : ∀ n
  → ¬ (EmbeddingRule.Embed outer-rule (Tower.layer twoTower n) ≡ dep-embed n)
embed-eq-false n eq =
  zero≠suc-fzero (begin
    fzero
      ≡˘⟨ right≡fzero ⟩
    right-F₀
      ≡˘⟨ eq-F₀ ⟩
    left-F₀
      ≡⟨ left≡fsuc ⟩
    fsuc fzero
    ∎)
  where
    x    = const0-n n
    ed-x = ed-base n
    z-n  = ( embed-obj (suc n) (fsuc fzero)
           , embed-shape (suc n) (embed-obj (suc n) (fsuc fzero)) )
    left  = strictEmbed (Tower.layer twoTower n) x ed-x
    right = dep-embed n x ed-x
    left-F₀  = proj-obj n
                (Unfolding.unfoldFunctor (out left)  .Functor.F₀ z-n .proj₁)
    right-F₀ = proj-obj n
                (Unfolding.unfoldFunctor (out right) .Functor.F₀ z-n .proj₁)
    left≡fsuc  : left-F₀ ≡ fsuc fzero
    left≡fsuc = fsuc-lemma n
    right≡fzero : right-F₀ ≡ fzero
    right≡fzero = fzero-lemma n
    eq1   = cong (λ f → f x ed-x) eq
    eq-F₀ : left-F₀ ≡ right-F₀
    eq-F₀ = cong (λ c → proj-obj n
                  (Unfolding.unfoldFunctor (out c) .Functor.F₀ z-n .proj₁)) eq1
