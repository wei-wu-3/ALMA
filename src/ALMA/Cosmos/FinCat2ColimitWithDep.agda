------------------------------------------------------------------------
-- Conditional framework for the FinCat 2 tower with dep-embed-tower
-- FinCat 2 塔上以 dep-embed-tower 为嵌入的条件性框架
--
-- Replaces the EmbeddingRule parameter of FinCat2Colimit.WithSurjectivity
-- by the concrete tower-level embedding dep-embed-tower, eliminating the
-- embed-eq side condition. Given a uniform embedding family unif and its
-- surjectivity witness surj, constructs UniversalLimitDep and
-- NontrivialLimitDep. Both hypotheses are discharged unconditionally
-- downstream (unif by FinCat2DefaultUnif, surj by FinCat2Surjectivity)
-- 将 FinCat2Colimit.WithSurjectivity 的 EmbeddingRule 参数替换为具体
-- 塔层嵌入 dep-embed-tower，消除 embed-eq 边条件。给定一致嵌入族 unif
-- 与其满射性见证 surj，构造 UniversalLimitDep 与 NontrivialLimitDep
-- 两个假设均在下游被无条件消解（unif 由 FinCat2DefaultUnif，
-- surj 由 FinCat2Surjectivity）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2ColimitWithDep where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)

open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import ALMA.Cosmos.CumulativeHierarchy using (EmbeddingData; UniformEmbeddingFamily)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (Tower; LimitLayer)
open import ALMA.Cosmos.FinCat2Witness
  using (twoTower; twoIdx; cosmos-id; cosmos-const0; cosmos-id≉cosmos-const0)
open import ALMA.Cosmos.FinCat2TowerLemmas using (shape-singleton-at)
open import ALMA.Cosmos.FinCat2Colimit
  using (pos-inhabited-tower; dep-embed; dep-liftAt; dep-liftAt-resp
        ; dep-liftAt-step; colimitLayer; pos-singleton-tower)
open import ALMA.Cosmos.DependentEmbedding
  using (DependentEmbeddingRule; dep-rule)
open DependentEmbeddingRule

-- Instantiate dep-rule.EmbedDep at tower layers. The three preconditions
-- (pos-inhabited-tower, pos-singleton-tower, shape-singleton-at) are all
-- intrinsic to the tower, so the instantiation is unconditional
-- 把 dep-rule.EmbedDep 实例化到塔层。三个前提
-- （pos-inhabited-tower、pos-singleton-tower、shape-singleton-at）
-- 均为塔的固有结构，故该实例化无条件成立
dep-embed-tower
  : ∀ n (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
           (StrictLayer.FC (Tower.layer twoTower (suc n)))
dep-embed-tower n =
  EmbedDep dep-rule
    (Tower.layer twoTower n)
    (λ {A} → pos-inhabited-tower n A)
    (λ {A} → pos-singleton-tower n A)
    (shape-singleton-at (suc n))

-- Correspondence to FinCat2Colimit.dep-embed. The three _≈C_ fields are
-- definitional: both sides share the same underlying data
-- 与 FinCat2Colimit.dep-embed 的对应。三个 _≈C_ 字段均为定义性相等：
-- 两侧共享相同的底层数据
dep-embed-tower-≈-dep-embed
  : ∀ n x ed → dep-embed-tower n x ed ≈C dep-embed n x ed
dep-embed-tower-≈-dep-embed n x ed ._≈C_.unfoldFunctor₀-eq {A} s = refl
dep-embed-tower-≈-dep-embed n x ed ._≈C_.pos-to-shape-eq s p = refl
dep-embed-tower-≈-dep-embed n x ed ._≈C_.unfold-next-eq {A = A} s =
  dep-embed-tower-≈-dep-embed n
    (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
    (EmbeddingData.next ed {A = proj₁ A} (proj₂ A))

-- Tower-level cocone. Compared to the generic Cocone of
-- ConditionalNontrivialLimit, the step condition uses dep-embed-tower
-- directly rather than going through an EmbeddingRule
-- 塔层余锥。与 ConditionalNontrivialLimit 中泛型的 Cocone 相比，
-- 步进条件直接使用 dep-embed-tower，不再经过 EmbeddingRule
record CoconeDep {oD hD eD sD pD : Level}
                 (unif : ∀ n → UniformEmbeddingFamily
                                 {C  = StrictLayer.C  (Tower.layer twoTower n)}
                                 {FC = StrictLayer.FC (Tower.layer twoTower n)})
                 (D : StrictLayer oD hD eD sD pD) : Setω where
  field
    map : ∀ n → Cosmos (StrictLayer.C (Tower.layer twoTower n))
                       (StrictLayer.FC (Tower.layer twoTower n))
              → Cosmos (StrictLayer.C D) (StrictLayer.FC D)
    map-resp : ∀ n {x y}
      → _≈C_ {C  = StrictLayer.C  (Tower.layer twoTower n)}
             {FC = StrictLayer.FC (Tower.layer twoTower n)} x y
      → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D} (map n x) (map n y)
    step-compat : ∀ n x
      → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
          (map (suc n)
            (dep-embed-tower n x (UniformEmbeddingFamily.getData (unif n) x)))
          (map n x)

open CoconeDep

-- Conditional framework: given a uniform embedding family unif and a
-- surjectivity witness surj for it, we obtain the tower-level universal
-- limit and a non-triviality witness. surj is discharged unconditionally
-- by FinCat2Surjectivity; unif by FinCat2DefaultUnif
-- 条件性框架：给定一致嵌入族 unif 与其满射性见证 surj，
-- 得到塔层通用极限与非平凡见证。surj 由 FinCat2Surjectivity
-- 无条件消解，unif 由 FinCat2DefaultUnif 消解
module WithDepSurjectivity
  (unif : ∀ n → UniformEmbeddingFamily
                  {C  = StrictLayer.C  (Tower.layer twoTower n)}
                  {FC = StrictLayer.FC (Tower.layer twoTower n)})
  (surj : ∀ n
          (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
                       (StrictLayer.FC (Tower.layer twoTower (suc n))))
        → Σ (Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
            (λ y → x ≈C dep-embed-tower n y
                     (UniformEmbeddingFamily.getData (unif n) y)))
  where

  -- liftAt-step for dep-embed-tower: first transfer dep-embed-tower to
  -- dep-embed via the correspondence lemma, then apply dep-liftAt-step
  -- dep-embed-tower 的 liftAt-step：先用对应引理把 dep-embed-tower
  -- 换成 dep-embed，再应用 dep-liftAt-step
  liftAt-step-tower
    : ∀ n
      (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                   (StrictLayer.FC (Tower.layer twoTower n)))
    → dep-liftAt (suc n)
        (dep-embed-tower n x
          (UniformEmbeddingFamily.getData (unif n) x))
      ≈C dep-liftAt n x
  liftAt-step-tower n x =
    ≈C-trans
      (dep-liftAt-resp (suc n)
        (dep-embed-tower-≈-dep-embed n x
          (UniformEmbeddingFamily.getData (unif n) x)))
      (dep-liftAt-step n x (UniformEmbeddingFamily.getData (unif n) x))

  -- mediate-coh for CoconeDep: same proof chain as FinCat2Colimit, with
  -- dep-embed-tower inlined and no embed-eq side condition
  -- CoconeDep 的 mediate-coh：与 FinCat2Colimit 证明链相同，
  -- 内联 dep-embed-tower，无 embed-eq 边条件
  dep-mediate-coh
    : ∀ {oD hD eD sD pD}
      {D : StrictLayer oD hD eD sD pD}
      (cone : CoconeDep unif D) (n : ℕ)
      (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                   (StrictLayer.FC (Tower.layer twoTower n)))
    → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
        (map cone 0 (dep-liftAt n x))
        (map cone n x)
  dep-mediate-coh cone zero    x = ≈C-refl
  dep-mediate-coh cone (suc n) x =
    let (y , p) = surj n x
        q1 = map-resp cone 0 (dep-liftAt-resp (suc n) p)
        q2 = map-resp cone 0 (liftAt-step-tower n y)
        q3 = dep-mediate-coh cone n y
        q4 = ≈C-trans (≈C-sym (step-compat cone n y))
                      (map-resp cone (suc n) (≈C-sym p))
    in ≈C-trans q1 (≈C-trans q2 (≈C-trans q3 q4))

-- Tower-level universal limit. The type is deliberately incompatible
-- with ConditionalNontrivialLimit.UniversalLimit: the latter is
-- parameterised by an EmbeddingRule R, this one is specialised to
-- dep-embed-tower. The two are related only through
-- dependentUniversalLimitDep below
-- 塔层通用极限。其类型与 ConditionalNontrivialLimit.UniversalLimit
-- 刻意不兼容：后者以 EmbeddingRule R 为参数，本记录特化到
-- dep-embed-tower。二者仅通过下方的 dependentUniversalLimitDep 关联
record UniversalLimitDep
  (unif : ∀ n → UniformEmbeddingFamily
                  {C  = StrictLayer.C  (Tower.layer twoTower n)}
                  {FC = StrictLayer.FC (Tower.layer twoTower n)})
  : Setω where
  field
    limit          : LimitLayer twoIdx twoTower
    liftAt         : ∀ n
                   → Cosmos (StrictLayer.C  (Tower.layer twoTower n))
                            (StrictLayer.FC (Tower.layer twoTower n))
                   → Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                            (StrictLayer.FC (LimitLayer.layer∞ limit))
    liftAt-resp    : ∀ n {x y}
                   → _≈C_ {C  = StrictLayer.C  (Tower.layer twoTower n)}
                          {FC = StrictLayer.FC (Tower.layer twoTower n)} x y
                   → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                          {FC = StrictLayer.FC (LimitLayer.layer∞ limit)}
                          (liftAt n x) (liftAt n y)
    liftAt-step    : ∀ n
                     (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                                 (StrictLayer.FC (Tower.layer twoTower n)))
                   → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                          {FC = StrictLayer.FC (LimitLayer.layer∞ limit)}
                          (liftAt (suc n)
                            (dep-embed-tower n x
                              (UniformEmbeddingFamily.getData (unif n) x)))
                          (liftAt n x)

    mediate        : ∀ {oD hD eD sD pD : Level}
                   → (D : StrictLayer oD hD eD sD pD)
                   → CoconeDep unif D
                   → Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                            (StrictLayer.FC (LimitLayer.layer∞ limit))
                   → Cosmos (StrictLayer.C D) (StrictLayer.FC D)

    mediate-resp   : ∀ {oD hD eD sD pD : Level}
                   → {D : StrictLayer oD hD eD sD pD}
                   → (cone : CoconeDep unif D)
                   → {x y : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                   (StrictLayer.FC (LimitLayer.layer∞ limit))}
                   → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                          {FC = StrictLayer.FC (LimitLayer.layer∞ limit)} x y
                   → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                           (mediate D cone x) (mediate D cone y)

    mediate-coh    : ∀ {oD hD eD sD pD : Level}
                   → {D : StrictLayer oD hD eD sD pD}
                   → (cone : CoconeDep unif D) (n : ℕ)
                   → (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                                 (StrictLayer.FC (Tower.layer twoTower n)))
                   → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                       (mediate D cone (liftAt n x))
                       (CoconeDep.map cone n x)

    mediate-unique : ∀ {oD hD eD sD pD : Level}
                   → {D : StrictLayer oD hD eD sD pD}
                   → (cone : CoconeDep unif D)
                   → (g : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                 (StrictLayer.FC (LimitLayer.layer∞ limit))
                        → Cosmos (StrictLayer.C D) (StrictLayer.FC D))
                   → (g-resp : ∀ {x y : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                               (StrictLayer.FC (LimitLayer.layer∞ limit))}
                             → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                                    {FC = StrictLayer.FC (LimitLayer.layer∞ limit)} x y
                             → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                                     (g x) (g y))
                   → (g-coh : ∀ (n : ℕ)
                                (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                                            (StrictLayer.FC (Tower.layer twoTower n)))
                            → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                                (g (liftAt n x))
                                (CoconeDep.map cone n x))
                   → ∀ (z : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                   (StrictLayer.FC (LimitLayer.layer∞ limit)))
                   → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                       (g z) (mediate D cone z)

open UniversalLimitDep

-- A uniform embedding family at every layer of the tower
-- 塔每一层上的一致嵌入族
UniformEmbeddingFamilyForTower : Setω
UniformEmbeddingFamilyForTower =
  ∀ n → UniformEmbeddingFamily
          {C  = StrictLayer.C  (Tower.layer twoTower n)}
          {FC = StrictLayer.FC (Tower.layer twoTower n)}

-- Every (suc n)-layer cosmos arises, up to _≈C_, as the dep-embed-tower
-- image of some n-layer cosmos
-- 第 (suc n) 层的任意宇宙在 _≈C_ 意义下都等于某第 n 层宇宙的
-- dep-embed-tower 像
SurjectivityForTower : UniformEmbeddingFamilyForTower → Setω
SurjectivityForTower unif =
  ∀ n
    (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
                 (StrictLayer.FC (Tower.layer twoTower (suc n))))
  → Σ (Cosmos (StrictLayer.C (Tower.layer twoTower n))
               (StrictLayer.FC (Tower.layer twoTower n)))
      (λ y → x ≈C dep-embed-tower n y
                   (UniformEmbeddingFamily.getData (unif n) y))

-- Assemble the tower-level universal limit from dep-liftAt and colimitLayer,
-- with mediate = map cone 0
-- 由 dep-liftAt 与 colimitLayer 组装塔层通用极限，mediate = map cone 0
dependentUniversalLimitDep
  : (unif : UniformEmbeddingFamilyForTower)
  → (surj : SurjectivityForTower unif)
  → UniversalLimitDep unif
dependentUniversalLimitDep unif surj = record
  { limit          = colimitLayer
  ; liftAt         = dep-liftAt
  ; liftAt-resp    = λ n {x} {y} → dep-liftAt-resp n
  ; liftAt-step    = λ n x →
      WithDepSurjectivity.liftAt-step-tower unif surj n x
  ; mediate        = λ D cone z → CoconeDep.map cone 0 z
  ; mediate-resp   = λ {D} cone {x} {y} eq → CoconeDep.map-resp cone 0 eq
  ; mediate-coh    = λ {D} cone n x →
      WithDepSurjectivity.dep-mediate-coh unif surj cone n x
  ; mediate-unique = λ {D} cone g g-resp g-coh z → g-coh 0 z
  }

-- Non-triviality: liftAt distinguishes a pair of cosmos elements
-- 非平凡性：liftAt 区分一对宇宙元素
record NontrivialLimitDep
  {unif : UniformEmbeddingFamilyForTower}
  (UL : UniversalLimitDep unif) : Setω where
  field
    n   : ℕ
    x   : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                 (StrictLayer.FC (Tower.layer twoTower n))
    y   : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                 (StrictLayer.FC (Tower.layer twoTower n))
    x≉y : ¬ (_≈C_
              {C  = StrictLayer.C  (LimitLayer.layer∞ (limit UL))}
              {FC = StrictLayer.FC (LimitLayer.layer∞ (limit UL))}
              (liftAt UL n x) (liftAt UL n y))

open NontrivialLimitDep

-- Non-triviality at layer 0: liftAt 0 is the identity, so the two
-- layer-0 cosmoi cosmos-id and cosmos-const0 remain distinguishable
-- after lifting, with the same witness as FinCat2Witness
-- 第 0 层的非平凡性：liftAt 0 为恒等，故两个第 0 层宇宙
-- cosmos-id 与 cosmos-const0 在提升后仍可区分，
-- 见证与 FinCat2Witness 相同
dependentNontrivialDep
  : (unif : UniformEmbeddingFamilyForTower)
  → (surj : SurjectivityForTower unif)
  → NontrivialLimitDep (dependentUniversalLimitDep unif surj)
dependentNontrivialDep unif surj = record
  { n    = 0
  ; x    = cosmos-id
  ; y    = cosmos-const0
  ; x≉y  = cosmos-id≉cosmos-const0
  }
