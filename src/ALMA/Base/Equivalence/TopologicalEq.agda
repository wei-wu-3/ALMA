------------------------------------------------------------------------
-- degeneration: DiscreteEq under a topology
-- TopologicalEq is DiscreteEq at the same-opens layer induced by a
-- topology. It sits on the "drop next-eq" branch of the DepLayeredEq
-- degeneration lattice, alongside the other DiscreteEq instances
-- The same-opens relation is the symmetrisation of the specialisation
-- order _≤ₛ_; two points are topologically indistinguishable when
-- every open treats them equally
-- This module records the topology, the induced relation, its
-- specialisation order, the T0 characterisation as antisymmetry of
-- the order, preservation under continuous maps, and functoriality
-- of continuity
--
-- 退化：拓扑下的 DiscreteEq
-- TopologicalEq 是拓扑所诱导的相同开集 layer 处的 DiscreteEq
-- 它位于 DepLayeredEq 退化格的「去掉 next-eq」分支上，与其他
-- DiscreteEq 实例并列。相同开集关系是特化序 _≤ₛ_ 的对称化；
-- 两点拓扑不可区分，当且仅当每个开集同等对待它们
-- 本模块记录拓扑、所诱导的关系、其特化序、T0 作为序反对称性的
-- 刻画、连续映射下的保持性，以及连续性的函子性
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.TopologicalEq where

open import Agda.Primitive using (lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; subst)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)
open import Data.Product.Base using (_×_; proj₁; proj₂)

open import ALMA.Base.Equivalence.DiscreteEq using (DiscreteEq; module Symmetrisation)

------------------------------------------------------------------------
-- A minimal topology: a family of opens together with a membership
-- relation. The full topological axioms (closure under finite
-- intersections and arbitrary unions) are not needed for the
-- relations and preservation theorems below
--
-- 最小拓扑：开集族与成员关系。下面的关系与保持性定理不需要
-- 完整的拓扑公理（有限交与任意并的封闭性）
record TopologyStructure {a} (X : Set a) : Set (lsuc a) where
  field
    Open : Set a
    _∈_  : X → Open → Set a

open TopologyStructure public

------------------------------------------------------------------------
-- Specialisation order
-- The order is defined before TopologicalEq so that same-opens can be
-- obtained as the symmetrisation Sym _≤ₛ_, reusing the generic
-- Symmetrisation module rather than redefining it
--
-- 特化序
-- 该序在 TopologicalEq 之前定义，使 same-opens 可以作为
-- 对称化 Sym _≤ₛ_ 得到，复用通用 Symmetrisation 模块而非重新定义
module _ {a} {X : Set a} (𝕋 : TopologyStructure X) where
  private
    module 𝕋 = TopologyStructure 𝕋

  _≤ₛ_ : X → X → Set a
  x ≤ₛ y = ∀ U → 𝕋._∈_ x U → 𝕋._∈_ y U

  ≤ₛ-refl : ∀ x → x ≤ₛ x
  ≤ₛ-refl x U x∈U = x∈U

  ≤ₛ-trans : ∀ {x y z} → x ≤ₛ y → y ≤ₛ z → x ≤ₛ z
  ≤ₛ-trans p q U x∈U = q U (p U x∈U)

  ≤ₛ-isPreorder : IsPreorder _≡_ _≤ₛ_
  ≤ₛ-isPreorder = record
    { isEquivalence = record
      { refl  = λ {x} → refl
      ; sym   = λ {x} {y} → sym
      ; trans = λ {x} {y} {z} → trans
      }
    ; reflexive = λ {x} {y} x≡y U x∈U → subst (λ z → 𝕋._∈_ z U) x≡y x∈U
    ; trans     = ≤ₛ-trans
    }

------------------------------------------------------------------------
-- TopologicalEq is DiscreteEq at the symmetrisation of _≤ₛ_.
-- same-opens is Sym _≤ₛ_ by definition, so it is obtained by reuse
-- rather than by a fresh definition; the equivalence relation is
-- obtained from the generic sym-isEquivalence applied to
-- ≤ₛ-isPreorder
--
-- TopologicalEq 是 _≤ₛ_ 对称化处的 DiscreteEq
-- same-opens 定义上即 Sym _≤ₛ_，通过复用而非重新定义得到；
-- 等价关系由通用 sym-isEquivalence 应用于 ≤ₛ-isPreorder 得到
module TopologicalEq
    {a} {X : Set a}
    (𝕋 : TopologyStructure X)
  where

  same-opens : X → X → Set a
  same-opens = Symmetrisation.Sym (_≤ₛ_ 𝕋)

  TopologicalEq : X → X → Set a
  TopologicalEq = DiscreteEq same-opens

  TopologicalEq-eq : ∀ {x y} → TopologicalEq x y → same-opens x y
  TopologicalEq-eq p = p

  TopologicalEq-intro : ∀ {x y} → same-opens x y → TopologicalEq x y
  TopologicalEq-intro p = p

  -- Equivalence relation, from sym-isEquivalence applied to the
  -- preorder structure of _≤ₛ_
  --
  -- 等价关系，由 sym-isEquivalence 应用于 _≤ₛ_ 的预序结构得到
  top-isEquivalence : IsEquivalence TopologicalEq
  top-isEquivalence =
    Symmetrisation.sym-isEquivalence (_≤ₛ_ 𝕋) (≤ₛ-isPreorder 𝕋)

open TopologicalEq public

------------------------------------------------------------------------
-- Mathematical content: T0 characterisation, maximality of same-opens
-- among symmetric subrelations, and preservation under continuous maps
--
-- 数学内容：T0 刻画、same-opens 在对称子关系中的最大性，
-- 以及连续映射下的保持性
module TopologicalEq-Math
    {a} {X : Set a} {Y : Set a}
    (𝕋X : TopologyStructure X)
    (𝕋Y : TopologyStructure Y)
  where

  module TX = TopologicalEq 𝕋X
  module TY = TopologicalEq 𝕋Y
  module SX = TopologyStructure 𝕋X
  module SY = TopologyStructure 𝕋Y

  -- Plain function names, avoiding the parsing issue caused by mixing
  -- symbol and letter characters in an infix alias
  --
  -- 普通函数名，避免中缀别名中符号与字母混合导致的解析问题
  private
    leqX : X → X → Set a
    leqX = _≤ₛ_ 𝕋X

    leqY : Y → Y → Set a
    leqY = _≤ₛ_ 𝕋Y

  ------------------------------------------------------------------------
  -- T0 characterisation: indistinguishability collapses to equality
  -- if and only if the specialisation order is antisymmetric
  --
  -- T0 刻画：不可区分性塌缩为相等，当且仅当特化序反对称
  T0 : Set a
  T0 = ∀ x y → TX.TopologicalEq x y → x ≡ y

  ≤ₛ-antisym : Set a
  ≤ₛ-antisym = ∀ {x y} → leqX x y → leqX y x → x ≡ y

  T0→≤ₛ-antisym : T0 → ≤ₛ-antisym
  T0→≤ₛ-antisym t0 p q = t0 _ _ (TX.TopologicalEq-intro (p , q))

  ≤ₛ-antisym→T0 : ≤ₛ-antisym → T0
  ≤ₛ-antisym→T0 antisym x y p =
    antisym (proj₁ (TX.TopologicalEq-eq p))
            (proj₂ (TX.TopologicalEq-eq p))

  T0-iff-antisym : (T0 → ≤ₛ-antisym) × (≤ₛ-antisym → T0)
  T0-iff-antisym = T0→≤ₛ-antisym , ≤ₛ-antisym→T0

  T0-collapses : T0 → ∀ {x y} → TX.TopologicalEq x y → x ≡ y
  T0-collapses t0 p = t0 _ _ p

  ------------------------------------------------------------------------
  -- same-opens is the largest symmetric subrelation of _≤ₛ_: any
  -- symmetric R with R ⊆ _≤ₛ_ is contained in same-opens
  --
  -- same-opens 是 _≤ₛ_ 的最大对称子关系：任何对称且 R ⊆ _≤ₛ_
  -- 的关系 R 都包含于 same-opens
  module SymX = Symmetrisation leqX

  sym-sub-⊆-same-opens
    : (R : X → X → Set a)
    → (∀ {x y} → R x y → R y x)
    → (∀ {x y} → R x y → leqX x y)
    → ∀ {x y} → R x y → TX.TopologicalEq x y
  sym-sub-⊆-same-opens R sym-R R-⊆-leq p =
    TX.TopologicalEq-intro (R-⊆-leq p , R-⊆-leq (sym-R p))

  ------------------------------------------------------------------------
  -- Continuity: for every open U in Y, there is an open V in X whose
  -- extension is exactly f⁻¹(U)
  --
  -- 连续性：对 Y 中每个开集 U，存在 X 中开集 V，其外延恰好是 f⁻¹(U)
  Continuous : (X → Y) → Set a
  Continuous f =
    ∀ (U : SY.Open)
    → Σ SX.Open (λ V →
        ∀ z → (SX._∈_ z V → SY._∈_ (f z) U)
            × (SY._∈_ (f z) U → SX._∈_ z V))

  -- Continuous maps preserve the specialisation order
  --
  -- 连续映射保持特化序
  continuous-preserves-≤ₛ
    : (f : X → Y) → Continuous f
    → ∀ {x y} → leqX x y → leqY (f x) (f y)
  continuous-preserves-≤ₛ f cont {x} {y} p U fx∈U =
    let V , prf = cont U
        x∈V    = proj₂ (prf x) fx∈U
        y∈V    = p V x∈V
    in  proj₁ (prf y) y∈V

  -- Continuous maps preserve indistinguishability
  --
  -- 连续映射保持不可区分性
  continuous-preserves-indist
    : (f : X → Y) → Continuous f
    → ∀ {x y} → TX.TopologicalEq x y → TY.TopologicalEq (f x) (f y)
  continuous-preserves-indist f cont {x} {y} p =
    TY.TopologicalEq-intro
      ( continuous-preserves-≤ₛ f cont {x} {y}
          (proj₁ (TX.TopologicalEq-eq p))
      , continuous-preserves-≤ₛ f cont {y} {x}
          (proj₂ (TX.TopologicalEq-eq p)) )

------------------------------------------------------------------------
-- Identity map
-- The identity map is continuous on any topology
--
-- 恒等映射
-- 恒等映射在任意拓扑上连续
module TopologicalEq-Identity
    {a} {X : Set a}
    (𝕋X : TopologyStructure X)
  where

  module MXX = TopologicalEq-Math 𝕋X 𝕋X

  continuous-id : MXX.Continuous (λ x → x)
  continuous-id U = U , (λ x → (λ p → p) , (λ p → p))

------------------------------------------------------------------------
-- Composition of continuous maps
-- The composite of two continuous maps is continuous
--
-- 连续映射的复合
-- 两个连续映射的复合连续
module TopologicalEq-Functorial
    {a} {X : Set a} {Y : Set a} {Z : Set a}
    (𝕋X : TopologyStructure X)
    (𝕋Y : TopologyStructure Y)
    (𝕋Z : TopologyStructure Z)
  where

  module MXY = TopologicalEq-Math 𝕋X 𝕋Y
  module MYZ = TopologicalEq-Math 𝕋Y 𝕋Z
  module MXZ = TopologicalEq-Math 𝕋X 𝕋Z

  continuous-∘
    : (f : X → Y) (g : Y → Z)
    → MXY.Continuous f → MYZ.Continuous g
    → MXZ.Continuous (λ x → g (f x))
  continuous-∘ f g cf cg U =
    let V , prf-V = cg U
        W , prf-W = cf V
    in  W ,
        ( λ x →
            ( λ x∈W → proj₁ (prf-V (f x)) (proj₁ (prf-W x) x∈W) )
          , ( λ gfx∈U → proj₂ (prf-W x) (proj₂ (prf-V (f x)) gfx∈U) ) )
