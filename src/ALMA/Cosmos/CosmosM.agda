------------------------------------------------------------------------
-- The Cosmos as a pure M (matryoshka): object-level sketch.
--
-- The old Cosmos is a terminal coalgebra
--     record Cosmos : out : Unfolding FC (Cosmos C FC)
-- routing self-reference through an external seed type X = Cosmos.
-- Here self-reference is native: the child of a node at index j is
-- again an M A E j, i.e. again a Cosmos at j.
--
-- What used to be the four fields of Unfolding now lands as follows:
--   unfoldFunctor   ->  CosmosData.uf  (in the label layer A)
--   pos-to-shape    ->  CosmosData.pts (in the label layer A)
--   unfold-next     ->  M.below        (native recursion)
--   pos-actS-compat ->  NOT here       (needed only at the morphism layer)
--
-- 宇宙作为纯 M（俄罗斯套娃）：对象层草图。
--
-- 旧的 Cosmos 是一个终余代数
--     record Cosmos : out : Unfolding FC (Cosmos C FC)
-- 自指经外部种子类型 X = Cosmos 绕行。此处自指是内建的：索引 j 处节点
-- 的子节点又是 M A E j，即 j 处的宇宙。
--
-- 旧 Unfolding 的四个字段落位如下：
--   unfoldFunctor   ->  CosmosData.uf  （标签层 A 中）
--   pos-to-shape    ->  CosmosData.pts （标签层 A 中）
--   unfold-next     ->  M.below        （原生递归）
--   pos-actS-compat ->  此处无          （仅态射层需要）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.CosmosM where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  ----------------------------------------------------------------------
  -- Index: a base object together with a shape over it.
  -- 索引：基对象连同一个其上的形状。
  ----------------------------------------------------------------------
  I : Set (o ⊔ s)
  I = Σ (Category.Obj C) (ShapeOf FC)

  ----------------------------------------------------------------------
  -- Per-layer unfolding data.
  -- This is the only place the old "four-field" structure survives, and
  -- it survives as two fields because two of the four have native
  -- counterparts in M.
  -- 每层展开数据。
  -- 这是旧四字段结构唯一存留之处，且只留两个字段，因为另两个在 M 中
  -- 有原生对应物。
  ----------------------------------------------------------------------
  record CosmosData : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    field
      uf  : Functor (ShapeCat C FC) C
      pts : ∀ {A} (s : ShapeOf FC A) → PosOf FC s
          → ShapeOf FC (Functor.F₀ uf (A , s))

  open CosmosData public

  A : I → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  A _ = CosmosData

  ----------------------------------------------------------------------
  -- Edge: from (A₀ , s), a position p, to the next index.
  -- The witness carries the homogeneous equation that pins the target
  -- index to uf/pts applied at p; no J is used to eliminate it.
  -- 边：从 (A₀ , s) 出发、经位置 p 到下一索引。
  -- 见证携带同质等式，把目标索引钉为 p 处 uf/pts 的作用结果；不用 J
  -- 消去。
  ----------------------------------------------------------------------
  E : (i : I) (d : A i) (j : I) → Set (o ⊔ s ⊔ p)
  E (A₀ , s) d (A₁ , s₁) =
    Σ (PosOf FC s) λ p →
      (A₁ , s₁) ≡ ( Functor.F₀ (uf d) (A₀ , s)
                  , pts d s p )

  ----------------------------------------------------------------------
  -- Self-reference is native: the type of nodes is already the fixpoint
  -- of the one-step unfolding. Below, the child at index j is again
  -- CosmosM j.
  -- 自指是内建的：节点类型已经是一步展开的不动点。下方索引 j 处的子
  -- 节点又是 CosmosM j。
  ----------------------------------------------------------------------
  CosmosM : I → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  CosmosM i = M A E i

  ----------------------------------------------------------------------
  -- Readout: next index determined by a node and a source position.
  -- 读出：由节点与源位置确定的下一索引。
  ----------------------------------------------------------------------
  next : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i)) → I
  next (A₀ , s) t p =
    ( Functor.F₀ (uf (M.here t)) (A₀ , s)
    , pts (M.here t) s p )

  ----------------------------------------------------------------------
  -- Step into the next layer. This is the analogue of the old
  -- unfold-next, but it is derived, not a field. The edge witness
  -- (p , refl) is the canonical one: by construction the target index
  -- is exactly uf/pts applied at p.
  -- 步入下一层。这是旧 unfold-next 的对应物，但它是派生的，不是字段。
  -- 边见证 (p , refl) 是典范的：按构造，目标索引恰为 p 处 uf/pts 的结
  -- 果。
  ----------------------------------------------------------------------
  step : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i))
       → CosmosM (next i t p)
  step (A₀ , s) t p =
    M.below t (next (A₀ , s) t p) (p , refl)

  ----------------------------------------------------------------------
  -- Rooted Cosmos: fix a base object and a shape.
  -- 有根宇宙：固定基对象与形状。
  ----------------------------------------------------------------------
  Rooted : (A₀ : Category.Obj C) → ShapeOf FC A₀
         → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  Rooted A₀ s₀ = CosmosM (A₀ , s₀)
