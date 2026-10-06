------------------------------------------------------------------------
-- Sewing obstruction and direction dichotomy on the carried M base.
--
-- Legacy results (Cosmos/CumulativeHierarchySewing):
--   * FinCatSewing: at layer 1 of the FinCat 2 tower a cosmos whose
--     unfolding changes the shape component (F₀ ((A,s₀),s₁) = (A,s₁),
--     s₁ ≢ s₀) admits no EmbeddingData: the elements-category retract
--     would have to carry actS f s₁ ≡ s₀, i.e. s₁ ≡ s₀, contradicted by
--     the disjoint Fin constructors.
--   * DirectionDichotomy: under rigidity, the outer rule propagates an
--     embedding for EVERY unfolding iff every shape type is a singleton;
--     the unit tower stitches only because its shapes are ⊤.
--
-- M-base reconstruction.  The strict layer tower is absorbed by the M
-- index: iterating ShapeCat C FC (objects Σ A (Shape A)) is exactly
-- iterating MO.I = Σ (Obj C) (ShapeOf FC).  There is no per-step
-- universe lifting and no PosOf subst.  A carried "retract" of a
-- raised node back to its source shape is just an M edge
--
--   E (A,s) d (A,s) = Σ (PosOf FC s) λ p →
--                     (A,s) ≡ (F₀ (uf d) (A,s) , pts d s p),
--
-- whose target is pinned by a homogeneous refl.  For an
-- object-preserving label (uf.F₀ = proj₁) with singleton positions and
-- shape routing r, pts d s tt = r s, so a return edge exists iff
-- r s ≡ s: the whole sewing obstruction collapses to the fixed-point
-- condition of the routing function, with no equation to transport.
--
-- The dichotomy is then a category-free lemma:
--
--   (∀ r s → r s ≡ s)  ⇔  (∀ x y → x ≡ y),
--
-- i.e. every self-map fixes every point iff the type is a singleton.
-- Fin n (n ≥ 2) is not a singleton (fzero ≠ fsuc fzero), witnessed by
-- the constant routing rChg = const (fsuc fzero) which moves fzero;
-- hence its label has no return edge.  Over a singleton shape every
-- routing fixes the unique point and every return edge exists -- the
-- vacuous unit-tower case.  All mismatches are absorbed by the empty
-- pattern (constructive no-confusion): no subst, cast, Maybe, K or UIP.
--
-- 携带式 M 底座上的缝纫障碍与方向二分。
--
-- 旧结果（Cosmos/CumulativeHierarchySewing）：
--   * FinCatSewing：在 FinCat 2 塔第 1 层，展开改变形状分量的宇宙
--     （F₀ ((A,s₀),s₁) = (A,s₁)，s₁ ≢ s₀）没有 EmbeddingData：元素范畴
--     的 retract 必须携带 actS f s₁ ≡ s₀，即 s₁ ≡ s₀，被 Fin 构造子不
--     相交矛盾否决。
--   * DirectionDichotomy：刚性下，outer 规则对每个宇宙都传播嵌入当且
--     仅当每个形状类型单点；单位塔能缝合只因形状为 ⊤。
--
-- M 底座重建。严格层塔被 M 索引吸收：迭代 ShapeCat C FC（对象
-- Σ A (Shape A)）正是迭代 MO.I = Σ (Obj C) (ShapeOf FC)。无需逐层抬
-- universe，也无 PosOf subst。被提升节点回到源形状的携带式"retract"
-- 就是一条 M 边
--
--   E (A,s) d (A,s) = Σ (PosOf FC s) λ p →
--                     (A,s) ≡ (F₀ (uf d) (A,s) , pts d s p)，
--
-- 其目标由同质 refl 钉死。对对象保持（uf.F₀ = proj₁）、位置单点、形
-- 状路由为 r 的标签，pts d s tt = r s，故回边存在当且仅当 r s ≡ s：
-- 整个缝纫障碍塌缩为路由函数的不动点条件，没有任何待传输的等式。
--
-- 二分于是一条与范畴无关的引理：
--
--   （∀ r s → r s ≡ s） ⇔ （∀ x y → x ≡ y），
--
-- 即每个自映射都固定每个点当且仅当该类型单点。Fin n（n ≥ 2）非单点
-- （fzero ≠ fsuc fzero），常值路由 rChg = const (fsuc fzero) 移动
-- fzero 即为见证，故其标签无回边。单点形状下每个路由都固定唯一元素、
-- 每条回边都存在——即空洞的单位塔情形。所有失配由空模式吸收（构造性
-- 无混淆）：无 subst、cast、Maybe、K 或 UIP。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.SewingObstruction where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Function.Base using (id; const)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; _≢_)
open import Relation.Nullary.Negation using (¬_)

open import Data.Container.Core using (Container)
open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)
open Functor using (F₀)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

import ALMA.Cosmos.M.Object as MO

------------------------------------------------------------------------
-- Category-free core of the direction dichotomy: every self-map r on P
-- fixes every point  iff  P is a singleton (any two elements equal).
--
-- 方向二分的无范畴核心：P 上每个自映射 r 固定每个点 当且仅当 P 单点
-- （任意两元素相等）。
--
--   to   : if every self-map fixes every point, fix the constant map
--          const y at x to get y ≡ x, hence x ≡ y.
--   from : if P is singleton, r s is the unique element, hence r s ≡ s.
--
--   to   ：若每个自映射固定每个点，把常值映射 const y 在 x 处固定得
--          y ≡ x，故 x ≡ y。
--   from ：若 P 单点，r s 即唯一元素，故 r s ≡ s。
------------------------------------------------------------------------
routing-fixed-iff-singleton
  : ∀ {ℓ : Level} {P : Set ℓ}
  → (∀ (r : P → P) (s : P) → r s ≡ s)
    ⇔ (∀ (x y : P) → x ≡ y)
routing-fixed-iff-singleton {P = P} = mk⇔ to from
  where
    to : (∀ (r : P → P) (s : P) → r s ≡ s)
       → ∀ (x y : P) → x ≡ y
    to h x y = sym (h (const y) x)

    from : (∀ (x y : P) → x ≡ y)
         → ∀ (r : P → P) (s : P) → r s ≡ s
    from u r s = u (r s) s

------------------------------------------------------------------------
-- FinCat n stage, parameterised by m with n = suc (suc m), so n ≥ 2
-- holds definitionally and the distinct element fsuc fzero exists.
--
-- FinCat n 塔层，以 m 为参数，n = suc (suc m)，故 n ≥ 2 定义性成立、
-- 相异元素 fsuc fzero 存在。
------------------------------------------------------------------------
module SewingObstruction (m : ℕ) where

  n : ℕ
  n = suc (suc m)

  -- FinCat n = Indiscrete (Fin n): every hom is the unique (lift tt).
  -- FinCat n = Indiscrete (Fin n)：每个 hom 为唯一的 (lift tt)。
  Cn : Category lzero lzero lzero
  Cn = Indiscrete (Fin n)

  -- Non-singleton-shape container: shapes are Fin n, positions are the
  -- singleton ⊤.  The container functor acts as the identity on shapes
  -- (rigid), so an elements-category hom over it carries s ≡ s', i.e.
  -- only equal shapes are related -- the rigidity premise of the old
  -- dichotomy, here built into the M index rather than assumed.
  --
  -- 非单点形状容器：形状为 Fin n，位置为单点 ⊤。容器函子在形状上恒等
  -- 作用（刚性），故其上元素范畴的 hom 携带 s ≡ s'，即只联系相等形状
  -- ——旧二分的刚性前提，在此内建于 M 索引而非另行假设。
  FinContainer : Container lzero lzero
  FinContainer = record { Shape = Fin n ; Position = λ _ → ⊤ }

  FinFC : Functor Cn (ContCat lzero lzero)
  FinFC = record
    { F₀           = λ _ → FinContainer
    ; F₁           = λ _ → record { shape = id ; position = λ _ → tt }
    ; identity     = ≈sr-refl
    ; homomorphism = ≈sr-refl
    ; F-resp-≈     = λ _ → ≈sr-refl
    }

  -- Object-preserving unfolding: F₀ (A , s) = A.  This is the ufId of
  -- the tower separation witness; the object is kept, only the shape
  -- routing pts may move.
  --
  -- 对象保持的展开：F₀ (A , s) = A。即塔分离见证的 ufId；对象保持，
  -- 只有形状路由 pts 可能移动。
  ufId : Functor (ShapeCat Cn FinFC) Cn
  ufId = record
    { F₀           = proj₁
    ; F₁           = proj₁
    ; identity     = ≡refl
    ; homomorphism = ≡refl
    ; F-resp-≈     = λ p → p
    }

  -- An object-preserving label whose shape routing is r : Fin n → Fin n.
  -- Positions are singleton, so pts d s tt = r s.
  --
  -- 形状路由为 r : Fin n → Fin n 的对象保持标签。位置单点，故
  -- pts d s tt = r s。
  label : (r : Fin n → Fin n) → MO.CosmosData Cn FinFC
  label r = record { uf = ufId ; pts = λ s _ → r s }

  ----------------------------------------------------------------------
  -- The M edge pins the target index by a homogeneous refl.  For the
  -- label r, an edge from (A,s) back to (A,s) exists iff r s ≡ s:
  --
  --   E (A,s) (label r) (A,s)
  --     = Σ ⊤ λ _ → (A,s) ≡ (F₀ ufId (A,s) , r s)
  --     = Σ ⊤ λ _ → (A,s) ≡ (A , r s).
  --
  -- M 边以同质 refl 钉住目标索引。对标签 r，从 (A,s) 回到 (A,s) 的边
  -- 存在当且仅当 r s ≡ s。
  ----------------------------------------------------------------------
  return-edge
    : ∀ (r : Fin n → Fin n) (A s : Fin n)
    → r s ≡ s
    → MO.E Cn FinFC (A , s) (label r) (A , s)
  return-edge r A s eq =
    tt , Σ-≡,≡→≡ (≡refl , sym eq)

  no-return-edge
    : ∀ (r : Fin n → Fin n) (A s : Fin n)
    → r s ≢ s
    → ¬ MO.E Cn FinFC (A , s) (label r) (A , s)
  no-return-edge r A s ne (tt , q) =
    ne (sym (cong proj₂ q))

  ----------------------------------------------------------------------
  -- The concrete obstruction: 1 ≠ 0 in Fin n (n ≥ 2).  The constant
  -- routing rChg sends every shape to fsuc fzero, so it moves fzero.
  --
  -- 具体障碍：Fin n（n ≥ 2）中 1 ≠ 0。常值路由 rChg 把每个形状送到
  -- fsuc fzero，故它移动 fzero。
  ----------------------------------------------------------------------
  zero one : Fin n
  zero = fzero
  one  = fsuc fzero

  one≢zero : one ≢ zero
  one≢zero ()

  rChg : Fin n → Fin n
  rChg _ = one

  rChg-moves-fzero : rChg fzero ≢ fzero
  rChg-moves-fzero = one≢zero

  -- FinCatSewing.embedding-blocked, M form: the routing-changed label
  -- has no return edge at (A , fzero) for any object A.  This is the
  -- layer-1 stitching obstruction, with the elements-category retract
  -- replaced by the M edge and the mismatch absorbed by no-confusion.
  --
  -- FinCatSewing.embedding-blocked 的 M 形态：路由改变的标签在
  -- (A , fzero) 处对任意对象 A 都无回边。这是第 1 层缝纫障碍，元素范
  -- 畴 retract 被 M 边取代，失配由无混淆吸收。
  no-retract-routing-change
    : ∀ (A : Fin n)
    → ¬ MO.E Cn FinFC (A , fzero) (label rChg) (A , fzero)
  no-retract-routing-change A =
    no-return-edge rChg A fzero rChg-moves-fzero

  -- The universal outer-rule propagation fails at n ≥ 2: it is not the
  -- case that every routing label admits a return edge at every shape.
  --
  -- 全称 outer 规则传播在 n ≥ 2 失败：并非每个路由标签都在每个形状处
  -- 有回边。
  no-universal-return
    : ¬ (∀ (r : Fin n → Fin n) (A s : Fin n)
        → MO.E Cn FinFC (A , s) (label r) (A , s))
  no-universal-return h =
    no-retract-routing-change fzero (h rChg fzero fzero)

  ----------------------------------------------------------------------
  -- DirectionDichotomy, M form (necessity at n ≥ 2).  Fin n is not a
  -- singleton (fzero ≠ fsuc fzero); by the category-free dichotomy the
  -- fixed-point property fails, and the M-edge equivalence turns that
  -- failure into the absence of a universal retract.
  --
  -- 方向二分的 M 形态（n ≥ 2 的必要性）。Fin n 非单点
  -- （fzero ≠ fsuc fzero）；由无范畴二分，不动点性质失败，而 M 边等
  -- 价把该失败转为全称 retract 的缺失。
  ----------------------------------------------------------------------
  Fin-not-singleton : ¬ (∀ (x y : Fin n) → x ≡ y)
  Fin-not-singleton u = one≢zero (u one zero)

  Fin-not-all-fixed : ¬ (∀ (r : Fin n → Fin n) (s : Fin n) → r s ≡ s)
  Fin-not-all-fixed h =
    Fin-not-singleton λ a b → sym (h (const b) a)

  -- The obstruction and the fixed-point failure are the same fact read
  -- through the M edge: a return edge is exactly a fixed point.
  --
  -- 障碍与不动点失败是同一事实经 M 边读出：回边恰是一个不动点。
  fixed-point-iff-return-edge
    : ∀ (r : Fin n → Fin n) (A s : Fin n)
    → (r s ≡ s)
      ⇔ (MO.E Cn FinFC (A , s) (label r) (A , s))
  fixed-point-iff-return-edge r A s =
    mk⇔ (return-edge r A s)
         λ { (tt , q) → sym (cong proj₂ q) }
