------------------------------------------------------------------------
-- Permuted embedding on the carried M base: refuting criterion C.
--
-- Legacy result (Cosmos/FinCatNPermutedEmbedding, 649 lines): for every
-- f : Fin n → Fin n with a left inverse, a tower-specific permuted
-- embedding applies f at each layer together with a liftAt applying
-- f⁻¹ to cancel the accumulated f.  When f has a non-fixed point, the
-- embedding does not preserve the input F₀ at layer 0 while liftAt 0 is
-- the identity (hence injective).  This refutes criterion C:
--
--   "feasibility of an embedding (an injective / reflecting lift)
--    implies preservation of the input F₀."
--
-- The witness is unconditional, given by the swap of two elements.
--
-- M-base reconstruction.  On M the strict layer tower is absorbed by
-- the indexed coinductive type, so there is no layer index k, no liftF
-- across universes and no liftAt to thread through the tower.  The
-- residual content is purely finitary.  To stay inside Cubical Agda
-- without relying on constructor injectivity (which Fin index matching
-- would trigger), the two-element fibre is a plain non-indexed enum
-- `data Two`, exactly as in the slice-14 permutation argument.  Over a
-- singleton-position container with shape fibre Two, the transposition
-- sw (w0 ↔ w1)
--
--   * is a perfectly feasible carried routing (label sw is a valid
--     CosmosData),
--   * is INVERTIBLE: sw is an involution, so it is its own two-sided
--     inverse and the carried fibre adjunction swapAdj (to = fro = sw,
--     η = ε = sw-invol) is a self-adjunction -- the M form of an
--     injective, identity-at-the-base lift,
--   * yet it does NOT preserve the input shape: sw w0 = w1 ≠ w0.
--
-- Hence a feasible, invertible (bijective) carried correspondence
-- need not preserve F₀/labels: criterion C is false on M as well.
-- The mismatch is absorbed by the empty pattern on the disjoint
-- constructors of the non-indexed enum (constructive no-confusion); no
-- subst, cast, Maybe, K or UIP, and the 649-line cross-level tower is
-- not needed.
--
-- 携带式 M 底座上的置换嵌入：反驳判据 C。
--
-- 旧结果（Cosmos/FinCatNPermutedEmbedding，649 行）：对每个带左逆的
-- f : Fin n → Fin n，构造在每层施加 f 的塔特定置换嵌入，并用施加 f⁻¹
-- 的 liftAt 抵消累积的 f。当 f 有非不动点时，嵌入在第 0 层不保持输入
-- F₀，而 liftAt 0 为恒等（故单射）。这反驳判据 C：
--
--   “嵌入的可行性（单射/反射的 lift）蕴含对输入 F₀ 的保持。”
--
-- 见证由两元素对换无条件给出。
--
-- M 底座重建。M 上严格层塔被索引余归纳类型吸收，故没有层指标 k、没有
-- 跨 universe 的 liftF，也没有贯穿塔的 liftAt。剩余内容纯粹有限。为在
-- Cubical Agda 内不依赖构造子内射（Fin 索引匹配会触发它），两元素纤
-- 维采用普通非索引枚举 data Two，与切片14 的置换论证一致。在位置单点、
-- 形状纤维为 Two 的容器上，对换 sw（w0 ↔ w1）
--
--   * 是完全可行的携带式路由（label sw 是合法 CosmosData）；
--   * 可逆：sw 对合，故它是自身的双侧逆，携带式纤维伴随 swapAdj
--     （to = fro = sw，η = ε = sw-invol）是自伴随——即“基底处恒等、
--     单射的 lift”的 M 形态；
--   * 却不保持输入形状：sw w0 = w1 ≠ w0。
--
-- 因此可行、可逆（双射）的携带式对应不必保持 F₀/标签：判据 C 在 M 上
-- 同样不成立。失配由非索引枚举不相交构造子的空模式（构造性无混淆）吸
-- 收；无 subst、cast、Maybe、K 或 UIP，也不需要 649 行跨层塔。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.PermutedEmbedding where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality.Core using (cong; _≢_)
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
open import ALMA.Base.MCorrSetoid using (FiberAdjˢ; propEqOn)

------------------------------------------------------------------------
-- The two-element shape fibre, as a plain non-indexed enumeration so
-- that matching its constructors needs no injectivity (Cubical-safe).
--
-- 两元素形状纤维，普通非索引枚举，故匹配其构造子无需内射（Cubical
-- 安全）。
------------------------------------------------------------------------
data Two : Set lzero where
  w0 w1 : Two

-- The two elements are distinct by constructive no-confusion.
--
-- 两元素由构造性无混淆而不同。
w1≢w0 : ¬ (w1 ≡ w0)
w1≢w0 ()

------------------------------------------------------------------------
-- Base category Indiscrete Two (every hom unique), a container with
-- Shape = Two and singleton positions, and the identity-on-shape rigid
-- container functor.
--
-- 基范畴 Indiscrete Two（每个 hom 唯一），容器 Shape = Two、位置单
-- 点，容器函子在形状上恒等作用（刚性）。
------------------------------------------------------------------------
C2 : Category lzero lzero lzero
C2 = Indiscrete Two

TwoContainer : Container lzero lzero
TwoContainer = record { Shape = Two ; Position = λ _ → ⊤ }

TwoFC : Functor C2 (ContCat lzero lzero)
TwoFC = record
  { F₀           = λ _ → TwoContainer
  ; F₁           = λ _ → record { shape = id ; position = λ _ → tt }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

-- Object-preserving unfolding: F₀ (A , s) = A.
-- 对象保持的展开：F₀ (A , s) = A。
ufId : Functor (ShapeCat C2 TwoFC) C2
ufId = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = ≡refl
  ; homomorphism = ≡refl
  ; F-resp-≈     = λ p → p
  }

-- Object-preserving label with shape routing r; positions singleton.
-- 形状路由为 r 的对象保持标签；位置单点。
label : (r : Two → Two) → MO.CosmosData C2 TwoFC
label r = record { uf = ufId ; pts = λ s _ → r s }

------------------------------------------------------------------------
-- The transposition sw on Two: swaps w0 and w1.
-- Two 上的对换 sw：交换 w0 与 w1。
------------------------------------------------------------------------
sw : Two → Two
sw w0 = w1
sw w1 = w0

-- sw is definitionally an involution (its own two-sided inverse).
--
-- sw 定义性对合（即自身的双侧逆）。
sw-invol : ∀ (s : Two) → sw (sw s) ≡ s
sw-invol w0 = ≡refl
sw-invol w1 = ≡refl

-- sw moves w0 to w1: it does not preserve the input shape at w0.
--
-- sw 把 w0 移到 w1：它在 w0 处不保持输入形状。
sw-moves-w0 : sw w0 ≢ w0
sw-moves-w0 = w1≢w0

------------------------------------------------------------------------
-- The carried fibre self-adjunction of sw: to = fro = sw, with the
-- involution as both round-trip laws.  This is the M form of the
-- feasible embedding together with its canceling, identity-at-the-base
-- (hence injective) lift: a self-adjunction is a carried bijection.
--
-- sw 的携带式纤维自伴随：to = fro = sw，对合同时作为两条往返律。这是
-- “可行嵌入 + 其抵消的、基底处恒等（故单射）的 lift”的 M 形态：自伴随
-- 即携带式双射。
------------------------------------------------------------------------
swapAdj : FiberAdjˢ (propEqOn Two) (propEqOn Two)
swapAdj = record
  { to       = sw
  ; fro      = sw
  ; to-cong  = λ e → cong sw e
  ; fro-cong = λ e → cong sw e
  ; η        = sw-invol
  ; ε        = sw-invol
  }

------------------------------------------------------------------------
-- The permuted label: a valid object-preserving CosmosData whose shape
-- routing is sw.  It is feasible (ana over it produces a CosmosM) and
-- its routing carries the invertible swapAdj, yet it changes shapes.
--
-- 置换标签：合法的对象保持 CosmosData，其形状路由为 sw。它可行（对其
-- 取 ana 产生 CosmosM），路由携带可逆的 swapAdj，却改变形状。
------------------------------------------------------------------------
permuted-label : MO.CosmosData C2 TwoFC
permuted-label = label sw

------------------------------------------------------------------------
-- Criterion C, M form: every routing f equipped with a left inverse
-- f⁻¹ (the canceling, injective lift) must fix every shape, i.e.
-- preserve the input F₀.
--
-- 判据 C 的 M 形态：每个配有左逆 f⁻¹（抵消的、单射的 lift）的路由 f
-- 必须固定每个形状，即保持输入 F₀。
------------------------------------------------------------------------
CriterionC : Set lzero
CriterionC =
  ∀ (f f⁻¹ : Two → Two)
  → (∀ (s : Two) → f⁻¹ (f s) ≡ s)
  → ∀ (s : Two) → f s ≡ s

-- Refutation: sw is its own left inverse (sw-invol) so it satisfies the
-- feasibility/injectivity premise, but it does not fix w0.  The
-- resulting w1 ≡ w0 is absorbed by constructive no-confusion.
--
-- 反驳：sw 是自身的左逆（sw-invol），满足可行性/单射前提，却不固定
-- w0。所得 w1 ≡ w0 由构造性无混淆吸收。
criterion-C-refuted : ¬ CriterionC
criterion-C-refuted cc =
  w1≢w0 (cc sw sw sw-invol w0)
