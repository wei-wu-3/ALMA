------------------------------------------------------------------------
-- FinColimit: zero-subst colimit of the finite stages Fin (n-at m)
--
-- The family of finite object sets {Fin (n-at m)}, n-at m = suc (suc m),
-- embeds by iterated inject₁; its colimit is ℕ via toℕ. This is the
-- carried, zero-subst / zero-cast replacement for the Set-level universal
-- property previously proved in FinCatInfinity.agda, whose debt came
-- from two axes:
--
--   * the layer-arithmetic axis: inject₁^d packaged every result in
--       subst Fin (cong n-at (sym (+-suc m d))) ...,
--     because the target Fin size was stated with + and did not reduce.
--     Here the d-fold embedding is embFin (from LimitSystem), whose
--     target size n-at (shift d m) reduces DEFINITIONALLY (shift d m is
--     the same recursion as m + d);
--
--   * the Fin-position axis: value-independent-of-m used the unbounded
--     two-way ≤-total split and the partial defaultFin. Here every
--     position is read through the TOTAL clamp representative cl, with a
--     single BOUNDED split m≤n⇒m<n∨m≡n and structural recursion on the
--     stage m (no Fin indexed match, no Cubical absurd pattern on ≤).
--
-- The public API colimitUniv has exactly the same shape as the old one,
-- so consumers switch by import alone.
--
-- FinColimit：有限层 Fin (n-at m) 的零 subst 余极限
--
-- 有限对象集族 {Fin (n-at m)}（n-at m = suc (suc m)）经迭代 inject₁ 嵌
-- 入，其余极限为经 toℕ 的 ℕ。本模块是先前 FinCatInfinity.agda 中 Set 层
-- 泛性质的携带式、零 subst / 零 cast 替代，旧证明的债务来自两条轴：
--
--   * 层算术轴：inject₁^d 把每个结果包一层
--       subst Fin (cong n-at (sym (+-suc m d))) ...，
--     因为目标 Fin 尺寸用 + 陈述而不归约。这里 d 次嵌入用
--     LimitSystem 的 embFin，其目标尺寸 n-at (shift d m) 定义性归约
--     （shift d m 与 m + d 是同一递归）；
--
--   * Fin 位置轴：value-independent-of-m 用无界双向 ≤-total 拆分与偏
--     defaultFin。这里每个位置经全函数 clamp 代表 cl 读取，只用一次有
--     界拆分 m≤n⇒m<n∨m≡n，并对层号 m 结构递归（无 Fin 索引匹配，无对
--     ≤ 的 Cubical 空模式）。
--
-- 公开 API colimitUniv 与旧版同形，消费方仅改导入即可切换。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.FinColimit where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans)

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties
  using ( ≤-pred; ≤-refl; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; n≤0⇒n≡0 )
open import Data.Fin.Base using (Fin; zero; toℕ; inject₁)
open import Data.Fin.Properties
  using (toℕ-injective; toℕ-inject₁; toℕ<n)
open import Data.Sum.Base using (inj₁; inj₂)

open import ALMA.Cosmos.Carried.SeqColimit using (shift)
open import ALMA.Cosmos.Carried.LimitSystem
  using (n-at; natToFin; toℕ-natToFin; embFin; cl; cl-toℕ)

------------------------------------------------------------------------
-- Pure Fin representatives (independent of the cone).
--
-- 纯 Fin 代表（与锥无关）。
------------------------------------------------------------------------

-- At the top of stage m, one inject₁ reaches the canonical element of
-- stage suc m with the same natural reading.
--
-- 在第 m 层顶端，一次 inject₁ 到达第 suc m 层具有相同自然读数的典范
-- 元素。
top-eq : ∀ m → inject₁ (cl m (suc m)) ≡ natToFin (suc m)
top-eq m =
  toℕ-injective
    (trans (toℕ-inject₁ (cl m (suc m)))
      (trans (cl-toℕ m (suc m) ≤-refl)
             (sym (toℕ-natToFin (suc m)))))

-- Below the top, the stage-(suc p) representative is one inject₁ of the
-- stage-p representative.
--
-- 顶端以下，第 suc p 层代表是第 p 层代表的一次 inject₁。
inj-cl : ∀ p k (le : k ≤ suc p)
       → cl (suc p) k ≡ inject₁ (cl p k)
inj-cl p k le =
  toℕ-injective
    (trans (cl-toℕ (suc p) k (m≤n⇒m≤1+n le))
      (sym (trans (toℕ-inject₁ (cl p k))
                  (cl-toℕ p k le))))

------------------------------------------------------------------------
-- A compatible cone over the finite stages, valued in a set X.
-- at (suc m) (inject₁ x) ≡ at m x is the one-step compatibility.
--
-- 有限层上取值于集合 X 的相容锥。
-- at (suc m) (inject₁ x) ≡ at m x 是一步相容性。
------------------------------------------------------------------------
record FinCone (X : Set) : Set where

  field
    at     : ∀ m → Fin (n-at m) → X
    compat : ∀ m (x : Fin (n-at m))
           → at (suc m) (inject₁ x) ≡ at m x

  -- d-fold compatibility along embFin: the target Fin size reduces
  -- DEFINITIONALLY via shift, so there is no subst Fin (+-suc).
  --
  -- 沿 embFin 的 d 次相容性：目标 Fin 尺寸经 shift 定义性归约，故无
  -- subst Fin (+-suc)。
  compat-emb : ∀ d m (x : Fin (n-at m))
             → at (shift d m) (embFin d m x) ≡ at m x
  compat-emb zero    m x = refl
  compat-emb (suc d) m x =
    trans (compat-emb d (suc m) (inject₁ x))
          (compat m x)

  -- The stage-m clamp representative of k reads the same cone value as
  -- the canonical element at stage k. Structural recursion on m; the
  -- top case (k ≡ suc m) goes one stage up via compat, the inherited case
  -- (k ≤ suc p) descends via compat and the recursion at stage p.
  --
  -- 第 m 层的 k 的 clamp 代表与第 k 层典范元素读到相同的锥值。对 m 结构
  -- 递归：顶端情形（k ≡ suc m）经 compat 上走一层；继承情形（k ≤ suc p）
  -- 经 compat 下降并在第 p 层递归。
  at-cl : ∀ m k (le : k ≤ suc m)
        → at m (cl m k) ≡ at k (natToFin k)
  at-cl zero k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq =
    sym (trans (cong (at (suc zero)) (sym (top-eq zero)))
               (compat zero (cl zero (suc zero))))
  ... | inj₁ lt rewrite n≤0⇒n≡0 (≤-pred lt) = refl
  at-cl (suc p) k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq =
    sym (trans (cong (at (suc (suc p))) (sym (top-eq (suc p))))
               (compat (suc p) (cl (suc p) (suc (suc p)))))
  ... | inj₁ lt =
    let le' : k ≤ suc p
        le' = ≤-pred lt
    in trans (cong (at (suc p)) (inj-cl p k le'))
             (trans (compat p (cl p k))
                    (at-cl p k le'))

  -- The unique extension g∞ : ℕ → X reads the canonical element of the
  -- stage equal to the natural index.
  --
  -- 唯一扩展 g∞ : ℕ → X，读取等于自然索引那一层的典范元素。
  g∞ : ℕ → X
  g∞ k = at k (natToFin k)

  -- g∞ (toℕ x) ≡ at m x: identify x with the clamp representative at
  -- stage m and then use at-cl.
  --
  -- g∞ (toℕ x) ≡ at m x：把 x 认同为第 m 层的 clamp 代表，再用 at-cl。
  extends : ∀ m (x : Fin (n-at m)) → g∞ (toℕ x) ≡ at m x
  extends m x =
    let k  : ℕ
        k  = toℕ x
        le : k ≤ suc m
        le = ≤-pred (toℕ<n x)
        eqx : x ≡ cl m k
        eqx = toℕ-injective (sym (cl-toℕ m k le))
    in trans (sym (at-cl m k le))
             (cong (at m) (sym eqx))

  -- Any other extension h agreeing on every finite stage equals g∞ at
  -- every natural index: k is toℕ (natToFin k) definitionally in value.
  --
  -- 任何在每个有限层都一致的扩展 h 在每个自然索引处等于 g∞：k 在值上
  -- 即为 toℕ (natToFin k)。
  unique : (h : ℕ → X)
         → (∀ m (x : Fin (n-at m)) → h (toℕ x) ≡ at m x)
         → ∀ k → h k ≡ g∞ k
  unique h h-ext k =
    trans (cong h (sym (toℕ-natToFin k)))
          (h-ext k (natToFin k))

open FinCone public

------------------------------------------------------------------------
-- The Set-level universal property, same shape as the old
-- FinCatInfinity.colimitUniv so consumers switch by import alone.
--
-- Set 层泛性质，与旧 FinCatInfinity.colimitUniv 同形，消费方仅改导入。
------------------------------------------------------------------------
colimitUniv
  : ∀ {X : Set} (cone : FinCone X)
  → Σ (ℕ → X) λ g∞ →
      Σ (∀ m (x : Fin (n-at m)) → g∞ (toℕ x) ≡ at cone m x) λ _ →
        (∀ (h : ℕ → X)
         → (∀ m (x : Fin (n-at m)) → h (toℕ x) ≡ at cone m x)
         → ∀ k → h k ≡ g∞ k)
colimitUniv cone = g∞ cone , (extends cone , unique cone)
