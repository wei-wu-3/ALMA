------------------------------------------------------------------------
-- Carried limit system for the FinCat tower — existence core (zero subst).
--
-- The finite stages are trivial-fibre deterministic systems on
-- Fin (n-at m), with n-at m = suc (suc m). Their coinductive limit L∞ is
-- the trivial-fibre system on ℕ. The ONLY real datum is the deterministic
-- position transition.
--
-- The position axis is eliminated AT THE DEFINING SITE:
--
--   * The limit transition at position v is read from stage v itself:
--       s∞ v = toℕ (t v (natToFin v)).
--     Stage v has n-at v = suc (suc v) > v positions, so natToFin v is
--     ALWAYS in range. There is no out-of-range case, hence no partial
--     defaultFin / finFromℕ-maybe, no "sufficiently large layer"
--     threshold and no ≤-total split — the three devices that, in
--     WIP.agda, buried the guarded recursion under E1…E5 transports.
--
--   * natToFin v is the canonical in-range representative (toℕ = v),
--     defined here self-containedly by ℕ recursion (no Fin indexed
--     pattern match, so it is Cubical-Agda transport-safe).
--
-- The coinductive orbit (the deterministic tree over L∞) is written in
-- edge-indexed style: below y e = orbit y. The child index y is carried
-- BY THE EDGE e; we recurse at y directly, never matching the successor
-- equation inside e and never transporting. For the trivial fibre there
-- is exactly one such y (y ≡ s∞ x).
--
-- This slice fixes L∞ and its orbit. In-range projection coherence (the
-- stage-m reading commuting with s∞ for positions present at stage m) and
-- the bisimulation cone / uniqueness are added in following slices.
--
-- FinCat 塔的携带式极限系统 —— 存在性核心（零 subst）。
--
-- 有限层是 Fin (n-at m) 上的平凡纤维确定性系统，n-at m = suc (suc m)。
-- 其余归纳极限 L∞ 是 ℕ 上的平凡纤维系统；唯一真实数据是确定性位置转移。
--
-- 位置轴在定义点即被消除：
--
--   * 位置 v 处的极限转移直接从第 v 层读取：
--       s∞ v = toℕ (t v (natToFin v))。
--     第 v 层有 n-at v = suc (suc v) > v 个位置，故 natToFin v 永远在范
--     围内。没有越界情形，因而没有偏函数 defaultFin / finFromℕ-maybe、
--     没有"足够大层"阈值、没有 ≤-total 情形划分 —— 正是这三样东西在
--     WIP.agda 里把受保护递归掩埋在 E1…E5 传输之下。
--
--   * natToFin v 是典范的范围内代表（toℕ = v），在此自包含地以 ℕ 递归
--     定义（不对 Fin 做索引模式匹配，对 Cubical Agda 传输安全）。
--
-- 余归纳轨道（L∞ 上的确定性树）以边索引风格书写：below y e = orbit y。
-- 子索引 y 由边 e 携带；直接在 y 处递归，绝不匹配 e 内的后继等式，绝不
-- 传输。平凡纤维下恰有一个这样的 y（y ≡ s∞ x）。
--
-- 本切片固定 L∞ 与其轨道。范围内投影相干性（第 m 层读数对该层存在位置
-- 与 s∞ 交换）及互模拟余锥 / 唯一性在后续切片补齐。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.LimitSystem where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties
  using ( ≤-pred; ≤-refl; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; n≤0⇒n≡0
        ; m≥n⇒m⊓n≡n )
open import Data.Fin.Base using (Fin; zero; suc; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁; toℕ<n)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ALMA.Base.MCorr using (here; below)
open import ALMA.Cosmos.Carried.DetSys
open import ALMA.Cosmos.Carried.SeqColimit using (shift)
open import ALMA.Cosmos.Carried.FinProj using (clamp; clamp-val)

-- Size of the object set of FinCatN m: n-at m = suc (suc m).
--
-- FinCatN m 对象集的大小：n-at m = suc (suc m)。
n-at : ℕ → ℕ
n-at m = suc (suc m)

-- The canonical representative of natural position v in stage v.
-- natToFin v : Fin (n-at v), and n-at v > v, so it is always in range.
--
-- 自然位置 v 在第 v 层的典范代表。natToFin v : Fin (n-at v)，且
-- n-at v > v，故永远在范围内。
natToFin : (v : ℕ) → Fin (n-at v)
natToFin zero    = zero
natToFin (suc v) = suc (natToFin v)

-- toℕ (natToFin v) ≡ v, by ℕ recursion only.
--
-- toℕ (natToFin v) ≡ v，仅对 ℕ 递归。
toℕ-natToFin : (v : ℕ) → toℕ (natToFin v) ≡ v
toℕ-natToFin zero    = refl
toℕ-natToFin (suc v) = cong suc (toℕ-natToFin v)

-- d-fold finite embedding Fin (n-at m) → Fin (n-at (shift d m)), by
-- iterating inject₁. The target size is computed by the same `shift`
-- recursion as the carried chain (SeqColimit), so
-- n-at (shift d m) reduces DEFINITIONALLY to the d-times-enlarged Fin
-- size. There is no subst Fin (+-suc) / castCosmos / ShiftedTower: the
-- old inject₁^d packaged every result in
--   subst Fin (cong n-at (sym (+-suc m d))) ...,
-- which is exactly the layer-arithmetic transport axis, now baked into
-- the recursion.
--
-- d 次有限嵌入 Fin (n-at m) → Fin (n-at (shift d m))，迭代 inject₁ 而
-- 成。目标尺寸由携带链（SeqColimit）的同一 shift 递归计算，故
-- n-at (shift d m) 定义性归约为放大 d 次的 Fin 尺寸。不存在
-- subst Fin (+-suc) / castCosmos / ShiftedTower：旧 inject₁^d 把每个结
-- 果包一层 subst Fin (cong n-at (sym (+-suc m d)))，那正是层算术传输
-- 轴，现已烤进递归。
embFin : (d m : ℕ) → Fin (n-at m) → Fin (n-at (shift d m))
embFin zero    m x = x
embFin (suc d) m x = embFin d (suc m) (inject₁ x)

-- The iterated embedding preserves the natural-number position.
--
-- 迭代嵌入保持自然数位置。
toℕ-embFin : ∀ d m (x : Fin (n-at m))
           → toℕ (embFin d m x) ≡ toℕ x
toℕ-embFin zero    m x = refl
toℕ-embFin (suc d) m x =
  trans (toℕ-embFin d (suc m) (inject₁ x)) (toℕ-inject₁ x)

-- Stage-m representative of a natural position k, as the TOTAL clamp
-- into Fin (n-at m). For in-range k ≤ suc m its toℕ reading is exactly k
-- (clamp saturates only beyond the stage). clamp is total and defined by
-- ℕ recursion, so there is NO Fin indexed pattern match and NO Cubical
-- absurd pattern on ≤ proofs (which carry hcomp and are not empty for
-- unification): the position axis is represented by a total function.
--
-- 自然位置 k 在第 m 层的代表，即向 Fin (n-at m) 的全函数 clamp。范围
-- 内 k ≤ suc m 时其 toℕ 读数恰为 k（clamp 仅在超出该层时饱和）。clamp
-- 全函数且由 ℕ 递归定义，故无 Fin 索引模式匹配，也无对 ≤ 证明的
-- Cubical 空模式（≤ 带 hcomp，统一时不为空）：位置轴由全函数表示。
cl : (m k : ℕ) → Fin (n-at m)
cl m k = clamp {k = suc m} k

-- In-range reading of the stage-m representative: toℕ (cl m k) ≡ k.
--
-- 第 m 层代表的范围内读数：toℕ (cl m k) ≡ k。
cl-toℕ : ∀ m k (le : k ≤ suc m) → toℕ (cl m k) ≡ k
cl-toℕ m k le =
  trans (clamp-val {k = suc m} k) (m≥n⇒m⊓n≡n le)

------------------------------------------------------------------------
-- The limit system, parameterised by the per-stage deterministic
-- position transition t m : Fin (n-at m) → Fin (n-at m).
--
-- 极限系统，以各层确定性位置转移 t m : Fin (n-at m) → Fin (n-at m)
-- 为参数。
------------------------------------------------------------------------
module LimitSystem
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  -- One-step embedding compatibility: advancing one stage commutes with
  -- the transition on the inherited (non-new-top) positions. This is the
  -- carried form of the live tower's embedF₀ / compat; it is a bare
  -- homogeneous equation on Fin, never a transport.
  --
  -- 一步嵌入相容：推进一层与继承位置（非新末位）上的转移交换。这是真实
  -- 塔 embedF₀ / compat 的携带形式；它是 Fin 上的裸同质等式，绝非传输。
  (embed-compat :
     (m : ℕ) (x : Fin (n-at m))
   → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  -- Limit position transition: read at the stage that always contains v.
  --
  -- 极限位置转移：在永远包含 v 的第 v 层读取。
  s∞ : ℕ → ℕ
  s∞ v = toℕ (t v (natToFin v))

  -- L∞ is the trivial-fibre deterministic system on ℕ with transition s∞.
  --
  -- L∞ 是 ℕ 上以 s∞ 为转移的平凡纤维确定性系统。
  open TrivDet ℕ s∞
    using (sys; E; DetM)

  L∞ = sys

  -- Coinductive orbit of the deterministic limit dynamics. In
  -- edge-indexed form the child index y is carried by e, so the
  -- continuation is orbit y — no successor equation is matched and no
  -- transport is needed. The call is guarded directly by `below`.
  --
  -- 确定性极限动力学的余归纳轨道。边索引形式下子索引 y 由 e 携带，故
  -- 连续项就是 orbit y —— 不匹配后继等式、无需传输。递归调用直接由
  -- below 保护。
  orbit∞ : (x : ℕ) → DetM x
  orbit∞ x .here      = tt
  orbit∞ x .below y _ = orbit∞ y

  ----------------------------------------------------------------------
  -- In-range reading coherence: every position present at stage m is
  -- read by the limit transition s∞. The split "inherited position vs
  -- new top" is the BOUNDED disjunction k ≤ suc m → k < suc m ⊎ k ≡ suc m
  -- (one layer), NOT the unbounded ≤-total threshold of WIP.agda. Fin
  -- constructors are never pattern-matched (no Cubical absurd pattern,
  -- no UnsupportedIndexedMatch): arbitrary positions are normalised to
  -- the total `cl` representative via toℕ-injective, and every step is a
  -- homogeneous equation. There is no subst / cast.
  --
  -- 范围内读数相干性：第 m 层存在的每个位置都被极限转移 s∞ 正确读取。
  -- "继承位置 vs 新末位"的拆分是有界析取 k ≤ suc m → k < suc m ⊎
  -- k ≡ suc m（只跨一层），不是 WIP.agda 里的无界 ≤-total 阈值。全程不
  -- 对 Fin 构造子模式匹配（无 Cubical 空模式、无 UnsupportedIndexed
  -- Match）：任意位置经 toℕ-injective 归一为全函数代表 cl，每一步都是
  -- 同质等式。没有 subst / cast。
  ----------------------------------------------------------------------
  private
    -- One upward embedding step, read at natural-number level.
    --
    -- 一次上行嵌入，在自然数层读取。
    up-toℕ : ∀ m x → toℕ (t (suc m) (inject₁ x)) ≡ toℕ (t m x)
    up-toℕ m x =
      trans (cong toℕ (embed-compat m x)) (toℕ-inject₁ (t m x))

    -- At an inherited (non-new-top) position, the stage (suc p)
    -- representative equals inject₁ of the stage-p representative.
    --
    -- 在继承位置（非新末位）上，第 suc p 层代表等于第 p 层代表的
    -- inject₁。
    inj-clamp : ∀ p k (le : k ≤ suc p)
              → cl (suc p) k ≡ inject₁ (cl p k)
    inj-clamp p k le =
      toℕ-injective
        (trans (cl-toℕ (suc p) k (m≤n⇒m≤1+n le))
          (sym (trans (toℕ-inject₁ (cl p k))
                      (cl-toℕ p k le))))

    -- inject₁ of stage s's top is the canonical representative of s+1.
    --
    -- 第 s 层末位的 inject₁ 即 s+1 的典范代表。
    inj-top : ∀ s → inject₁ (cl s (suc s)) ≡ natToFin (suc s)
    inj-top s =
      toℕ-injective
        (trans (trans (toℕ-inject₁ (cl s (suc s)))
                      (cl-toℕ s (suc s) ≤-refl))
               (sym (toℕ-natToFin (suc s))))

  -- Reading at stage s's top agrees with the limit transition at s+1
  -- (a single upward embedding step).
  --
  -- 第 s 层末位的读数与 s+1 处的极限转移一致（一次上行嵌入）。
  top-read : ∀ s → toℕ (t s (cl s (suc s))) ≡ s∞ (suc s)
  top-read s =
    sym
      (trans (cong toℕ (cong (t (suc s)) (sym (inj-top s))))
        (trans (cong toℕ (embed-compat s (cl s (suc s))))
               (toℕ-inject₁ (t s (cl s (suc s))))))

  -- In-range reading for a natural position k at stage m.
  --
  -- 第 m 层自然位置 k 的范围内读数。
  read-cl : ∀ m k (le : k ≤ suc m)
          → toℕ (t m (cl m k)) ≡ s∞ k
  read-cl zero k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq = top-read zero
  ... | inj₁ lt rewrite n≤0⇒n≡0 (≤-pred lt) = refl
  read-cl (suc p) k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq = top-read (suc p)
  ... | inj₁ lt =
    let le' : k ≤ suc p
        le' = ≤-pred lt
    in trans (cong toℕ (cong (t (suc p)) (inj-clamp p k le')))
             (trans (up-toℕ p (cl p k))
                    (read-cl p k le'))

  -- In-range reading for EVERY position x present at stage m.
  --
  -- 第 m 层存在的每个位置 x 的范围内读数。
  read-coh : ∀ m (x : Fin (n-at m))
           → toℕ (t m x) ≡ s∞ (toℕ x)
  read-coh m x =
    let le : toℕ x ≤ suc m
        le = ≤-pred (toℕ<n x)
        eqx : x ≡ cl m (toℕ x)
        eqx = toℕ-injective (sym (cl-toℕ m (toℕ x) le))
    in trans (cong toℕ (cong (t m) eqx))
             (read-cl m (toℕ x) le)
