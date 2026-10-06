------------------------------------------------------------------------
-- Non-commutativity of the position permutation group Sₙ for n ≥ 3,
-- and the 3-cycle, on the carried M base.
--
-- Legacy result (Cosmos/FinCatNNonCommutative): for n ≥ 3 the permutation
-- group Sₙ is non-abelian — with s01 swapping positions 0↔1 and s12
-- swapping 1↔2, one has s01 ∘ s12 ≠ s12 ∘ s01, witnessed at position 1;
-- the composite c = s01 ∘ s12 is a 3-cycle (c³ = id, exact period 3).
-- The threshold is n = 3: for n = 2 the group is ℤ₂, which is abelian.
--
-- M-base reconstruction.  The algebra lives in the carried position
-- automorphism group PosAutˢ of slice 12 (ContainerAutomorphism,
-- Part A): a per-shape permutation with a carried two-sided inverse, no
-- naturality / subst field.  To keep EVERYTHING definitional and free of
-- Fin indexed matching (and hence of DecUIP/K), the finite position sets
-- are declared as ordinary, NON-indexed enumerations:
--
--   data Three : Set where t0 t1 t2 : Three   (the n = 3 fibre)
--   data Two   : Set where w0 w1    : Two     (the n = 2 fibre)
--
-- Pattern matching on their constructors is legal under
-- --cubical-compatible (they are not indexed), the two transpositions
-- are definitionally involutive, the 3-cycle reduces to refl in three
-- clauses, and every disequality is constructive no-confusion absorbed
-- by the empty pattern.  There is no subst, cast, Maybe, K or UIP.
--
-- The consequence at the cosmos level is the slice-11 engine: two
-- position permutations that differ as functions route a constant
-- relabelling differently, hence the induced trees are not bisimilar
-- (MorphismCorrespondence.swap-not-commute is exactly the head-routing
-- mismatch).  This module supplies the GROUP-LEVEL fact that makes such a
-- divergence unavoidable for n ≥ 3 (the two orderings of s01,s12 already
-- disagree at position 1), together with the n = 2 abelian threshold.
--
-- 携带式 M 底座上位置置换群 Sₙ 在 n ≥ 3 时的非交换性与 3-循环。
--
-- 旧结果（Cosmos/FinCatNNonCommutative）：n ≥ 3 时置换群 Sₙ 非阿贝尔
-- ——s01 交换位置 0↔1、s12 交换 1↔2，有 s01 ∘ s12 ≠ s12 ∘ s01，在位置
-- 1 处见证；复合 c = s01 ∘ s12 是 3-循环（c³ = id，恰周期 3）。阈值为
-- n = 3：n = 2 时群为 ℤ₂，阿贝尔。
--
-- M 底座重建。代数落在切片12（ContainerAutomorphism A 部）的携带位置
-- 自同构群 PosAutˢ：携带双侧逆的逐形状置换，无自然性 / subst 字段。为
-- 使一切定义性且免于 Fin 索引匹配（也即免于 DecUIP/K），有限位置集声
-- 明为普通的、非索引的枚举类型：
--
--   data Three : Set where t0 t1 t2 : Three   （n = 3 纤维）
--   data Two   : Set where w0 w1    : Two     （n = 2 纤维）
--
-- 在 --cubical-compatible 下匹配其构造子合法（它们非索引），两个对换
-- 定义性对合，3-循环三条子句即归约为 refl，每个不等都是构造性无混淆、
-- 由空模式吸收。无 subst、cast、Maybe、K 或 UIP。
--
-- 宇宙层后果即切片11 的引擎：作为函数不同的两个位置置换对常重标签的
-- 路由不同，故诱导的树不互模拟（MorphismCorrespondence.swap-not-commute
-- 正是头部路由失配）。本模块供给使该发散在 n ≥ 3 不可避免的群级事实
-- （s01、s12 的两种次序已在位置 1 处不同），以及 n = 2 的阿贝尔阈值。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.PermutationNonCommutative where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; cong; _≢_)
open import Relation.Binary.PropositionalEquality using (inspect; [_])

import ALMA.Cosmos.M.ContainerAutomorphism as CA

------------------------------------------------------------------------
-- The two finite position fibres as ordinary non-indexed enumerations.
-- 两个有限位置纤维，作为普通非索引枚举。
------------------------------------------------------------------------
data Three : Set where
  t0 t1 t2 : Three

data Two : Set where
  w0 w1 : Two

------------------------------------------------------------------------
-- Part 1. S₃ is non-abelian and contains a 3-cycle.
-- 第一部分：S₃ 非阿贝尔且含一个 3-循环。
------------------------------------------------------------------------
module S₃ where

  -- The position automorphism group of the single shape ⊤ with Three
  -- positions.
  -- 单形状 ⊤、Three 个位置的位置自同构群。
  open CA.PositionPermutationGroup (⊤ {lzero}) (λ _ → Three) public

  -- s01 swaps t0 ↔ t1, fixing t2; s12 swaps t1 ↔ t2, fixing t0.
  -- s01 交换 t0 ↔ t1、固定 t2；s12 交换 t1 ↔ t2、固定 t0。
  s01 : Three → Three
  s01 t0 = t1
  s01 t1 = t0
  s01 t2 = t2

  s12 : Three → Three
  s12 t0 = t0
  s12 t1 = t2
  s12 t2 = t1

  -- Both transpositions are definitionally involutive.
  -- 两个对换定义性对合。
  s01-invol : ∀ x → s01 (s01 x) ≡ x
  s01-invol t0 = refl
  s01-invol t1 = refl
  s01-invol t2 = refl

  s12-invol : ∀ x → s12 (s12 x) ≡ x
  s12-invol t0 = refl
  s12-invol t1 = refl
  s12-invol t2 = refl

  -- Lift an involutive function to a carried position automorphism whose
  -- two-sided inverse is itself.
  -- 把对合函数提升为双侧逆即自身的携带位置自同构。
  mkInvol : (f : Three → Three) → (∀ x → f (f x) ≡ x) → PosAutˢ
  mkInvol f invol = record
    { τ       = λ _ → f
    ; τ⁻¹     = λ _ → f
    ; τ-τ⁻¹   = λ _ x → invol x
    ; τ⁻¹-τ   = λ _ x → invol x
    }

  a01 : PosAutˢ
  a01 = mkInvol s01 s01-invol

  a12 : PosAutˢ
  a12 = mkInvol s12 s12-invol

  -- The two orderings of the transpositions.
  -- 两个对换的两种次序。
  c  : PosAutˢ   -- forward permutation s01 ∘ s12
  c  = a01 ∘PosAutˢ a12

  c' : PosAutˢ   -- forward permutation s12 ∘ s01
  c' = a12 ∘PosAutˢ a01

  -- Action of c = s01 ∘ s12: t0 ↦ t1, t1 ↦ t2, t2 ↦ t0 (a 3-cycle).
  -- c = s01 ∘ s12 的作用：t0 ↦ t1、t1 ↦ t2、t2 ↦ t0（3-循环）。
  c-at0 : τ c tt t0 ≡ t1
  c-at0 = refl
  c-at1 : τ c tt t1 ≡ t2
  c-at1 = refl
  c-at2 : τ c tt t2 ≡ t0
  c-at2 = refl

  -- Action of c' = s12 ∘ s01 at t1 is t0, whereas c sends t1 to t2.
  -- c' = s12 ∘ s01 在 t1 处为 t0，而 c 把 t1 送到 t2。
  c'-at1 : τ c' tt t1 ≡ t0
  c'-at1 = refl

  ----------------------------------------------------------------------
  -- Non-commutativity, witnessed at position 1: t2 ≠ t0.
  -- 非交换性，在位置 1 处见证：t2 ≠ t0。
  ----------------------------------------------------------------------
  t2≢t0 : ¬ (t2 ≡ t0)
  t2≢t0 ()

  s01-s12-noncommute : ¬ (c ≈PAˢ c')
  s01-s12-noncommute eq = t2≢t0 (trans (eq tt t1) (sym c'-at1))

  -- The Σ-witness form: there is a position at which the two composites
  -- disagree.
  -- Σ 见证形式：存在一个位置使两个复合不同。
  noncommute-witness : Σ Three λ x → τ c tt x ≢ τ c' tt x
  noncommute-witness = t1 , λ eq → t2≢t0 (trans eq (sym c'-at1))

  ----------------------------------------------------------------------
  -- Exact period 3 of c = s01 ∘ s12.
  -- c = s01 ∘ s12 恰周期 3。
  ----------------------------------------------------------------------
  -- c² sends t0 ↦ t2 (so c² ≠ id); c³ is the identity on all three.
  -- c² 把 t0 送到 t2（故 c² ≠ id）；c³ 在三者上均为恒等。
  c²-at0 : τ (c ∘PosAutˢ c) tt t0 ≡ t2
  c²-at0 = refl

  c³≈id : ((c ∘PosAutˢ c) ∘PosAutˢ c) ≈PAˢ idPosAutˢ
  c³≈id _ t0 = refl
  c³≈id _ t1 = refl
  c³≈id _ t2 = refl

  t1≢t0 : ¬ (t1 ≡ t0)
  t1≢t0 ()

  -- c ≠ id (witnessed at t0: c t0 = t1) and c² ≠ id (witnessed at t0:
  -- c² t0 = t2); together with c³ = id this makes the order exactly 3.
  -- c ≠ id（在 t0 处见证：c t0 = t1）且 c² ≠ id（在 t0 处见证：
  -- c² t0 = t2）；连同 c³ = id，其阶恰为 3。
  c-nonid : ¬ (c ≈PAˢ idPosAutˢ)
  c-nonid eq = t1≢t0 (eq tt t0)

  c²-nonid : ¬ ((c ∘PosAutˢ c) ≈PAˢ idPosAutˢ)
  c²-nonid eq = t2≢t0 (eq tt t0)

  -- The forward permutation of c iterated three times is the identity
  -- function; this is the function-level 3-cycle law.
  -- c 的正向置换迭代三次为恒等函数；这是函数级 3-循环律。
  c³-fun : ∀ x → (τ c tt ∘ τ c tt ∘ τ c tt) x ≡ x
  c³-fun t0 = refl
  c³-fun t1 = refl
  c³-fun t2 = refl

  -- Routing divergence precondition for the cosmos-level argument: the
  -- two orderings act differently at position 1.  By the slice-11 engine
  -- a constant relabelling along two permutations that disagree at a
  -- position yields two trees whose head routing differs and which are
  -- therefore not bisimilar (the empty-pattern head mismatch).
  --
  -- 宇宙层论证所需的路由发散前提：两种次序在位置 1 处作用不同。按切片
  -- 11 的引擎，沿两个在某位置不一致的置换对常重标签作用，得到头部路由
  -- 不同、因而不互模拟的两棵树（空模式头部失配）。
  routing-diverges : τ c tt t1 ≢ τ c' tt t1
  routing-diverges eq = t2≢t0 (trans eq (sym c'-at1))

------------------------------------------------------------------------
-- Part 2. S₂ = ℤ₂ is abelian (the n = 2 threshold).
-- 第二部分：S₂ = ℤ₂ 阿贝尔（n = 2 阈值）。
------------------------------------------------------------------------
module S₂ where

  open CA.PositionPermutationGroup (⊤ {lzero}) (λ _ → Two)

  -- The unique nonidentity permutation swaps w0 ↔ w1.
  -- 唯一的非恒等置换交换 w0 ↔ w1。
  sw : Two → Two
  sw w0 = w1
  sw w1 = w0

  sw-invol : ∀ x → sw (sw x) ≡ x
  sw-invol w0 = refl
  sw-invol w1 = refl

  swA : PosAutˢ
  swA = record
    { τ       = λ _ → sw
    ; τ⁻¹     = λ _ → sw
    ; τ-τ⁻¹   = λ _ x → sw-invol x
    ; τ⁻¹-τ   = λ _ x → sw-invol x
    }

  w0≢w1 : ¬ (w0 ≡ w1)
  w0≢w1 ()

  w1≢w0 : ¬ (w1 ≡ w0)
  w1≢w0 ()

  -- A carried two-position automorphism is determined by its value at w0;
  -- the carried two-sided inverse forces the value at w1 to be sw of it:
  -- a bijection of a two-element set that sends w0 to a must send the
  -- other element to the other value.  The proof uses only the carried
  -- left-inverse law (τ⁻¹ (τ x) ≡ x) and disjointness of the Two
  -- constructors; no equality is eliminated and no subst appears.
  --
  -- 携带的二元位置自同构由其在 w0 处的值决定；携带的双侧逆强制其在 w1
  -- 处的值为该值的 sw：二元集合上把 w0 送到 a 的双射必把另一元素送到另
  -- 一值。证明仅用携带的左逆律（τ⁻¹ (τ x) ≡ x）与 Two 构造子的不相交
  -- 性；不消去等式，也不出现 subst。
  at1-forced : (φ : PosAutˢ)
             → τ φ tt w1 ≡ sw (τ φ tt w0)
  -- Abstract the two forward values and the two left-inverse laws
  -- together, in dependency order; matching the forward values refines
  -- the types of both laws in one step.  The four (f w0, f w1) cases
  -- reduce to two refls and two disjoint-constructor contradictions.
  --
  -- 按依赖次序一次性抽象两个正向值与两条左逆律；匹配正向值即一步精化两
  -- 条律的类型。四个 (f w0, f w1) 情形归约为两个 refl 与两个构造子不相
  -- 交矛盾。
  at1-forced φ
    with τ φ tt w0 | τ φ tt w1 | τ⁻¹-τ φ tt w0 | τ⁻¹-τ φ tt w1
  ... | w0 | w0 | g0 | h = ⊥-elim (w0≢w1 (trans (sym g0) h))
  ... | w0 | w1 | _  | _ = refl
  ... | w1 | w0 | _  | _ = refl
  ... | w1 | w1 | g1 | h = ⊥-elim (w1≢w0 (trans (sym h) g1))

  -- Pointwise equality with the identity / swap, given the value at w0
  -- as an explicit equation.  The w1 clause threads at1-forced (which
  -- gives f w1 ≡ sw (f w0)) through the w0 equation; only trans/cong are
  -- used, never subst.
  --
  -- 给定 w0 处的值等式，给出与恒等 / 交换的逐点相等。w1 子句把
  -- at1-forced（给 f w1 ≡ sw (f w0)）穿过 w0 等式；仅用 trans/cong，绝不
  -- 用 subst。
  id-case : (φ : PosAutˢ) → τ φ tt w0 ≡ w0 → φ ≈PAˢ idPosAutˢ
  id-case φ e tt w0 = e
  id-case φ e tt w1 = trans (at1-forced φ) (cong sw e)

  sw-case : (φ : PosAutˢ) → τ φ tt w0 ≡ w1 → φ ≈PAˢ swA
  sw-case φ e tt w0 = e
  sw-case φ e tt w1 = trans (at1-forced φ) (cong sw e)

  -- Every two-position automorphism is either the identity or the swap.
  -- The with matches f w0, after which refl carries the forced equation.
  --
  -- 每个二元位置自同构不是恒等就是该交换。with 匹配 f w0，此后 refl 携
  -- 带被强制的等式。
  classify : (φ : PosAutˢ)
           → (φ ≈PAˢ idPosAutˢ) ⊎ (φ ≈PAˢ swA)
  classify φ with τ φ tt w0 | inspect (τ φ tt) w0
  ... | w0 | [ e ] = inj₁ (id-case φ e)
  ... | w1 | [ e ] = inj₂ (sw-case φ e)

  -- The swap is self-inverse (ℤ₂ multiplication).
  -- 该交换自逆（ℤ₂ 乘法）。
  sw²≈id : (swA ∘PosAutˢ swA) ≈PAˢ idPosAutˢ
  sw²≈id _ w0 = refl
  sw²≈id _ w1 = refl

  -- S₂ is abelian: classifying both factors as id or sw leaves four
  -- cases.  The middle composites agree definitionally (id is the
  -- identity function and sw is an involution), so each case is pure
  -- congruence up to pointwise equality.
  --
  -- S₂ 阿贝尔：把两个因子分类为 id 或 sw 后剩四种情形。中间复合定义性
  -- 相等（id 为恒等函数、sw 对合），故每种情形在逐点相等下都是纯同余。
  S₂-abelian : (φ ψ : PosAutˢ)
             → (φ ∘PosAutˢ ψ) ≈PAˢ (ψ ∘PosAutˢ φ)
  S₂-abelian φ ψ with classify φ | classify ψ
  ... | inj₁ φ≈id | inj₁ ψ≈id = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = idPosAutˢ}
                               {ψ = ψ} {ψ' = idPosAutˢ} φ≈id ψ≈id sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = idPosAutˢ}
                                   {ψ = φ} {ψ' = idPosAutˢ} ψ≈id φ≈id sh x))
  ... | inj₁ φ≈id | inj₂ ψ≈sw = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = idPosAutˢ}
                               {ψ = ψ} {ψ' = swA} φ≈id ψ≈sw sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = swA}
                                   {ψ = φ} {ψ' = idPosAutˢ} ψ≈sw φ≈id sh x))
  ... | inj₂ φ≈sw | inj₁ ψ≈id = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = swA}
                               {ψ = ψ} {ψ' = idPosAutˢ} φ≈sw ψ≈id sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = idPosAutˢ}
                                   {ψ = φ} {ψ' = swA} ψ≈id φ≈sw sh x))
  ... | inj₂ φ≈sw | inj₂ ψ≈sw = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = swA}
                               {ψ = ψ} {ψ' = swA} φ≈sw ψ≈sw sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = swA}
                                   {ψ = φ} {ψ' = swA} ψ≈sw φ≈sw sh x))
