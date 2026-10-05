------------------------------------------------------------------------
-- degeneration: ScaleInvariant at Obs = ⊤
-- The non-trivial theory on this position is Coalgebra,
-- obtained by adding x ≡ y as base
--   Iteration     the free monoid action of ℕ on X induced by f
--   Coalgebra     the final coalgebra equality of f
--
-- 退化：Obs = ⊤ 处的 ScaleInvariant
-- 该位置上的非平凡理论是 Coalgebra，由加上 base case x ≡ y 得到
--   Iteration     由 f 诱导的 ℕ 在 X 上的自由幺半群作用
--   Coalgebra     f 的最终 coalgebra 相等
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.LinearDynamics where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc)
open import Data.Product.Base using (proj₁; proj₂; _×_)

open import ALMA.Base.IndexedMType using (snd)
open import ALMA.Base.Equivalence.ScaleInvariant using (ScaleInvariant)

------------------------------------------------------------------------
-- The alias
-- ScaleInvariant's universe depends only on Obs, not on X
-- 别名
-- ScaleInvariant 的 universe 只依赖 Obs，不依赖 X
LinearDynamics : {a : _} {X : Set a} → (f : X → X) → X → X → Set lzero
LinearDynamics {a} {X} f = ScaleInvariant {Obs = ⊤ {lzero}} (λ x _ → f x)

------------------------------------------------------------------------
-- Iteration theory: the free monoid action of ℕ on X induced by f
-- The iteration operator satisfies the two monoid action laws:
--   f^[0] = id
--   f^[m+n] = f^[m] ∘ f^[n]
-- These are the only equations imposed by iteration alone: the
-- action is free, so no two states are identified by iteration
--
-- 迭代理论：由 f 诱导的 ℕ 在 X 上的自由幺半群作用
-- 迭代算子满足两条幺半群作用律：
--   f^[0] = id
--   f^[m+n] = f^[m] ∘ f^[n]
-- 这是迭代单独施加的唯一方程：作用是自由的，因此没有两个状态被迭代等同
module Iteration
    {a : _} {X : Set a}
    (f : X → X) where

  -- Iteration
  --
  -- 迭代
  _^[_] : X → ℕ → X
  x ^[ zero ]  = x
  x ^[ suc n ] = f (x ^[ n ])

  -- Iteration law: zero
  --
  -- 迭代律：零
  ^-zero : ∀ x → x ^[ 0 ] ≡ x
  ^-zero x = refl

  -- Iteration law: successor
  --
  -- 迭代律：后继
  ^-suc : ∀ x n → x ^[ suc n ] ≡ f (x ^[ n ])
  ^-suc x n = refl

  -- Shift law: applying f first and then iterating n times agrees
  -- with iterating suc n times.
  -- This bridges the two syntactic forms x ^[ suc n ] and (f x) ^[ n ]
  --
  -- 移位律：先应用 f 再迭代 n 次，与迭代 suc n 次一致
  -- 这桥接了两种语法形式 x ^[ suc n ] 与 (f x) ^[ n ]
  ^-suc-shift : ∀ x n → x ^[ suc n ] ≡ (f x) ^[ n ]
  ^-suc-shift x zero    = refl
  ^-suc-shift x (suc n) = cong f (^-suc-shift x n)

  -- Iteration law: addition
  -- Proved by induction on n, using +-identityʳ and +-suc to
  -- rewrite the index
  --
  -- 迭代律：加法
  -- 对 n 归纳，使用 +-identityʳ 与 +-suc 重写索引
  ^-+ : ∀ x m n → x ^[ m + n ] ≡ (x ^[ m ]) ^[ n ]
  ^-+ x m zero    = cong (λ k → x ^[ k ]) (+-identityʳ m)
  ^-+ x m (suc n) = begin
    x ^[ m + suc n ]
      ≡⟨ cong (λ k → x ^[ k ]) (+-suc m n) ⟩
    x ^[ suc (m + n) ]
      ≡⟨ refl ⟩
    f (x ^[ m + n ])
      ≡⟨ cong f (^-+ x m n) ⟩
    f ((x ^[ m ]) ^[ n ])
      ≡⟨ refl ⟩
    (x ^[ m ]) ^[ suc n ]
      ∎

  -- The iteration operator is a monoid action
  --
  -- 迭代算子是幺半群作用
  iteration-action : ∀ x m n → x ^[ m + n ] ≡ (x ^[ m ]) ^[ n ]
  iteration-action = ^-+

------------------------------------------------------------------------
-- Coalgebra theory: the final coalgebra equality of f
-- Two states are synchronous when all their iterates agree. This
-- relation is the final coalgebra equality: it is the largest
-- relation R with R x y → x ≡ y × R (f x) (f y). The coinductive
-- characterisation makes precise that Sync is the "behavioural
-- equality" of the deterministic coalgebra (X, f)
--
-- Coalgebra 理论：f 的最终 coalgebra 相等
-- 两个状态同步当且仅当所有迭代一致。该关系是最终 coalgebra 相等：
-- 它是满足 R x y → x ≡ y × R (f x) (f y) 的最大关系 R。余归纳
-- 刻画精确陈述了 Sync 是确定性 coalgebra (X, f) 的「行为相等」
module Coalgebra
    {a : _} {X : Set a}
    (f : X → X) where

  open Iteration f

  -- Synchronisation: all iterates agree
  --
  -- 同步：所有迭代相等
  Sync : X → X → Set a
  Sync x y = ∀ n → x ^[ n ] ≡ y ^[ n ]

  -- Sync is an equivalence relation
  --
  -- 同步是等价关系
  sync-isEquivalence : IsEquivalence Sync
  sync-isEquivalence = record
    { refl  = λ {x} n → refl
    ; sym   = λ p n → sym (p n)
    ; trans = λ p q n → trans (p n) (q n)
    }

  -- Coinductive characterisation: Sync x y iff x ≡ y and
  -- Sync (f x) (f y). The two directions are the base case and the
  -- recursive case. The shift law ^-suc-shift converts between the
  -- two syntactic forms x ^[ suc n ] and (f x) ^[ n ]
  --
  -- 余归纳刻画：Sync x y 当且仅当 x ≡ y 且 Sync (f x) (f y)
  -- 两个方向分别是 base case 与递归 case。移位律 ^-suc-shift
  -- 在两种语法形式 x ^[ suc n ] 与 (f x) ^[ n ] 之间转换
  sync-char : ∀ {x y} → Sync x y → (x ≡ y) × Sync (f x) (f y)
  sync-char {x} {y} p =
    p 0 ,
    (λ n → begin
      (f x) ^[ n ]
        ≡⟨ sym (^-suc-shift x n) ⟩
      x ^[ suc n ]
        ≡⟨ p (suc n) ⟩
      y ^[ suc n ]
        ≡⟨ ^-suc-shift y n ⟩
      (f y) ^[ n ]
        ∎)

  sync-intro : ∀ {x y} → x ≡ y → Sync (f x) (f y) → Sync x y
  sync-intro {x} {y} refl q zero    = refl
  sync-intro {x} {y} refl q (suc n) = begin
    x ^[ suc n ]
      ≡⟨ ^-suc-shift x n ⟩
    (f x) ^[ n ]
      ≡⟨ q n ⟩
    (f y) ^[ n ]
      ≡⟨ sym (^-suc-shift y n) ⟩
    y ^[ suc n ]
      ∎

  -- Sync is the final coalgebra equality: it is the largest relation
  -- R with R x y → x ≡ y × R (f x) (f y)
  --
  -- Sync 是最终 coalgebra 相等：它是满足
  -- R x y → x ≡ y × R (f x) (f y) 的最大关系 R
  sync-final
    : (R : X → X → Set a)
    → (∀ {x y} → R x y → (x ≡ y) × R (f x) (f y))
    → ∀ {x y} → R x y → Sync x y
  sync-final R step {x} {y} r zero    = proj₁ (step r)
  sync-final R step {x} {y} r (suc n) = begin
    x ^[ suc n ]
      ≡⟨ ^-suc-shift x n ⟩
    (f x) ^[ n ]
      ≡⟨ sync-final R step (proj₂ (step r)) n ⟩
    (f y) ^[ n ]
      ≡⟨ sym (^-suc-shift y n) ⟩
    y ^[ suc n ]
      ∎

  -- Sync is reflexive
  --
  -- Sync 自反
  sync-refl : ∀ x → Sync x x
  sync-refl x = IsEquivalence.refl sync-isEquivalence

  -- Fixed points: states invariant under f
  --
  -- 不动点：在 f 下不变的状态
  IsFixed : X → Set a
  IsFixed x = f x ≡ x

  -- Periodic points: states returning to themselves after some
  -- positive number of iterations
  --
  -- 周期点：经过某个正数次迭代后回到自身的状态
  IsPeriodic : X → Set a
  IsPeriodic x = Σ ℕ (λ n → Σ (0 < n) (λ _ → x ^[ n ] ≡ x))

  -- Fixed points are periodic (with period 1)
  --
  -- 不动点是周期点（周期为 1）
  fixed→periodic : ∀ {x} → IsFixed x → IsPeriodic x
  fixed→periodic {x} fx = 1 , (s≤s z≤n , fx)

  -- Periodicity is preserved by iteration: if x has period p, then
  -- every iterate x^[k] has period p
  --
  -- 周期性在迭代下保持：若 x 的周期为 p，则每个迭代 x^[k] 的周期也是 p
  periodic-stable
    : ∀ {x} → IsPeriodic x
    → Σ ℕ (λ p → Σ (0 < p) (λ _ → ∀ k → (x ^[ k ]) ^[ p ] ≡ x ^[ k ]))
  periodic-stable {x} (p , 0<p , eq) = p , 0<p , period-iter
    where
      period-iter : ∀ k → (x ^[ k ]) ^[ p ] ≡ x ^[ k ]
      period-iter k = begin
        (x ^[ k ]) ^[ p ]
          ≡⟨ sym (^-+ x k p) ⟩
        x ^[ k + p ]
          ≡⟨ cong (λ j → x ^[ j ]) (+-comm k p) ⟩
        x ^[ p + k ]
          ≡⟨ ^-+ x p k ⟩
        (x ^[ p ]) ^[ k ]
          ≡⟨ cong (λ z → z ^[ k ]) eq ⟩
        x ^[ k ]
          ∎

  -- Periodicity gives an iterated period: the sequence is periodic
  -- with period p from the start
  --
  -- 周期性给出迭代周期：序列从起点起以 p 为周期
  periodic-iterate
    : ∀ {x} → IsPeriodic x
    → Σ ℕ (λ p → Σ (0 < p) (λ _ → ∀ n → x ^[ n + p ] ≡ x ^[ n ]))
  periodic-iterate {x} (p , 0<p , eq) = p , 0<p , period-law
    where
      period-law : ∀ n → x ^[ n + p ] ≡ x ^[ n ]
      period-law n = begin
        x ^[ n + p ]
          ≡⟨ cong (λ j → x ^[ j ]) (+-comm n p) ⟩
        x ^[ p + n ]
          ≡⟨ ^-+ x p n ⟩
        (x ^[ p ]) ^[ n ]
          ≡⟨ cong (λ z → z ^[ n ]) eq ⟩
        x ^[ n ]
          ∎

------------------------------------------------------------------------
-- Truncation: since there is no layer condition, every depth is
-- trivially inhabited
-- This is the flat truncation at the empty observation limit
--
-- 截断：没有 layer 条件，每个深度都平凡可居
-- 这是空观察极限处的平坦截断
module LinearDynamics-Depth
    {a : _} {X : Set a} {f : X → X} where

  LD-depth : (n : ℕ) → (x y : X) → Set lzero
  LD-depth zero    x y = ⊤ {lzero}
  LD-depth (suc n) x y = LD-depth n (f x) (f y)

  ld→LD-depth : ∀ {x y} → LinearDynamics f x y
              → ∀ n → LD-depth n x y
  ld→LD-depth p zero    = tt
  ld→LD-depth p (suc n) = ld→LD-depth (p .snd tt) n

  LD-depth-mono : ∀ {m n} (m≤n : m ≤ n) {x y : X}
                → LD-depth n x y → LD-depth m x y
  LD-depth-mono z≤n       p = tt
  LD-depth-mono (s≤s m≤n) {x} {y} p =
    LD-depth-mono m≤n {x = f x} {y = f y} p
