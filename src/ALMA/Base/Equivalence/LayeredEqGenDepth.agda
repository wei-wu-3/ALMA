------------------------------------------------------------------------
-- depth-bounded truncation of LayeredEqGen
-- LayeredEqGen is coinductive and therefore infinite. This module
-- provides its finite truncation at every depth n, together with the
-- projection from the infinite relation and monotonicity in n. The
-- truncation gives a finite induction-compatible predicate: any
-- coinductive proof projects to it at every depth, so downstream
-- proofs can reason by induction on n rather than by guarded
-- coinduction
--
-- LayeredEqGen 的深度有界截断
-- LayeredEqGen 是余归纳的，因此是无穷的。本模块给出它在每个深度 n
-- 处的有限截断，以及从无穷关系到截断的投影和截断在 n 上的单调性
-- 该截断给出一个有限归纳相容的谓词：任何余归纳证明在每一深度上都
-- 投影到它，因此下游证明可对 n 作归纳，而不必使用受守卫的余归纳
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.LayeredEqGenDepth where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)

open import ALMA.Base.IndexedMType using (fst; snd)
open import ALMA.Base.Equivalence.Core using (LayeredEqGen)

------------------------------------------------------------------------
-- Finite truncation of LayeredEqGen
-- Since obs-map is a function (not an equality), no subst is needed
-- in the recursive case: the target-side observation is obtained by
-- applying obs-map directly
--
-- LayeredEqGen 的有限截断
-- 由于 obs-map 是函数（而非等式），递归情形不需要 subst：
-- 目标侧观察由 obs-map 直接给出
module LayeredEqGen-Depth
    {a b c} {X : Set a}
    {Obs : X → Set b}
    {step : (x : X) → Obs x → X}
    {layer : X → X → Set c}
    {obs-map : (x y : X) → layer x y → Obs x → Obs y} where

  -- Depth-bounded truncation
  --
  -- 深度有界截断
  LE-depth : (n : ℕ) → (x y : X) → Set (a ⊔ b ⊔ c)
  LE-depth zero    x y = ⊤
  LE-depth (suc n) x y =
    Σ (layer x y) (λ l →
      ∀ (s : Obs x) → LE-depth n
        (step x s)
        (step y (obs-map x y l s)))

  -- Every coinductive proof yields a depth-bounded truncation
  --
  -- 每个余归纳证明都给出深度有界截断
  le→LE-depth : ∀ {x y} → LayeredEqGen Obs step layer obs-map x y
              → ∀ n → LE-depth n x y
  le→LE-depth p zero    = tt
  le→LE-depth p (suc n) =
    ( p .fst
    , λ s → le→LE-depth (p .snd s) n )

  -- Monotonicity in depth
  --
  -- 深度单调性
  LE-depth-mono : ∀ {m n} (m≤n : m ≤ n) {x y : X}
                → LE-depth n x y → LE-depth m x y
  LE-depth-mono z≤n       p = tt
  LE-depth-mono (s≤s m≤n) p =
    ( proj₁ p
    , λ s → LE-depth-mono m≤n (proj₂ p s) )
