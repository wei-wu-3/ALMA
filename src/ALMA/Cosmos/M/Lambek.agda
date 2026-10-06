------------------------------------------------------------------------
-- Lambek's lemma for the terminal M-Cosmos, up to bisimulation. In M
-- the self-reference is native (no separate Unfolding seed type): the
-- structure map is the observation coalgebra unfold-coalgebra (label =
-- M.here, child = step), and its inverse is simply ana of that
-- observation coalgebra. The two round-trips are therefore exactly the
-- eta pair already established in Cosmos/M/Object:
--   in-F ∘ out ≈ id   :=   ana-unfold
--   out ∘ in-F ≈ id   :=   ana-unfold˘
-- No inverse is synthesised and no transport is used.
--
-- 终 M-Cosmos 的 Lambek 引理（互模拟意义下）。在 M 中自指是内建的（无
-- 独立 Unfolding 种子类型）：结构映射即观察余代数 unfold-coalgebra
-- （label = M.here，child = step），其逆不过是对该观察余代数取 ana。
-- 两条往返恰是 Cosmos/M/Object 中已证的 eta 对：
--   in-F ∘ out ≈ id   :=   ana-unfold
--   out ∘ in-F ≈ id   :=   ana-unfold˘
-- 无需综合逆映射，也不用任何传输。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.Lambek where

open import Agda.Primitive using (Level)
open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid using (EqOn)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)} where

  module _ {ℓd : Level}
           (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i)) where

    -- in-F ∘ out ≈ id: ana-unfold.
    -- in-F ∘ out ≈ id：ana-unfold。
    lambek-in∘out : ∀ {i : MO.I C FC} (t : MO.CosmosM C FC i)
                  → MO.≈CosmosM C FC ≈CD
                      (MO.ana C FC (MO.unfold-coalgebra C FC) i t) t
    lambek-in∘out t = MO.ana-unfold C FC ≈CD t

    -- out ∘ in-F ≈ id: ana-unfold˘.
    -- out ∘ in-F ≈ id：ana-unfold˘。
    lambek-out∘in : ∀ {i : MO.I C FC} (t : MO.CosmosM C FC i)
                  → MO.≈CosmosM C FC ≈CD
                      t (MO.ana C FC (MO.unfold-coalgebra C FC) i t)
    lambek-out∘in t = MO.ana-unfold˘ C FC ≈CD t
