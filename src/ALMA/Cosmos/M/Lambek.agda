------------------------------------------------------------------------
-- Lambek's lemma for the terminal M-Cosmos, up to bisimulation.
--
-- M-base replacement for the legacy Cosmos/Lambek.agda.  In the legacy
-- seed-threaded presentation the structure map out : Cosmos → Unfolding
-- Cosmos is a weak isomorphism: an inverse in-F must be CONSTRUCTED from
-- the terminal universal property, and the two round-trips
-- in-F ∘ out ≈C id and out ∘ in-F ≈F id are proved through the subst-based
-- _≈C_ / _≈U_ machinery.
--
-- In M the self-reference is native: there is no separate Unfolding seed
-- type.  The structure map is the observation coalgebra unfold-coalgebra
-- (label = M.here, child = step), and its inverse "re-tupling" is simply
-- ana of that observation coalgebra.  Hence Lambek's two round-trips are
-- EXACTLY the eta pair already established in Cosmos/M/Object:
--
--   in-F ∘ out ≈ id   :=   ana unfold-coalgebra t  ≈CosmosM  t   (ana-unfold)
--   out ∘ in-F ≈ id   :=   t                        ≈CosmosM  ana unfold-coalgebra t
--                                                                 (ana-unfold˘)
--
-- No inverse has to be synthesised and no transport is used: native
-- guarded coinduction collapses Lambek's lemma to terminality eta.
--
-- 终 M-Cosmos 的 Lambek 引理（互模拟意义下）。
--
-- 旧 Cosmos/Lambek.agda 的 M 底座替代。在旧的经种子绕行表述中，结构映
-- 射 out : Cosmos → Unfolding Cosmos 是弱同构：必须由终对象泛性质构造
-- 逆 in-F，两条往返 in-F ∘ out ≈C id、out ∘ in-F ≈F id 经基于 subst 的
-- _≈C_ / _≈U_ 机器证明。
--
-- 在 M 中自指是内建的：不存在独立的 Unfolding 种子类型。结构映射即观
-- 察余代数 unfold-coalgebra（label = M.here，child = step），其逆“重
-- 新组元”不过是对该观察余代数取 ana。故 Lambek 的两条往返恰是
-- Cosmos/M/Object 中已证的 eta 对：
--
--   in-F ∘ out ≈ id  :=  ana unfold-coalgebra t  ≈CosmosM  t  （ana-unfold）
--   out ∘ in-F ≈ id  :=  t                        ≈CosmosM  ana unfold-coalgebra t
--                                                                （ana-unfold˘）
--
-- 无需综合逆映射，也不用任何传输：内建受保护余归纳把 Lambek 引理直接
-- 坍缩为终性 eta。
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

    -- in-F ∘ out ≈ id: re-tupling the one-step observation of a node
    -- rebuilds a bisimilar node.  This is ana-unfold.
    --
    -- in-F ∘ out ≈ id：对节点的一步观察重新组元，重建出互模拟的节
    -- 点。即 ana-unfold。
    lambek-in∘out : ∀ {i : MO.I C FC} (t : MO.CosmosM C FC i)
                  → MO.≈CosmosM C FC ≈CD
                      (MO.ana C FC (MO.unfold-coalgebra C FC) i t) t
    lambek-in∘out t = MO.ana-unfold C FC ≈CD t

    -- out ∘ in-F ≈ id: a node is bisimilar to the re-tupling of its
    -- observation.  This is ana-unfold˘.
    --
    -- out ∘ in-F ≈ id：节点与其观察的重新组元互模拟。即 ana-unfold˘。
    lambek-out∘in : ∀ {i : MO.I C FC} (t : MO.CosmosM C FC i)
                  → MO.≈CosmosM C FC ≈CD
                      t (MO.ana C FC (MO.unfold-coalgebra C FC) i t)
    lambek-out∘in t = MO.ana-unfold˘ C FC ≈CD t
