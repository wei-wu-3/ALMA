------------------------------------------------------------------------
-- Coinductive indexed M-type
--
-- Mᵢ is the coinductive skeleton underlying LayeredEqGen and
-- IndexedLayeredEq: an index i carries a first component fst : A i and
-- a guarded continuation snd that advances the index via next. The
-- non-indexed M is the specialization to the terminal index type ⊤.
--
-- 余归纳索引 M 型
--
-- Mᵢ 是 LayeredEqGen 与 IndexedLayeredEq 背后的余归纳骨架：索引 i
-- 携带首分量 fst : A i，以及经 next 推进索引的受守卫延续 snd。
-- 无索引的 M 是取终止索引类型 ⊤ 的特化。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.IndexedMType where

open import Agda.Primitive using (_⊔_; lzero)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

record Mᵢ {i a b} {I : Set i}
          (A : I → Set a)
          (B : (i : I) (a : A i) → Set b)
          (next : (i : I) (a : A i) (p : B i a) → I)
          (i : I) : Set (a ⊔ b) where
  coinductive
  field
    fst : A i
    snd : (p : B i fst) → Mᵢ A B next (next i fst p)

open Mᵢ public

------------------------------------------------------------------------
-- Non-indexed specialization at I = ⊤
--
-- 取 I = ⊤ 的无索引特化

M : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
M A B = Mᵢ {i = lzero} {I = ⊤} (λ _ → A) (λ _ x → B x) (λ _ _ _ → tt) tt
