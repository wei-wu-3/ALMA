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

M : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
M A B = Mᵢ {i = lzero} {I = ⊤} (λ _ → A) (λ _ x → B x) (λ _ _ _ → tt) tt
