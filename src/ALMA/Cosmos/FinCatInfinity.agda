------------------------------------------------------------------------
-- FinCat∞: colimit category Indiscrete ℕ with universal property
-- FinCat∞：余极限范畴 Indiscrete ℕ 及其泛性质
--
-- The family {FinCatN m} = {Indiscrete (Fin n_m)}, where n_m = suc (suc m),
-- has colimit Indiscrete ℕ. This module proves the universal property at
-- Set level:
--   ColimitCone X: a compatible family {g_m : Fin n_m → X} with
--     g_{suc m} ∘ inject₁ ≡ g_m
--   colimitUniv: every cone has a unique extension g∞ : ℕ → X with
--     g∞ ∘ toℕ ≡ g_m for all m
-- The construction uses natToFin k : Fin (suc (suc k)) (toℕ = k) and
-- compatibility to make the choice of m irrelevant.
-- {FinCatN m}（n_m = suc(suc m)）的余极限为 Indiscrete ℕ。
-- 本模块在 Set 层面证明泛性质：
--   ColimitCone X：相容族 {g_m}，满足 g_{suc m} ∘ inject₁ ≡ g_m
--   colimitUniv：每个锥有唯一扩展 g∞ : ℕ → X，g∞ ∘ toℕ ≡ g_m
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCatInfinity where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using ( +-suc; +-identityʳ; m+[n∸m]≡n; ≤-total )
open import Data.Fin.Base using (Fin; toℕ; inject₁)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-injective)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (LayerIdx; Tower)

FinCat∞ : Category lzero lzero lzero
FinCat∞ = Indiscrete ℕ

TrivialFC∞ : Functor FinCat∞ (ContCat lzero lzero)
TrivialFC∞ = record
  { F₀ = λ _ → record
      { Shape    = Lift lzero (⊤ {lzero})
      ; Position = λ _ → Lift lzero (⊤ {lzero})
      }
  ; F₁ = λ _ → record
      { shape    = λ _ → lift tt
      ; position = λ _ → lift tt
      }
  ; identity = record
      { shape-eq    = λ { (lift tt) → refl }
      ; position-eq = λ _ _ → refl
      }
  ; homomorphism = record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }
  ; F-resp-≈ = λ _ → record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }
  }

∞Layer : StrictLayer lzero lzero lzero lzero lzero
∞Layer = record { C = FinCat∞ ; FC = TrivialFC∞ }

∞Idx : LayerIdx
∞Idx = record { o = lzero ; h = lzero ; e = lzero ; s = lzero ; p = lzero }

∞Tower : Tower ∞Idx
∞Tower = record { layer₀ = ∞Layer }

-- Colimit universal property at Set level
-- Set 层面的余极限泛性质

-- n-at m = suc (suc m): the size of FinCatN m's object set
-- n-at m = suc (suc m)：FinCatN m 对象集的大小
n-at : ℕ → ℕ
n-at m = suc (suc m)

-- natToFin k : Fin (n-at k), the unique element with toℕ = k
-- natToFin k : Fin (n-at k)，toℕ = k 的唯一元素
natToFin : ∀ k → Fin (n-at k)
natToFin zero    = fzero
natToFin (suc k) = fsuc (natToFin k)

toℕ-natToFin : ∀ k → toℕ (natToFin k) ≡ k
toℕ-natToFin zero    = refl
toℕ-natToFin (suc k) = cong suc (toℕ-natToFin k)

-- inject₁^d d: iterated inject₁, Fin (n-at m) → Fin (n-at (m + d))
-- inject₁^d d：inject₁ 的 d 次迭代，Fin (n-at m) → Fin (n-at (m + d))
inject₁^d : ∀ d {m} → Fin (n-at m) → Fin (n-at (m + d))
inject₁^d zero    {m} x = subst Fin (cong n-at (sym (+-identityʳ m))) x
inject₁^d (suc d) {m} x =
  subst Fin (cong n-at (sym (+-suc m d))) (inject₁ (inject₁^d d x))

toℕ-subst : ∀ {n m} (eq : n ≡ m) (x : Fin n) → toℕ (subst Fin eq x) ≡ toℕ x
toℕ-subst refl x = refl

at-subst : ∀ {X : Set} (at : ∀ m → Fin (n-at m) → X)
  {m m'} (eq : m ≡ m') (z : Fin (n-at m))
  → at m' (subst Fin (cong n-at eq) z) ≡ at m z
at-subst at refl z = refl

toℕ-inject₁^d : ∀ d {m} (x : Fin (n-at m)) → toℕ (inject₁^d d x) ≡ toℕ x
toℕ-inject₁^d zero    {m} x =
  toℕ-subst (cong n-at (sym (+-identityʳ m))) x
toℕ-inject₁^d (suc d) {m} x =
  begin
    toℕ (inject₁^d (suc d) x)
      ≡⟨ toℕ-subst (cong n-at (sym (+-suc m d))) (inject₁ (inject₁^d d x)) ⟩
    toℕ (inject₁ (inject₁^d d x))
      ≡⟨ toℕ-inject₁ (inject₁^d d x) ⟩
    toℕ (inject₁^d d x)
      ≡⟨ toℕ-inject₁^d d x ⟩
    toℕ x
  ∎

-- Compatible cone: family {g_m} with g_{suc m} (inject₁ x) ≡ g_m x
-- 相容锥：族 {g_m}，满足 g_{suc m} (inject₁ x) ≡ g_m x
record ColimitCone (X : Set) : Set where
  field
    at     : ∀ m → Fin (n-at m) → X
    compat : ∀ m (x : Fin (n-at m)) → at (suc m) (inject₁ x) ≡ at m x

  compat-iter : ∀ d m (x : Fin (n-at m))
    → at (m + d) (inject₁^d d x) ≡ at m x
  compat-iter zero    m x = at-subst at (sym (+-identityʳ m)) x
  compat-iter (suc d) m x =
    begin
      at (m + suc d) (inject₁^d (suc d) x)
        ≡⟨ at-subst at (sym (+-suc m d)) (inject₁ (inject₁^d d x)) ⟩
      at (suc (m + d)) (inject₁ (inject₁^d d x))
        ≡⟨ compat (m + d) (inject₁^d d x) ⟩
      at (m + d) (inject₁^d d x)
        ≡⟨ compat-iter d m x ⟩
      at m x
    ∎
open ColimitCone

-- Value at k is independent of the chosen m
-- k 处的值与所选 m 无关
value-independent-of-m
  : ∀ {X} (cone : ColimitCone X) m (x : Fin (n-at m))
  → at cone (toℕ x) (natToFin (toℕ x)) ≡ at cone m x
value-independent-of-m {X} cone m x = go (≤-total m k)
  where
    k : ℕ
    k = toℕ x
    go : (m ≤ k) ⊎ (k ≤ m) → at cone k (natToFin k) ≡ at cone m x
    go (inj₁ m≤k) =
      let
        d : ℕ
        d = k ∸ m
        k≡m+d : k ≡ m + d
        k≡m+d = sym (m+[n∸m]≡n m≤k)
        x↑ : Fin (n-at k)
        x↑ = subst Fin (cong n-at (sym k≡m+d)) (inject₁^d d x)
        at-k-x↑ : at cone k x↑ ≡ at cone (m + d) (inject₁^d d x)
        at-k-x↑ = at-subst (at cone) (sym k≡m+d) (inject₁^d d x)
        at-md-x : at cone (m + d) (inject₁^d d x) ≡ at cone m x
        at-md-x = compat-iter cone d m x
        toℕ-x↑ : toℕ x↑ ≡ k
        toℕ-x↑ = begin
          toℕ x↑
            ≡⟨ toℕ-subst (cong n-at (sym k≡m+d)) (inject₁^d d x) ⟩
          toℕ (inject₁^d d x)
            ≡⟨ toℕ-inject₁^d d x ⟩
          k
          ∎
        x↑≡natToFin : x↑ ≡ natToFin k
        x↑≡natToFin = toℕ-injective (trans toℕ-x↑ (sym (toℕ-natToFin k)))
      in
      begin
        at cone k (natToFin k)
          ≡˘⟨ cong (at cone k) x↑≡natToFin ⟩
        at cone k x↑
          ≡⟨ at-k-x↑ ⟩
        at cone (m + d) (inject₁^d d x)
          ≡⟨ at-md-x ⟩
        at cone m x
      ∎
    go (inj₂ k≤m) =
      let
        d : ℕ
        d = m ∸ k
        m≡k+d : m ≡ k + d
        m≡k+d = sym (m+[n∸m]≡n k≤m)
        y↑ : Fin (n-at m)
        y↑ = subst Fin (cong n-at (sym m≡k+d)) (inject₁^d d (natToFin k))
        at-m-y↑ : at cone m y↑ ≡ at cone (k + d) (inject₁^d d (natToFin k))
        at-m-y↑ = at-subst (at cone) (sym m≡k+d) (inject₁^d d (natToFin k))
        at-kd-y : at cone (k + d) (inject₁^d d (natToFin k))
                ≡ at cone k (natToFin k)
        at-kd-y = compat-iter cone d k (natToFin k)
        toℕ-y↑ : toℕ y↑ ≡ k
        toℕ-y↑ = begin
          toℕ y↑
            ≡⟨ toℕ-subst (cong n-at (sym m≡k+d)) (inject₁^d d (natToFin k)) ⟩
          toℕ (inject₁^d d (natToFin k))
            ≡⟨ toℕ-inject₁^d d (natToFin k) ⟩
          toℕ (natToFin k)
            ≡⟨ toℕ-natToFin k ⟩
          k
          ∎
        y↑≡x : y↑ ≡ x
        y↑≡x = toℕ-injective (trans toℕ-y↑ refl)
      in
      begin
        at cone k (natToFin k)
          ≡˘⟨ at-kd-y ⟩
        at cone (k + d) (inject₁^d d (natToFin k))
          ≡˘⟨ at-m-y↑ ⟩
        at cone m y↑
          ≡⟨ cong (at cone m) y↑≡x ⟩
        at cone m x
      ∎

-- Universal property: every cone has a unique extension g∞ : ℕ → X
-- 泛性质：每个锥有唯一扩展 g∞ : ℕ → X
colimitUniv
  : ∀ {X : Set} (cone : ColimitCone X)
  → Σ (ℕ → X) λ g∞ →
      Σ (∀ m (x : Fin (n-at m)) → g∞ (toℕ x) ≡ at cone m x) λ _ →
      (∀ (h : ℕ → X) → (∀ m (x : Fin (n-at m)) → h (toℕ x) ≡ at cone m x)
       → ∀ k → h k ≡ g∞ k)
colimitUniv {X} cone = g∞ , (extends , unique)
  where
    g∞ : ℕ → X
    g∞ k = at cone k (natToFin k)
    extends : ∀ m (x : Fin (n-at m)) → g∞ (toℕ x) ≡ at cone m x
    extends m x = value-independent-of-m cone m x
    unique : ∀ (h : ℕ → X)
      → (∀ m (x : Fin (n-at m)) → h (toℕ x) ≡ at cone m x)
      → ∀ k → h k ≡ g∞ k
    unique h h-ext k = begin
      h k
        ≡⟨ cong h (sym (toℕ-natToFin k)) ⟩
      h (toℕ (natToFin k))
        ≡⟨ h-ext k (natToFin k) ⟩
      at cone k (natToFin k)
        ≡⟨ refl ⟩
      g∞ k
        ∎
