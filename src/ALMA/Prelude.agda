{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：ALMA框架的基础逻辑与类型论根基
-- 构造性语义、前置条件与核心引理
-}
-- Agda 与 ALMA 的语义桥梁：
-- 元判断形式 Γ ⊢ t : A 的自明根基 -- 存在（抽象逻辑）
-- 类型宇宙 Set 的设定（无外全体） -- 宇宙（整体动态）
-- 闭项 t : A -- 存在者（具体形态）
-- 依赖和类型 Σ A B -- 存在量词（封装存在者及其证明）
-- 空类型 ⊥ 无闭项 -- 虚无
-- 恒等类型构造器 refl : t ≡ t -- 同一律
-- 空类型消除 ⊥-elim -- 矛盾律
-- 类型系统的自指封闭性 -- 认知循环（先验框架）
module ALMA.Prelude where
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP) public
open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_) public
open import Data.Bool.Base using (T) public
open import Data.Bool.Properties
            renaming (_≟_ to Bool-_≟_; _<?_ to Bool-_<?_; ≤-antisym to Bool-≤-antisym; <-irrefl to Bool-<-irrefl; ≤-refl to Bool-≤-refl; <-trans to Bool-<-trans; ≤-trans to Bool-≤-trans) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Fin using (Fin; zero; suc; splitAt; fromℕ; toℕ) public
            renaming (pred to Fin-pred) public
open import Data.Fin.Properties using (toℕ-injective; toℕ<n; suc-injective) public
open import Data.List using (List; []; _∷_; _++_; any; all; foldl; foldr) public
open import Data.List.Membership.Propositional using (_∈_) public
open import Data.List.Relation.Unary.Any using (here; there) public
open import Data.Maybe using (Maybe; just; nothing; map; maybe) public
open import Data.Nat using (ℕ; _≤_; zero; suc; s≤s; z≤n; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _<_; _>_; _≯_; _<?_; _>?_; _≟_) public
            renaming (pred to Nat-pred) public
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≮⇒≥; +-assoc; +-∸-assoc; +-comm; +-identityˡ; +-identityʳ; ≡-irrelevant; m≤n+m; m≤n⇒m≤1+n; m≤n⇒m∸n≡0; +-mono-<; +-mono-≤; ≤-pred; +-suc)
            renaming (_≟_ to Nat-_≟_; _<?_ to Nat-_<?_; ≤-antisym to Nat-≤-antisym; <-irrefl to Nat-<-irrefl; ≤-refl to Nat-≤-refl; <-trans to Nat-<-trans; ≤-trans to Nat-≤-trans) public
open import Data.Product using (Σ; _,_; Σ-syntax; _×_; ∃; ∃-syntax; proj₁; proj₂) public
open import Data.Product.Properties using (≡-dec; ,-injective) public
open import Data.String using (String) public
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]) public
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective) public
open import Data.Unit using (⊤; tt) public
open import Data.Unit.Properties
            renaming (_≟_ to Unit-_≟_; ≡-antisym to Unit-≡-antisym; ≡-decSetoid to Unit-≡-decSetoid; ≡-setoid to Unit-≡-setoid) public
open import Function using (_↔_) public
open import Function.Base using (id; _∘_; case_of_) public
open import Relation.Binary.PropositionalEquality using (_≡_; [_]; refl; _≢_; cong; cong₂; inspect; isPropositional; J; subst; sym; trans) public
open Relation.Binary.PropositionalEquality.≡-Reasoning public
open import Relation.Binary.PropositionalEquality.Properties public
open import Relation.Nullary using (Dec; yes; no; ¬_; contradiction) public
open import Relation.Nullary.Decidable using (⌊_⌋; does; False; isYes; toWitness; toWitnessFalse; True) public
-- 引理1：不可无中生有
no-ex-nihilo : ¬ ⊥
no-ex-nihilo ()
-- 引理2：不可归于虚无
no-annihilation : ∀ {A : Set} → Σ A (λ _ → ⊤) → ¬ (A → ⊥)
no-annihilation (a , _) f = f a
-- 单位类型
⊤-isProp : ∀ (x y : ⊤) → x ≡ y
⊤-isProp tt tt = refl
-- 自然数基本性质
private
  isZero : ℕ → Set
  isZero zero    = ⊤
  isZero (suc _) = ⊥
zero≢suc : ∀ {n : ℕ} → 0 ≢ suc n
zero≢suc eq = subst isZero eq tt
suc≢zero : ∀ {n : ℕ} → suc n ≢ 0
suc≢zero = zero≢suc ∘ sym
suc≤0→⊥ : ∀ {n} → suc n ≤ 0 → ⊥
suc≤0→⊥ ()
suc≤n→⊥ : ∀ {n} → suc n ≤ n → ⊥
suc≤n→⊥ {zero} ()
suc≤n→⊥ {suc n} p = suc≤n→⊥ (≤-pred p)
suc≤→≤ : ∀ {m n} → suc m ≤ n → m ≤ n
suc≤→≤ p = Nat-≤-trans (m≤n⇒m≤1+n Nat-≤-refl) p
¬zero→suc : ∀ {i} → i ≢ 0 → i > 0
¬zero→suc {zero} ¬0 = ⊥-elim (¬0 refl)
¬zero→suc {suc _} _ = s≤s z≤n
m≤n→n≡m+n∸m : ∀ {m n} → m ≤ n → n ≡ m + (n ∸ m)
m≤n→n≡m+n∸m {zero} {n} _ = sym (+-identityˡ n)
m≤n→n≡m+n∸m {suc m} {suc n} p = cong suc (m≤n→n≡m+n∸m (≤-pred p))
+-∸-cancelˡ : ∀ m n → (m + n) ∸ m ≡ n
+-∸-cancelˡ zero n = refl
+-∸-cancelˡ (suc m) n = +-∸-cancelˡ m n
my-≡⇒≡ᵇ : ∀ m n → m ≡ n → (m ≡ᵇ n) ≡ true
my-≡⇒≡ᵇ zero zero _ = refl
my-≡⇒≡ᵇ zero (suc n) p = ⊥-elim (zero≢suc p)
my-≡⇒≡ᵇ (suc m) zero p = ⊥-elim (suc≢zero p)
my-≡⇒≡ᵇ (suc m) (suc n) p = my-≡⇒≡ᵇ m n (cong Nat-pred p)
my-≡ᵇ⇒≡ : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
my-≡ᵇ⇒≡ zero zero _ = refl
my-≡ᵇ⇒≡ (suc m) (suc n) p = cong suc (my-≡ᵇ⇒≡ m n p)
my-<⇒<ᵇ : ∀ {m n : ℕ} → m < n → (m <ᵇ n) ≡ true
my-<⇒<ᵇ {zero} {suc n} _ = refl
my-<⇒<ᵇ {suc m} {suc n} p = my-<⇒<ᵇ (≤-pred p)
my-<ᵇ⇒< : ∀ {m n : ℕ} → (m <ᵇ n) ≡ true → m < n
my-<ᵇ⇒< {zero} {suc n} _ = s≤s z≤n
my-<ᵇ⇒< {suc m} {suc n} p = s≤s (my-<ᵇ⇒< p)
0<ᵇn≡false : ∀ n → (n <ᵇ 0) ≡ false
0<ᵇn≡false zero = refl
0<ᵇn≡false (suc n) = refl
Fin-zero≢suc : ∀ {n : ℕ} {i : Fin n} → Fin.zero ≢ Fin.suc i
Fin-zero≢suc eq = zero≢suc (cong toℕ eq)
Fin-suc≢zero : ∀ {n : ℕ} {i : Fin n} → Fin.suc i ≢ Fin.zero
Fin-suc≢zero = Fin-zero≢suc ∘ sym
fin1-unique : ∀ (i : Fin 1) → i ≡ zero
fin1-unique i = toℕ-injective (Nat-≤-antisym (≤-pred (toℕ<n i)) z≤n)
true≢false : true ≢ false
true≢false eq = subst (λ { true → ⊤ ; false → ⊥ }) eq tt
false≢true : false ≢ true
false≢true = true≢false ∘ sym
private
  isInj₁ : ∀ {A B : Set} → A ⊎ B → Set
  isInj₁ (inj₁ _) = ⊤
  isInj₁ (inj₂ _) = ⊥
inj₁≢inj₂ : ∀ {A B : Set} {a : A} {b : B} → inj₁ a ≢ inj₂ b
inj₁≢inj₂ eq = subst isInj₁ eq tt
inj₂≢inj₁ : ∀ {A B : Set} {a : A} {b : B} → inj₂ b ≢ inj₁ a
inj₂≢inj₁ = inj₁≢inj₂ ∘ sym
-- 通用组合子
iter : ∀ {A : Set} → ℕ → (A → A) → A → A
iter zero f x = x
iter (suc n) f x = f (iter n f x)
if-≡ : ∀ {A : Set} (b : Bool)
     → (b ≡ true → A)
     → (b ≡ false → A)
     → A
if-≡ true  t f = t refl
if-≡ false t f = f refl
