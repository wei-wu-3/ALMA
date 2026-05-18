{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：非均匀性与内在差异
哲学意义：本质恒常的存在者整体中，偶性必然呈现非均匀变化
-}
module ALMA.Inhomogeneity where
open import ALMA.Cosmos public
open Stream public
open Always public
cos-observe : Cosmos → ℕ → ℕ → ℕ
cos-observe = observeAccident {ℕ} {ℕ} {Cosmos-C}
-- 宇宙层面的同质与变化
module CosmosLevel where
  WeakHom-Cosmos : Cosmos → Set
  WeakHom-Cosmos cos = ∀ n m i → cos-observe cos n i ≡ cos-observe cos m i
  Changes-Cosmos : Cosmos → Set
  Changes-Cosmos cos = ∃ λ n → ∃ λ i → cos-observe cos n i ≢ cos-observe cos (suc n) i
private
  obsS : ∀ {O C} → Stream (O × C) → ℕ → O
  obsS s n = proj₁ (head (stream-tail-n s n))
WeakHomS : ∀ {O C} → Stream (O × C) → Set
WeakHomS s = ∀ n m → obsS s n ≡ obsS s m
ChangesS : ∀ {O C} → Stream (O × C) → Set
ChangesS s = ∃ λ n → obsS s n ≢ obsS s (suc n)
ΔS : ∀ {O C} → Stream (O × C) → Set
ΔS s = ∃ λ n → ∃ λ m → obsS s n ≢ obsS s m
Generator : (O C : Set) → Set₁
Generator O C = Σ Set (λ S → S × (S → (O × C) × S))
genStream : ∀ {O C} → Generator O C → Stream (O × C)
genStream (S , init , step) = ana step init
WeakHomG : ∀ {O C} → Generator O C → Set
WeakHomG g = WeakHomS (genStream g)
ChangesG : ∀ {O C} → Generator O C → Set
ChangesG g = ChangesS (genStream g)
module _ {O C : Set} where
  const-output→WeakHomG : (S : Set) (init : S) (step : S → (O × C) × S)
    → (∀ s → proj₁ (step s) ≡ proj₁ (step init))
    → WeakHomG (S , init , step)
  const-output→WeakHomG S init step const-out = weak
    where
    o₀ = proj₁ (proj₁ (step init))
    lemma : (s : S) → ∀ n → proj₁ (head (stream-tail-n (ana step s) n)) ≡ o₀
    lemma s zero    = cong proj₁ (const-out s)
    lemma s (suc n) = lemma (proj₂ (step s)) n
    weak : WeakHomS (ana step init)
    weak n m = trans (lemma init n) (sym (lemma init m))
WeakHomCoind : ∀ {O C} → Stream (O × C) → Set
WeakHomCoind s = s ≈ constStream (head s)
coind-const→all-heads : ∀ {O C} {s : Stream (O × C)} {a : O × C}
                      → s ≈ constStream a
                      → ∀ n → head (stream-tail-n s n) ≡ a
coind-const→all-heads eq zero    = _≈_.head≈ eq
coind-const→all-heads eq (suc n) = coind-const→all-heads (_≈_.tail≈ eq) n
coind→pointwise : ∀ {O C} (s : Stream (O × C)) → WeakHomCoind s
                → ∀ n → head (stream-tail-n s n) ≡ head s
coind→pointwise s coind = coind-const→all-heads coind
LocalChangeCosmos : ℕ → Cosmos → Set
LocalChangeCosmos d cos = ∃ λ n → ∃ λ m → cos-observe cos n d ≢ cos-observe cos m d
GlobalChangeCosmos : Cosmos → Set
GlobalChangeCosmos cos = ∀ d → LocalChangeCosmos d cos
FrequentChangeCosmos : Cosmos → Set
FrequentChangeCosmos cos =
  ∀ n → ∃ λ m → n ≤ m × (∃ λ d → cos-observe cos m d ≢ cos-observe cos (suc m) d)
PeriodicCosmos : ℕ → Cosmos → Set
PeriodicCosmos k cos = ∀ n i → cos-observe cos n i ≡ cos-observe cos (n + k) i
open CosmosLevel
weakHomCosmos→¬localChange : ∀ cos → WeakHom-Cosmos cos → ∀ d → ¬ LocalChangeCosmos d cos
weakHomCosmos→¬localChange cos w d (n , m , neq) = neq (w n m d)
HomS : ∀ {O C : Set} → Stream (O × C) → Set
HomS {O} {C} s = ∀ (t : Stream (O × C)) n m → obsS s n ≡ obsS t m
homS→weakHomS : ∀ {O C} {s : Stream (O × C)} → HomS s → WeakHomS s
homS→weakHomS {s = s} hom n m = hom s n m
altGen : (C : Set) → C → Generator Bool C
altGen C c = Bool , true , step
  where
  step : Bool → (Bool × C) × Bool
  step b = ((b , c) , not b)
altGen-changes : ∀ {C} (c : C) → ChangesS (genStream (altGen _ c))
altGen-changes c = 0 , λ eq → true≢false eq
no-possible-hom : ∀ {C} (c : C) → ¬ (∃ λ (g : Generator Bool C) → HomS (genStream g))
no-possible-hom {C} c (g , hom) =
  let
    altStream = genStream (altGen _ c)
    (n , neq) = altGen-changes c
    eq1 : obsS (genStream g) n ≡ obsS altStream n
    eq1 = hom altStream n n
    eq2 : obsS (genStream g) n ≡ obsS altStream (suc n)
    eq2 = hom altStream n (suc n)
    eq : obsS altStream n ≡ obsS altStream (suc n)
    eq = trans (sym eq1) eq2
  in neq eq
WeakHom : ∀ {O C} → Process O C → Set
WeakHom p = WeakHomS (stream p)
Changes : ∀ {O C} → Process O C → Set
Changes p = ChangesS (stream p)
Δ : ∀ {O C} → Process O C → Set
Δ p = ΔS (stream p)
IntrinsicDifference = Δ
IntrinsicBoundary   = Δ
SelfSubstantialBeing = Δ
lemma-WeakHom→¬Changes : ∀ {O C} (p : Process O C) → WeakHom p → ¬ Changes p
lemma-WeakHom→¬Changes p weak (n , neq) = neq (weak n (suc n))
lemma-WeakHom→¬Boundary : ∀ {O C} (p : Process O C) → WeakHom p → ¬ IntrinsicBoundary p
lemma-WeakHom→¬Boundary p weak (n , m , neq) = neq (weak n m)
lemma-WeakHom→¬SelfSubstantial : ∀ {O C} (p : Process O C) → WeakHom p → ¬ SelfSubstantialBeing p
lemma-WeakHom→¬SelfSubstantial = lemma-WeakHom→¬Boundary
lemma-SelfSubstantial→¬WeakHom : ∀ {O C} (p : Process O C) → SelfSubstantialBeing p → ¬ WeakHom p
lemma-SelfSubstantial→¬WeakHom p delta weak = lemma-WeakHom→¬Boundary p weak delta
Hom : ∀ {O C} → Process O C → Set
Hom {O} {C} p = ∀ (q : Process O C) n m → observe p n ≡ observe q m
hom→weakHom : ∀ {O C} (p : Process O C) → Hom p → WeakHom p
hom→weakHom p hom-p n m = hom-p p n m
thm-Hom→¬Changes : ∀ {O C} (p : Process O C) → Hom p → ¬ Changes p
thm-Hom→¬Changes p hom = lemma-WeakHom→¬Changes p (hom→weakHom p hom)
thm-Hom→¬Boundary : ∀ {O C} (p : Process O C) → Hom p → ¬ IntrinsicBoundary p
thm-Hom→¬Boundary p hom = lemma-WeakHom→¬Boundary p (hom→weakHom p hom)
thm-no-Hom-if-any-change :
  ∀ {O C} (FB : Process O C) → Changes FB → ¬ (∃ λ (p : Process O C) → Hom p)
thm-no-Hom-if-any-change FB (n , neq) (p , hom-p) =
  neq (trans (sym (hom-p FB n n)) (hom-p FB n (suc n)))
-- 非均匀性必然：只要存在一个变化过程，就没有绝对同质的观察者
nonuniformity-inevitable :
  ∀ {O C} (FB : Process O C) → Changes FB → (∀ p → ¬ Hom p)
nonuniformity-inevitable FB changes p hom-p =
  thm-no-Hom-if-any-change FB changes (p , hom-p)
module WithFact
  {O C : Set}
  (FB : Process O C)
  (fact-FB-changes : Changes FB)
  where
  concrete-nonuniformity : ∀ p → ¬ Hom p
  concrete-nonuniformity = nonuniformity-inevitable FB fact-FB-changes
lemma-Hom-Cosmos→¬Changes-Cosmos : (cos : Cosmos) → WeakHom-Cosmos cos → ¬ Changes-Cosmos cos
lemma-Hom-Cosmos→¬Changes-Cosmos cos hom (n , i , neq) = neq (hom n (suc n) i)
