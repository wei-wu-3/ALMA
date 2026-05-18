{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：永恒性与不可消减性
哲学结构：基础存在形式 → 两种构造模式 → 过程同一性 → 核心存在论定理 → 唯一性定理
-}
module ALMA.Indestructibility where
open import ALMA.Prelude public
-- 基础存在形式：永恒流与持存谓词
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
record Always {A : Set} (P : A → Set) (s : Stream A) : Set where
  coinductive
  field
    head : P (Stream.head s)
    tail : Always P (Stream.tail s)
-- 构造模式一：认识论视角 —— 直接余归纳定义常量流
constStream : {A : Set} → A → Stream A
constStream a .Stream.head = a
constStream a .Stream.tail = constStream a
constStream-always-gen : ∀ {A} {P : A → Set} (a : A) → P a → Always P (constStream a)
constStream-always-gen a p .Always.head = p
constStream-always-gen a p .Always.tail = constStream-always-gen a p
-- 构造模式二：本体论视角 —— 余代数 + ana
StreamF : Set → Set → Set
StreamF A X = A × X
ana : ∀ {A X} → (X → StreamF A X) → X → Stream A
ana α x .Stream.head = proj₁ (α x)
ana α x .Stream.tail = ana α (proj₂ (α x))
-- 流等价关系（互模拟）
record _≈_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    head≈ : Stream.head s ≡ Stream.head t
    tail≈ : Stream.tail s ≈ Stream.tail t
≈-refl : ∀ {A} {s : Stream A} → s ≈ s
≈-refl ._≈_.head≈ = refl
≈-refl ._≈_.tail≈ = ≈-refl
≈-sym : ∀ {A} {s t : Stream A} → s ≈ t → t ≈ s
≈-sym s≈t ._≈_.head≈ = sym (s≈t ._≈_.head≈)
≈-sym s≈t ._≈_.tail≈ = ≈-sym (s≈t ._≈_.tail≈)
≈-trans : ∀ {A} {s t u : Stream A} → s ≈ t → t ≈ u → s ≈ u
≈-trans s≈t t≈u ._≈_.head≈ = trans (s≈t ._≈_.head≈) (t≈u ._≈_.head≈)
≈-trans s≈t t≈u ._≈_.tail≈ = ≈-trans (s≈t ._≈_.tail≈) (t≈u ._≈_.tail≈)
module _ {A : Set} (a : A) where
  private
    ≈-constStream-aux : ∀ (s : Stream A) → Always (λ x → x ≡ a) s → s ≈ constStream a
    ≈-constStream-aux s s-always-a ._≈_.head≈ = s-always-a .Always.head
    ≈-constStream-aux s s-always-a ._≈_.tail≈ = ≈-constStream-aux (Stream.tail s) (s-always-a .Always.tail)
  always-const-implies-≈-constStream :
    ∀ (s : Stream A) → Always (λ x → x ≡ a) s → s ≈ constStream a
  always-const-implies-≈-constStream = ≈-constStream-aux
module Constructions {O C : Set} (o : O) (c : C) where
  const-coalg : ⊤ → StreamF (O × C) ⊤
  const-coalg _ = ((o , c) , tt)
  const-stream-via-ana : Stream (O × C)
  const-stream-via-ana = ana const-coalg tt
  -- 余代数构造的流也完全满足恒常性
  private
    const-stream-always-element-constant : Always (λ oc → oc ≡ (o , c)) const-stream-via-ana
    const-stream-always-element-constant .Always.head = refl
    const-stream-always-element-constant .Always.tail = const-stream-always-element-constant
  const-stream-always-constant : Always (λ oc → proj₂ oc ≡ c) const-stream-via-ana
  const-stream-always-constant .Always.head = refl
  const-stream-always-constant .Always.tail = const-stream-always-constant
  private
    const-stream-always-proj₁-constant : Always (λ oc → proj₁ oc ≡ o) const-stream-via-ana
    const-stream-always-proj₁-constant .Always.head = refl
    const-stream-always-proj₁-constant .Always.tail = const-stream-always-proj₁-constant
  -- 过程同一性：两种构造模式产生的流是等价的
  const-stream-≈ : const-stream-via-ana ≈ constStream (o , c)
  const-stream-≈ = always-const-implies-≈-constStream (o , c)
    const-stream-via-ana
    const-stream-always-element-constant
open Constructions public
-- 函子结构与 ana 融合律（技术基础）
record Functor (F : Set → Set) : Set₁ where
  field
    imap : ∀ {A B} → (A → B) → F A → F B
    imap-id : ∀ {A} → imap {A} id ≡ id
    imap-comp : ∀ {A B C} {f : A → B} {g : B → C} → imap (g ∘ f) ≡ imap g ∘ imap f
instance
  StreamF-Functor : ∀ {A} → Functor (StreamF A)
  StreamF-Functor {A} = record
    { imap = λ { f (a , x) → (a , f x) }
    ; imap-id = refl
    ; imap-comp = refl
    }
private
  module AnaFusion {A : Set} where
    open Functor ⦃...⦄ using (imap)
    ana-fusion : ∀ {X Y} (α : X → StreamF A X) (β : Y → StreamF A Y) (f : X → Y) →
                 (∀ x → imap f (α x) ≡ β (f x)) →
                 ∀ x → ana α x ≈ ana β (f x)
    ana-fusion α β f comm x ._≈_.head≈ = cong proj₁ (comm x)
    ana-fusion α β f comm x ._≈_.tail≈ rewrite sym (cong proj₂ (comm x))
      = ana-fusion α β f comm (proj₂ (α x))
open AnaFusion public using (ana-fusion)
-- 核心存在论定理：不可消减性（两种等价证明）
Indestructibility-Theorem : Set₁
Indestructibility-Theorem =
  ¬ ⊥
  ×
  (∀ {A : Set} → Σ A (λ _ → ⊤) → ¬ (A → ⊥))
  ×
  (∀ (O C : Set) →
   Σ O (λ _ → ⊤) → Σ C (λ _ → ⊤) →
   Σ (Stream (O × C)) λ stream →
     Always (λ oc → proj₂ oc ≡ proj₂ (Stream.head stream)) stream)
indestructibility-proof : Indestructibility-Theorem
indestructibility-proof =
  no-ex-nihilo ,
  no-annihilation ,
  λ O C (o , _) (c , _) →
    let
      a : O × C
      a = (o , c)
      eternal-stream : Stream (O × C)
      eternal-stream = constStream a
      always-constant : Always (λ oc → proj₂ oc ≡ proj₂ (Stream.head eternal-stream)) eternal-stream
      always-constant = constStream-always-gen a refl
    in (eternal-stream , always-constant)
indestructibility-proof-via-coalgebra : Indestructibility-Theorem
indestructibility-proof-via-coalgebra =
  no-ex-nihilo ,
  no-annihilation ,
  λ O C (o , _) (c , _) →
    let
      eternal-stream : Stream (O × C)
      eternal-stream = const-stream-via-ana o c
      always-constant : Always (λ oc → proj₂ oc ≡ proj₂ (Stream.head eternal-stream)) eternal-stream
      always-constant = const-stream-always-constant o c
    in (eternal-stream , always-constant)
-- 两个证明生成的流是等价的：认识论视角与本体论视角的统一
indestructibility-proofs-equivalent :
  ∀ {O C} (o : O) (c : C) →
  proj₁ (proj₂ (proj₂ indestructibility-proof) O C (o , tt) (c , tt)) ≈
  proj₁ (proj₂ (proj₂ indestructibility-proof-via-coalgebra) O C (o , tt) (c , tt))
indestructibility-proofs-equivalent o c = ≈-sym (const-stream-≈ o c)
-- 唯一性定理：双分量皆恒常的流唯一互模拟等价于常量构造
BothComponentsConstant : ∀ {O C : Set} → O → C → Stream (O × C) → Set
BothComponentsConstant o c s =
  Always (λ oc → proj₁ oc ≡ o) s ×
  Always (λ oc → proj₂ oc ≡ c) s
both-const-implies-element-const :
  ∀ {O C : Set} (o : O) (c : C) (s : Stream (O × C)) →
  BothComponentsConstant o c s →
  Always (λ x → x ≡ (o , c)) s
both-const-implies-element-const o c s (p₁ , p₂) .Always.head =
  cong₂ _,_ (p₁ .Always.head) (p₂ .Always.head)
both-const-implies-element-const o c s (p₁ , p₂) .Always.tail =
  both-const-implies-element-const o c (Stream.tail s) (p₁ .Always.tail , p₂ .Always.tail)
both-const-implies-≈-constStream :
  ∀ {O C : Set} (o : O) (c : C) (s : Stream (O × C)) →
  BothComponentsConstant o c s →
  s ≈ constStream (o , c)
both-const-implies-≈-constStream o c s both-const =
  let
    element-const : Always (λ x → x ≡ (o , c)) s
    element-const = both-const-implies-element-const o c s both-const
  in
  always-const-implies-≈-constStream (o , c) s element-const
Indestructibility-Uniqueness : Set₁
Indestructibility-Uniqueness =
  ¬ ⊥
  ×
  (∀ {A : Set} → Σ A (λ _ → ⊤) → ¬ (A → ⊥))
  ×
  (∀ (O C : Set) →
   Σ O (λ _ → ⊤) → Σ C (λ _ → ⊤) →
   Σ O λ o →
   Σ C λ c →
   let stream = constStream (o , c)
   in
   BothComponentsConstant o c stream
   ×
   (∀ s → BothComponentsConstant o c s → s ≈ stream))
indestructibility-uniqueness-proof : Indestructibility-Uniqueness
indestructibility-uniqueness-proof =
  no-ex-nihilo ,
  no-annihilation ,
  λ O C (o , _) (c , _) →
    let
      stream : Stream (O × C)
      stream = constStream (o , c)
      P₁ : (O × C) → Set
      P₁ x = proj₁ x ≡ o
      p₁ : P₁ (o , c)
      p₁ = refl
      always-proj₁ : Always P₁ stream
      always-proj₁ = constStream-always-gen {A = O × C} {P = P₁} (o , c) p₁
      P₂ : (O × C) → Set
      P₂ x = proj₂ x ≡ c
      p₂ : P₂ (o , c)
      p₂ = refl
      always-proj₂ : Always P₂ stream
      always-proj₂ = constStream-always-gen {A = O × C} {P = P₂} (o , c) p₂
      both-const : BothComponentsConstant o c stream
      both-const = (always-proj₁ , always-proj₂)
      uniqueness : ∀ s → BothComponentsConstant o c s → s ≈ stream
      uniqueness s s-both-const =
        both-const-implies-≈-constStream o c s s-both-const
    in
    (o , c , both-const , uniqueness)
