{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：过程及其张量积范畴结构
哲学意义：将不可消减性原理应用于动态存在者，定义其基本结构与复合方式
-}
module ALMA.Core where
open import ALMA.Indestructibility public
comb : ∀ {O₁ C₁ O₂ C₂ : Set} → (O₁ → O₂) → (C₁ → C₂) → (O₁ × C₁) → (O₂ × C₂)
comb f-O f-C (o , c) = (f-O o , f-C c)
-- 过程：动态存在者的基本结构（O：偶性，C：本质）
record Process (O C : Set) : Set where
  constructor mkProc
  field
    o               : O
    c               : C
    stream          : Stream (O × C)
    essence-const   : Always (λ x → proj₂ x ≡ c) stream
    init-consistent : proj₁ (Stream.head stream) ≡ o
open Process public
core : ∀ {O C : Set} → Process O C → C
core = c
-- 过程等价：流互模拟
_≈ₚ_ : ∀ {O C : Set} → Process O C → Process O C → Set
_≈ₚ_ p q = stream p ≈ stream q
≈ₚ-refl  : ∀ {O C : Set} {p : Process O C} → p ≈ₚ p
≈ₚ-refl = ≈-refl
≈ₚ-sym   : ∀ {O C : Set} {p q : Process O C} → p ≈ₚ q → q ≈ₚ p
≈ₚ-sym = ≈-sym
≈ₚ-trans : ∀ {O C : Set} {p q r : Process O C} → p ≈ₚ q → q ≈ₚ r → p ≈ₚ r
≈ₚ-trans = ≈-trans
-- 标准过程构造（认识论视角：直接余归纳）
mkStandardProcess : ∀ (O C : Set) → O → C → Process O C
mkStandardProcess O C o c = mkProc o c standard-stream standard-essence-const refl
  where
    standard-stream : Stream (O × C)
    standard-stream = constStream (o , c)
    standard-essence-const : Always (λ x → proj₂ x ≡ c) standard-stream
    standard-essence-const = constStream-always-gen (o , c) refl
-- 标准过程构造（本体论视角：余代数式）
mkProcessViaAna : ∀ (O C : Set) → O → C → Process O C
mkProcessViaAna O C o c = mkProc o c ana-stream ana-essence-const refl
  where
    ana-stream : Stream (O × C)
    ana-stream = ana (const-coalg o c) tt
    ana-essence-const : Always (λ x → proj₂ x ≡ c) ana-stream
    ana-essence-const = const-stream-always-constant o c
-- 认识论与本体论的统一
standard-processes-equivalent : ∀ {O C : Set} (o : O) (c : C) →
  mkStandardProcess O C o c ≈ₚ mkProcessViaAna O C o c
standard-processes-equivalent o c = ≈-sym (const-stream-≈ o c)
-- 有限观察与本质守恒
stream-tail-n : ∀ {A : Set} → Stream A → ℕ → Stream A
stream-tail-n s zero    = s
stream-tail-n s (suc n) = stream-tail-n (Stream.tail s) n
always-implies-all-n : ∀ {A : Set} {P : A → Set} {s : Stream A} →
                       Always P s → ∀ (n : ℕ) → P (Stream.head (stream-tail-n s n))
always-implies-all-n alws zero    = Always.head alws
always-implies-all-n alws (suc n) = always-implies-all-n (Always.tail alws) n
observe : ∀ {O C : Set} → Process O C → ℕ → O
observe p n = proj₁ (Stream.head (stream-tail-n (stream p) n))
next : ∀ {O C : Set} → Process O C → Process O C
next p = mkProc o' (c p) stream' essence-const' init-consistent'
  where
    stream' = Stream.tail (stream p)
    o' = proj₁ (Stream.head stream')
    essence-const' = Always.tail (essence-const p)
    init-consistent' = refl
c-conservation : ∀ {O C : Set} (p : Process O C) → core (next p) ≡ core p
c-conservation p = refl
global-c-constancy : ∀ {O C : Set} (p : Process O C) (n : ℕ) →
                     proj₂ (Stream.head (stream-tail-n (stream p) n)) ≡ core p
global-c-constancy p n = always-implies-all-n (essence-const p) n
next-preserves-constancy : ∀ {O C : Set} (p : Process O C) → 
                            Always (λ x → proj₂ x ≡ core (next p)) (stream (next p))
next-preserves-constancy p = Always.tail (essence-const p)
core-preserves-≈ₚ : ∀ {O C : Set} {p q : Process O C} → p ≈ₚ q → core p ≡ core q
core-preserves-≈ₚ {p = p} {q = q} p≈q =
  let
    h₁ : proj₂ (Stream.head (stream p)) ≡ c p
    h₁ = always-implies-all-n (essence-const p) 0
    h₂ : proj₂ (Stream.head (stream q)) ≡ c q
    h₂ = always-implies-all-n (essence-const q) 0
    eq-head : Stream.head (stream p) ≡ Stream.head (stream q)
    eq-head = _≈_.head≈ p≈q
    eq-proj₂ : proj₂ (Stream.head (stream p)) ≡ proj₂ (Stream.head (stream q))
    eq-proj₂ = cong proj₂ eq-head
  in trans (sym h₁) (trans eq-proj₂ h₂)
observe-preserves-≈ₚ : ∀ {O C : Set} (p q : Process O C) (n : ℕ) →
                        p ≈ₚ q → observe p n ≡ observe q n
observe-preserves-≈ₚ p q n p≈q = aux-observe (stream p) (stream q) p≈q n
  where
    aux-observe : ∀ {O C : Set} (s1 s2 : Stream (O × C)) (e : s1 ≈ s2) (n : ℕ) →
                  proj₁ (Stream.head (stream-tail-n s1 n)) ≡ proj₁ (Stream.head (stream-tail-n s2 n))
    aux-observe s1 s2 e zero    = cong proj₁ (_≈_.head≈ e)
    aux-observe s1 s2 e (suc n) = aux-observe (Stream.tail s1) (Stream.tail s2) (_≈_.tail≈ e) n
next-preserves-≈ₚ : ∀ {O C : Set} {p q : Process O C} → p ≈ₚ q → next p ≈ₚ next q
next-preserves-≈ₚ p≈q = _≈_.tail≈ p≈q
-- 形态重构：偶性可变，本质不变
AccidentalReconfiguration : ∀ {O C : Set} → Process O C → Set
AccidentalReconfiguration p =
  (∀ (n : ℕ) → proj₂ (Stream.head (stream-tail-n (stream p) n)) ≡ core p)
  × (Σ ℕ λ (n : ℕ) → observe p n ≢ observe p (suc n))
reconfiguration-theorem :
  ∀ {O C : Set} (p : Process O C)
  → (Σ ℕ λ (n : ℕ) → observe p n ≢ observe p (suc n))
  → AccidentalReconfiguration p
reconfiguration-theorem p morph-change =
  (global-c-constancy p , morph-change)
reconfiguration-preserves-core : ∀ {O C : Set} (p : Process O C) →
  AccidentalReconfiguration p → core (next p) ≡ core p
reconfiguration-preserves-core p _ = c-conservation p
-- 交替过程示例
mkAlternatingProcess : ∀ (C : Set) → C → Process Bool C
mkAlternatingProcess C c₀ = mkProc true c₀ alt-stream alt-essence-const refl
  where
    alt-stream : Stream (Bool × C)
    alt-stream .Stream.head = (true , c₀)
    alt-stream .Stream.tail = alt-step
      where
        alt-step : Stream (Bool × C)
        alt-step .Stream.head = (false , c₀)
        alt-step .Stream.tail = alt-stream
    alt-essence-const : Always (λ x → proj₂ x ≡ c₀) alt-stream
    alt-essence-const .Always.head = refl
    alt-essence-const .Always.tail = alt-step-const
      where
        alt-step-const : Always (λ x → proj₂ x ≡ c₀) (Stream.tail alt-stream)
        alt-step-const .Always.head = refl
        alt-step-const .Always.tail = alt-essence-const
-- 张量积：过程的并行复合
merge-state : ∀ {O₁ C₁ O₂ C₂ : Set} → (O₁ × C₁) → (O₂ × C₂) → ((O₁ × O₂) × (C₁ × C₂))
merge-state (o1 , c1) (o2 , c2) = ((o1 , o2) , (c1 , c2))
merge-stream : ∀ {O₁ C₁ O₂ C₂ : Set} → Stream (O₁ × C₁) → Stream (O₂ × C₂) → Stream ((O₁ × O₂) × (C₁ × C₂))
merge-stream s₁ s₂ .Stream.head = merge-state (Stream.head s₁) (Stream.head s₂)
merge-stream s₁ s₂ .Stream.tail = merge-stream (Stream.tail s₁) (Stream.tail s₂)
private
  merge-const-lemma : ∀ {O₁ C₁ O₂ C₂ : Set} (a : O₁ × C₁) (b : O₂ × C₂) →
    merge-stream (constStream a) (constStream b) ≈ constStream (merge-state a b)
  merge-const-lemma a b ._≈_.head≈ = refl
  merge-const-lemma a b ._≈_.tail≈ = merge-const-lemma a b
_⊗_ : ∀ {O₁ C₁ O₂ C₂ : Set} → Process O₁ C₁ → Process O₂ C₂ → Process (O₁ × O₂) (C₁ × C₂)
_⊗_ {O₁} {C₁} {O₂} {C₂} p₁ p₂ = mkProc (o p₁ , o p₂) (c p₁ , c p₂) combined-stream combined-const combined-init
  where
    combined-stream : Stream ((O₁ × O₂) × (C₁ × C₂))
    combined-stream = merge-stream (stream p₁) (stream p₂)
    merge-always : (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂))
                   (alw₁ : Always (λ x → proj₂ x ≡ c p₁) s₁)
                   (alw₂ : Always (λ x → proj₂ x ≡ c p₂) s₂)
                   → Always (λ x → proj₂ x ≡ (c p₁ , c p₂)) (merge-stream s₁ s₂)
    merge-always s₁ s₂ alw₁ alw₂ .Always.head = cong₂ _,_ (Always.head alw₁) (Always.head alw₂)
    merge-always s₁ s₂ alw₁ alw₂ .Always.tail = merge-always (Stream.tail s₁) (Stream.tail s₂) (Always.tail alw₁) (Always.tail alw₂)
    combined-const : Always (λ x → proj₂ x ≡ (c p₁ , c p₂)) combined-stream
    combined-const = merge-always (stream p₁) (stream p₂) (essence-const p₁) (essence-const p₂)
    combined-init : proj₁ (Stream.head combined-stream) ≡ (o p₁ , o p₂)
    combined-init = cong₂ _,_ (init-consistent p₁) (init-consistent p₂)
⊗-preserves-standard : ∀ {O₁ C₁ O₂ C₂ : Set} (o₁ : O₁) (c₁ : C₁) (o₂ : O₂) (c₂ : C₂) →
  (mkStandardProcess O₁ C₁ o₁ c₁ ⊗ mkStandardProcess O₂ C₂ o₂ c₂) ≈ₚ
  mkStandardProcess (O₁ × O₂) (C₁ × C₂) (o₁ , o₂) (c₁ , c₂)
⊗-preserves-standard o₁ c₁ o₂ c₂ = merge-const-lemma (o₁ , c₁) (o₂ , c₂)
-- 异类型过程互模拟
record ≈-hetero {A B : Set} (s₁ : Stream A) (s₂ : Stream B) (f : A → B) : Set where
  coinductive
  field
    head≈ : f (Stream.head s₁) ≡ Stream.head s₂
    tail≈ : ≈-hetero (Stream.tail s₁) (Stream.tail s₂) f
open ≈-hetero public
record ≈ₚ-hetero {O₁ C₁ O₂ C₂ : Set}
                  (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂)
                  (f-O : O₁ → O₂) (f-C : C₁ → C₂) : Set where
  field
    stream≈ : ≈-hetero (stream p₁) (stream p₂) (comb f-O f-C)
open ≈ₚ-hetero public
≈ₚ-hetero-refl : ∀ {O C : Set} (p : Process O C) → ≈ₚ-hetero p p id id
≈ₚ-hetero-refl p .stream≈ .head≈ = refl
≈ₚ-hetero-refl p .stream≈ .tail≈ = ≈ₚ-hetero-refl (next p) .stream≈
-- 对称幺半范畴结构（同构）
UnitProcess : Process ⊤ ⊤
UnitProcess = mkStandardProcess ⊤ ⊤ tt tt
assoc-iso-O : ∀ {A B C : Set} → ((A × B) × C) → (A × (B × C))
assoc-iso-O ((a , b) , c) = (a , (b , c))
assoc-iso-C : ∀ {A B C : Set} → ((A × B) × C) → (A × (B × C))
assoc-iso-C ((a , b) , c) = (a , (b , c))
merge-stream-assoc : ∀ {O₁ C₁ O₂ C₂ O₃ C₃ : Set}
                     (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂)) (s₃ : Stream (O₃ × C₃))
                     → ≈-hetero (merge-stream (merge-stream s₁ s₂) s₃)
                                (merge-stream s₁ (merge-stream s₂ s₃))
                                (comb assoc-iso-O assoc-iso-C)
merge-stream-assoc s₁ s₂ s₃ .head≈ = refl
merge-stream-assoc s₁ s₂ s₃ .tail≈ = merge-stream-assoc (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₃)
⊗-assoc-hetero : ∀ {O₁ C₁ O₂ C₂ O₃ C₃ : Set}
                 (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) (p₃ : Process O₃ C₃)
                 → ≈ₚ-hetero ((p₁ ⊗ p₂) ⊗ p₃) (p₁ ⊗ (p₂ ⊗ p₃)) assoc-iso-O assoc-iso-C
⊗-assoc-hetero p₁ p₂ p₃ .stream≈ = merge-stream-assoc (stream p₁) (stream p₂) (stream p₃)
left-unit-O : ∀ {O : Set} → (⊤ × O) → O
left-unit-O (tt , o) = o
left-unit-C : ∀ {C : Set} → (⊤ × C) → C
left-unit-C (tt , c) = c
left-stream-bisim : ∀ {O C : Set} (s : Stream (O × C))
                    → ≈-hetero (merge-stream (stream UnitProcess) s) s
                               (comb left-unit-O left-unit-C)
left-stream-bisim s .head≈ = refl
left-stream-bisim s .tail≈ = left-stream-bisim (Stream.tail s)
⊗-left-unit-hetero : ∀ {O C : Set} (p : Process O C)
                     → ≈ₚ-hetero (UnitProcess ⊗ p) p left-unit-O left-unit-C
⊗-left-unit-hetero p .stream≈ = left-stream-bisim (stream p)
right-unit-O : ∀ {O : Set} → (O × ⊤) → O
right-unit-O (o , tt) = o
right-unit-C : ∀ {C : Set} → (C × ⊤) → C
right-unit-C (c , tt) = c
right-stream-bisim : ∀ {O C : Set} (s : Stream (O × C))
                     → ≈-hetero (merge-stream s (stream UnitProcess)) s
                                (comb right-unit-O right-unit-C)
right-stream-bisim s .head≈ = refl
right-stream-bisim s .tail≈ = right-stream-bisim (Stream.tail s)
⊗-right-unit-hetero : ∀ {O C : Set} (p : Process O C)
                      → ≈ₚ-hetero (p ⊗ UnitProcess) p right-unit-O right-unit-C
⊗-right-unit-hetero p .stream≈ = right-stream-bisim (stream p)
swap-O : ∀ {A B : Set} → (A × B) → (B × A)
swap-O (a , b) = (b , a)
swap-C : ∀ {A B : Set} → (A × B) → (B × A)
swap-C (a , b) = (b , a)
merge-stream-comm : ∀ {O₁ C₁ O₂ C₂ : Set}
                    (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂))
                    → ≈-hetero (merge-stream s₁ s₂) (merge-stream s₂ s₁) (comb swap-O swap-C)
merge-stream-comm s₁ s₂ .head≈ = refl
merge-stream-comm s₁ s₂ .tail≈ = merge-stream-comm (Stream.tail s₁) (Stream.tail s₂)
⊗-comm-hetero : ∀ {O₁ C₁ O₂ C₂ : Set}
                (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂)
                → ≈ₚ-hetero (p₁ ⊗ p₂) (p₂ ⊗ p₁) swap-O swap-C
⊗-comm-hetero p₁ p₂ .stream≈ = merge-stream-comm (stream p₁) (stream p₂)
-- 过程唯一性定理：核心相同、初始观察相同且各自恒常的两个过程必然互模拟等价
Process-Uniqueness : Set₁
Process-Uniqueness =
  ∀ {O C : Set} (o₀ : O) (c₀ : C) →
  ∀ (p q : Process O C) →
  core p ≡ c₀ →
  core q ≡ c₀ →
  Process.o p ≡ o₀ →
  Process.o q ≡ o₀ →
  Always (λ x → proj₁ x ≡ o₀) (stream p) →
  Always (λ x → proj₁ x ≡ o₀) (stream q) →
  p ≈ₚ q
process-uniqueness-proof : Process-Uniqueness
process-uniqueness-proof {O} {C} o₀ c₀ p q cp≡c₀ cq≡c₀ op≡o₀ oq≡o₀ p-always-o₀ q-always-o₀ =
  let
    p-both-const : BothComponentsConstant o₀ c₀ (stream p)
    p-both-const = (p-always-o₀ , subst (λ x → Always (λ y → proj₂ y ≡ x) (stream p)) cp≡c₀ (essence-const p))
    q-both-const : BothComponentsConstant o₀ c₀ (stream q)
    q-both-const = (q-always-o₀ , subst (λ x → Always (λ y → proj₂ y ≡ x) (stream q)) cq≡c₀ (essence-const q))
    p≈const : stream p ≈ constStream (o₀ , c₀)
    p≈const = both-const-implies-≈-constStream o₀ c₀ (stream p) p-both-const
    q≈const : stream q ≈ constStream (o₀ , c₀)
    q≈const = both-const-implies-≈-constStream o₀ c₀ (stream q) q-both-const
  in
  ≈-trans p≈const (≈-sym q≈const)
-- next 操作的引理
next-functor : ∀ {O C} {p q : Process O C} → p ≈ₚ q → next p ≈ₚ next q
next-functor p≈q = _≈_.tail≈ p≈q
next-core-comm : ∀ {O C} (p : Process O C) → core (next p) ≡ core p
next-core-comm = c-conservation
stream-tail-n-tail : ∀ {A} (s : Stream A) (n : ℕ) →
                     Stream.tail (stream-tail-n s n) ≡ stream-tail-n (Stream.tail s) n
stream-tail-n-tail s zero = refl
stream-tail-n-tail s (suc n) = stream-tail-n-tail (Stream.tail s) n
next-iter : ∀ {O C} (p : Process O C) (n : ℕ) →
            stream (iter n next p) ≡ stream-tail-n (stream p) n
next-iter p zero = refl
next-iter p (suc n) =
  begin
    stream (iter (suc n) next p)
      ≡⟨ refl ⟩
    stream (next (iter n next p))
      ≡⟨ refl ⟩
    Stream.tail (stream (iter n next p))
      ≡⟨ cong Stream.tail (next-iter p n) ⟩
    Stream.tail (stream-tail-n (stream p) n)
      ≡⟨ stream-tail-n-tail (stream p) n ⟩
    stream-tail-n (Stream.tail (stream p)) n
      ≡⟨ refl ⟩
    stream-tail-n (stream p) (suc n)
  ∎
next-preserves-essence-const : ∀ {O C} (p : Process O C) →
                               Always (λ x → proj₂ x ≡ core (next p)) (stream (next p))
next-preserves-essence-const = next-preserves-constancy
observe-iter : ∀ {O C} (p : Process O C) (n : ℕ) →
               observe p n ≡ observe (iter n next p) 0
observe-iter p n =
  begin
    observe p n
      ≡⟨ refl ⟩
    proj₁ (Stream.head (stream-tail-n (stream p) n))
      ≡⟨ sym (cong (λ s → proj₁ (Stream.head s)) (next-iter p n)) ⟩
    proj₁ (Stream.head (stream (iter n next p)))
      ≡⟨ refl ⟩
    observe (iter n next p) 0
  ∎
-- ⊗ 张量积的引理
⊗-functor₁ : ∀ {O₁ C₁ O₂ C₂} 
             (p₁ p₁' : Process O₁ C₁)
             (p₂ : Process O₂ C₂)
             → p₁ ≈ₚ p₁' 
             → (p₁ ⊗ p₂) ≈ₚ (p₁' ⊗ p₂)
⊗-functor₁ p₁ p₁' p₂ p₁≈p₁' = helper (stream p₁) (stream p₁') (stream p₂) p₁≈p₁'
  where
    helper : ∀ {O₁ C₁ O₂ C₂} (s₁ s₁' : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂)) →
             s₁ ≈ s₁' → merge-stream s₁ s₂ ≈ merge-stream s₁' s₂
    helper s₁ s₁' s₂ eq ._≈_.head≈ = cong (λ x → merge-state x (Stream.head s₂)) (_≈_.head≈ eq)
    helper s₁ s₁' s₂ eq ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₁') (Stream.tail s₂) (_≈_.tail≈ eq)

⊗-functor₂ : ∀ {O₁ C₁ O₂ C₂}
             (p₁ : Process O₁ C₁)
             (p₂ p₂' : Process O₂ C₂)
             → p₂ ≈ₚ p₂' 
             → (p₁ ⊗ p₂) ≈ₚ (p₁ ⊗ p₂')
⊗-functor₂ p₁ p₂ p₂' p₂≈p₂' = helper (stream p₁) (stream p₂) (stream p₂') p₂≈p₂'
  where
    helper : ∀ {O₁ C₁ O₂ C₂} (s₁ : Stream (O₁ × C₁)) (s₂ s₂' : Stream (O₂ × C₂)) →
             s₂ ≈ s₂' → merge-stream s₁ s₂ ≈ merge-stream s₁ s₂'
    helper s₁ s₂ s₂' eq ._≈_.head≈ = cong (merge-state (Stream.head s₁)) (_≈_.head≈ eq)
    helper s₁ s₂ s₂' eq ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₂') (_≈_.tail≈ eq)
⊗-functor : ∀ {O₁ C₁ O₂ C₂} 
            {p₁ p₁' : Process O₁ C₁} 
            {p₂ p₂' : Process O₂ C₂} 
            → p₁ ≈ₚ p₁' 
            → p₂ ≈ₚ p₂' 
            → (p₁ ⊗ p₂) ≈ₚ (p₁' ⊗ p₂')
⊗-functor {p₁ = p₁} {p₁'} {p₂} {p₂'} eq1 eq2 = helper (stream p₁) (stream p₁') (stream p₂) (stream p₂') eq1 eq2
  where
    helper : ∀ {O₁ C₁ O₂ C₂} 
             (s₁ s₁' : Stream (O₁ × C₁)) 
             (s₂ s₂' : Stream (O₂ × C₂)) 
             → s₁ ≈ s₁' 
             → s₂ ≈ s₂' 
             → merge-stream s₁ s₂ ≈ merge-stream s₁' s₂'
    helper s₁ s₁' s₂ s₂' eq1 eq2 ._≈_.head≈ = 
      cong₂ merge-state (_≈_.head≈ eq1) (_≈_.head≈ eq2)
    helper s₁ s₁' s₂ s₂' eq1 eq2 ._≈_.tail≈ = 
      helper (Stream.tail s₁) (Stream.tail s₁') (Stream.tail s₂) (Stream.tail s₂') 
             (_≈_.tail≈ eq1) (_≈_.tail≈ eq2)
⊗-core-comm : ∀ {O₁ C₁ O₂ C₂} (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) →
              core (p₁ ⊗ p₂) ≡ (core p₁ , core p₂)
⊗-core-comm p₁ p₂ = refl
⊗-next-comm : ∀ {O₁ C₁ O₂ C₂}
              → (p1 : Process O₁ C₁) (p2 : Process O₂ C₂)
              → (next (p1 ⊗ p2)) ≈ₚ (next p1 ⊗ next p2)
⊗-next-comm p1 p2 ._≈_.head≈ = refl
⊗-next-comm p1 p2 ._≈_.tail≈ = ≈-refl
⊗-observe-comm : ∀ {O₁ C₁ O₂ C₂} (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) (n : ℕ) →
                 observe (p₁ ⊗ p₂) n ≡ (observe p₁ n , observe p₂ n)
⊗-observe-comm p₁ p₂ n =
  begin
    observe (p₁ ⊗ p₂) n
      ≡⟨ refl ⟩
    proj₁ (Stream.head (stream-tail-n (merge-stream (stream p₁) (stream p₂)) n))
      ≡⟨ merge-stream-observe (stream p₁) (stream p₂) n ⟩
    (observe p₁ n , observe p₂ n)
  ∎
  where
    merge-stream-observe : ∀ {O₁ C₁ O₂ C₂} (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂)) (n : ℕ) →
                           proj₁ (Stream.head (stream-tail-n (merge-stream s₁ s₂) n)) ≡
                           (proj₁ (Stream.head (stream-tail-n s₁ n)) , proj₁ (Stream.head (stream-tail-n s₂ n)))
    merge-stream-observe s₁ s₂ zero = refl
    merge-stream-observe s₁ s₂ (suc n) = merge-stream-observe (Stream.tail s₁) (Stream.tail s₂) n
-- 对称幺半范畴的引理
⊗-assoc : ∀ {O₁ C₁ O₂ C₂ O₃ C₃} (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) (p₃ : Process O₃ C₃) →
          ≈ₚ-hetero ((p₁ ⊗ p₂) ⊗ p₃) (p₁ ⊗ (p₂ ⊗ p₃)) assoc-iso-O assoc-iso-C
⊗-assoc = ⊗-assoc-hetero
⊗-left-unit : ∀ {O C} (p : Process O C) →
              ≈ₚ-hetero (UnitProcess ⊗ p) p left-unit-O left-unit-C
⊗-left-unit = ⊗-left-unit-hetero
⊗-right-unit : ∀ {O C} (p : Process O C) →
               ≈ₚ-hetero (p ⊗ UnitProcess) p right-unit-O right-unit-C
⊗-right-unit = ⊗-right-unit-hetero
⊗-comm : ∀ {O₁ C₁ O₂ C₂} (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) →
         ≈ₚ-hetero (p₁ ⊗ p₂) (p₂ ⊗ p₁) swap-O swap-C
⊗-comm = ⊗-comm-hetero
