{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：相干模式、演化与不可逆定理
哲学意义：动态存在者本质不可消减的偶性形态重构与演化不可逆性
-}
module ALMA.Beings where
open import ALMA.Core public
-- 预备定义：命题与集合截断层级
isProp : Set → Set
isProp A = (x y : A) → x ≡ y
isSet : Set → Set
isSet A = {x y : A} → isProp (x ≡ y)
ℕ-isSet : isSet ℕ
ℕ-isSet = ≡-irrelevant
Bool-isSet : isSet Bool
Bool-isSet = Decidable⇒UIP.≡-irrelevant Bool-_≟_
⊤-isSet : isSet ⊤
⊤-isSet = Decidable⇒UIP.≡-irrelevant Unit-_≟_
×-isSet : ∀ {A B : Set} → (∀ (x y : A) → Dec (x ≡ y)) → (∀ (x y : B) → Dec (x ≡ y)) → isSet (A × B)
×-isSet decA decB = Decidable⇒UIP.≡-irrelevant (≡-dec decA (λ {_} → decB))
IsZero : ℕ → Set
IsZero zero = ⊤
IsZero (suc _) = ⊥
-- 度量与熵：过程的空间结构与方向性
record Metric (O : Set) : Set where
  field
    dist : O → O → ℕ
    dist-refl : ∀ {o} → dist o o ≡ 0
    dist-sym : ∀ {o1 o2} → dist o1 o2 ≡ dist o2 o1
    dist-triangle : ∀ {o1 o2 o3} → dist o1 o3 ≤ dist o1 o2 + dist o2 o3
open Metric public
record Entropy (O : Set) : Set where
  field
    entropy : O → ℕ
open Entropy public
-- 相干模式：过程阶段性快照
record CoherentPattern (O : Set) (C : Set) : Set where
  constructor mkPattern
  field
    base     : Process O C
    internal : ℕ
    external : ℕ
open CoherentPattern public
data CoherenceStage : Set where
  Alive  : CoherenceStage
  Broken : CoherenceStage
  Faded  : CoherenceStage
Alive≢Faded : Alive ≢ Faded
Alive≢Faded eq = subst P eq tt
  where
  P : CoherenceStage → Set
  P Alive = ⊤
  P Faded = ⊥
  P Broken = ⊤
Alive≢Broken : Alive ≢ Broken
Alive≢Broken eq = subst P eq tt
  where
  P : CoherenceStage → Set
  P Alive = ⊤
  P Faded = ⊤
  P Broken = ⊥
Faded≢Alive : Faded ≢ Alive
Faded≢Alive = Alive≢Faded ∘ sym
Faded≢Broken : Faded ≢ Broken
Faded≢Broken eq = subst P eq tt
  where
  P : CoherenceStage → Set
  P Alive = ⊤
  P Faded = ⊤
  P Broken = ⊥
Broken≢Alive : Broken ≢ Alive
Broken≢Alive = Alive≢Broken ∘ sym
Broken≢Faded : Broken ≢ Faded
Broken≢Faded = Faded≢Broken ∘ sym
-- 反馈增益：内禀驱动力与外部阻力之差
feedback-gain : ℕ → ℕ → ℕ
feedback-gain i e = i ∸ e
lemma-zero-feedback : ∀ e → feedback-gain 0 e ≡ 0
lemma-zero-feedback zero = refl
lemma-zero-feedback (suc e) = refl
lemma-positive-i-le-e-feedback-zero : ∀ {i e} → i > 0 → i ≤ e → feedback-gain i e ≡ 0
lemma-positive-i-le-e-feedback-zero _ i≤e = m≤n⇒m∸n≡0 i≤e
∸-additive : ∀ {i1 e1 i2 e2} → e1 ≤ i1 → e2 ≤ i2 → (i1 ∸ e1) + (i2 ∸ e2) ≡ (i1 + i2) ∸ (e1 + e2)
∸-additive {i1} {e1} {i2} {e2} e1≤i1 e2≤i2 =
  let
    a = i1 ∸ e1
    b = i2 ∸ e2
    p1 : i1 ≡ e1 + a
    p1 = m≤n→n≡m+n∸m e1≤i1
    p2 : i2 ≡ e2 + b
    p2 = m≤n→n≡m+n∸m e2≤i2
    add-rearrange : (e1 + a) + (e2 + b) ≡ (e1 + e2) + (a + b)
    add-rearrange =
      begin
        (e1 + a) + (e2 + b)
          ≡⟨ +-assoc e1 a (e2 + b) ⟩
        e1 + (a + (e2 + b))
          ≡⟨ cong (e1 +_) (cong (a +_) (+-comm e2 b)) ⟩
        e1 + (a + (b + e2))
          ≡⟨ cong (e1 +_) (sym (+-assoc a b e2)) ⟩
        e1 + ((a + b) + e2)
          ≡⟨ cong (e1 +_) (+-comm (a + b) e2) ⟩
        e1 + (e2 + (a + b))
          ≡⟨ sym (+-assoc e1 e2 (a + b)) ⟩
        (e1 + e2) + (a + b)
      ∎
    sum-eq : i1 + i2 ≡ (e1 + e2) + (a + b)
    sum-eq = trans (cong₂ _+_ p1 p2) add-rearrange
  in
  begin
    a + b
      ≡⟨ sym (+-∸-cancelˡ (e1 + e2) (a + b)) ⟩
    ((e1 + e2) + (a + b)) ∸ (e1 + e2)
      ≡⟨ cong (λ x → x ∸ (e1 + e2)) (sym sum-eq) ⟩
    (i1 + i2) ∸ (e1 + e2)
  ∎
feedback-gain-additive-coherent : ∀ {i1 e1 i2 e2}
                                → i1 > e1 → i2 > e2
                                → feedback-gain i1 e1 + feedback-gain i2 e2 ≡ feedback-gain (i1 + i2) (e1 + e2)
feedback-gain-additive-coherent {i1} {e1} {i2} {e2} i1>e1 i2>e2 =
  ∸-additive (suc≤→≤ i1>e1) (suc≤→≤ i2>e2)
-- 相干性判定与演化推进
is-coherent : ∀ {O C} → CoherentPattern O C → Set
is-coherent cp = internal cp > external cp
step-process : ∀ {O C} → CoherentPattern O C → Process O C
step-process cp = next (base cp)
next-external : ∀ {O} → (O → ℕ) → CoherentPattern O ⊤ → ℕ
next-external env cp = env (observe (base cp) 0)
next-internal : ∀ {O} → (O → ℕ) → CoherentPattern O ⊤ → ℕ
next-internal env cp = internal cp + feedback-gain (internal cp) (external cp)
next-coherent : ∀ {O} → (O → ℕ) → CoherentPattern O ⊤ → CoherentPattern O ⊤
next-coherent env cp = mkPattern
  (step-process cp)
  (next-internal env cp)
  (env (observe (step-process cp) 0))
-- 动态一致性：演化流的局部转换律
record DynamicCoherent {O : Set} (env : O → ℕ) (s : Stream (CoherentPattern O ⊤)) : Set where
  coinductive
  field
    internal-step : Stream.head (Stream.tail s) .internal ≡ next-internal env (Stream.head s)
    external-step : Stream.head (Stream.tail s) .external ≡ env (observe (Stream.head (Stream.tail s) .base) 0)
    process-step  : Stream.head (Stream.tail s) .base     ≡ step-process (Stream.head s)
    tail-ok       : DynamicCoherent env (Stream.tail s)
open DynamicCoherent public
AlwaysCoherent : ∀ {O} → Stream (CoherentPattern O ⊤) → Set
AlwaysCoherent s = Always is-coherent s
-- 演化余代数：从初始过程与内部驱动力生成相干流（本体论视角）
module Evolution (O : Set) (env : O → ℕ) (init-proc : Process O ⊤) (init-int : ℕ) where
  State = Process O ⊤ × ℕ
  coalg : State → CoherentPattern O ⊤ × State
  coalg (proc , i) =
    let e  = env (observe proc 0)
        cp = mkPattern proc i e
        i' = i + feedback-gain i e
        proc' = next proc
    in cp , (proc' , i')
  evolution : State → Stream (CoherentPattern O ⊤)
  evolution = ana coalg
  start-stream : ℕ → Stream (CoherentPattern O ⊤)
  start-stream i = evolution (init-proc , i)
module _ (O : Set) (env : O → ℕ) (init-proc : Process O ⊤) (init-int : ℕ) where
  open Evolution O env init-proc init-int
  dynamic-consistent : ∀ st → DynamicCoherent env (evolution st)
  dynamic-consistent st .internal-step = refl
  dynamic-consistent st .external-step = refl
  dynamic-consistent st .process-step = refl
  dynamic-consistent st .tail-ok = dynamic-consistent (proj₂ (coalg st))
-- 相干阶段判定
CoherentStage : ∀ {O} → CoherentPattern O ⊤ → CoherenceStage
CoherentStage cp =
  if external cp <ᵇ internal cp
    then Alive
    else if internal cp ≡ᵇ 0
      then Faded
      else Broken
faded→internal-zero : ∀ {O} (cp : CoherentPattern O ⊤)
                    → CoherentStage cp ≡ Faded
                    → internal cp ≡ 0
faded→internal-zero cp eq = helper (external cp <ᵇ internal cp) (internal cp ≡ᵇ 0) refl refl
  where
  helper : (b1 b2 : Bool)
         → b1 ≡ (external cp <ᵇ internal cp)
         → b2 ≡ (internal cp ≡ᵇ 0)
         → internal cp ≡ 0
  helper true _ eq1 _ =
    let
      b1≡true : (external cp <ᵇ internal cp) ≡ true
      b1≡true = sym eq1
      stage≡Alive : CoherentStage cp ≡ Alive
      stage≡Alive = cong (λ b → if b then Alive else if (internal cp ≡ᵇ 0) then Faded else Broken) b1≡true
      contradiction : Alive ≡ Faded
      contradiction = trans (sym stage≡Alive) eq
    in ⊥-elim (Alive≢Faded contradiction)
  helper false true _ eq2 with internal cp
  ... | zero = refl
  ... | suc n =
    let
      suc≡ᵇ0≡false : (suc n ≡ᵇ 0) ≡ false
      suc≡ᵇ0≡false = refl
      contradiction : true ≡ false
      contradiction = trans eq2 suc≡ᵇ0≡false
    in ⊥-elim (true≢false contradiction)
  helper false false eq1 eq2 =
    let
      b1≡false : (external cp <ᵇ internal cp) ≡ false
      b1≡false = sym eq1
      b2≡false : (internal cp ≡ᵇ 0) ≡ false
      b2≡false = sym eq2
      step1 : CoherentStage cp ≡ (if (internal cp ≡ᵇ 0) then Faded else Broken)
      step1 = cong (λ b1 → if b1 then Alive else if (internal cp ≡ᵇ 0) then Faded else Broken) b1≡false
      step2 : (if (internal cp ≡ᵇ 0) then Faded else Broken) ≡ Broken
      step2 = cong (λ b2 → if b2 then Faded else Broken) b2≡false
      stage≡Broken : CoherentStage cp ≡ Broken
      stage≡Broken = trans step1 step2
      contradiction : Broken ≡ Faded
      contradiction = trans (sym stage≡Broken) eq
    in ⊥-elim (Broken≢Faded contradiction)
internal-zero→faded : ∀ {O} (cp : CoherentPattern O ⊤)
                    → internal cp ≡ 0
                    → CoherentStage cp ≡ Faded
internal-zero→faded cp i≡0 =
  let
    i = internal cp
    e = external cp
    b1≡false : (e <ᵇ i) ≡ false
    b1≡false = subst (λ x → (e <ᵇ x) ≡ false) (sym i≡0) (0<ᵇn≡false e)
    b2≡true : (i ≡ᵇ 0) ≡ true
    b2≡true = my-≡⇒≡ᵇ i 0 i≡0
  in
    begin
      CoherentStage cp
        ≡⟨ refl ⟩
      (if e <ᵇ i then Alive else if (i ≡ᵇ 0) then Faded else Broken)
        ≡⟨ cong (λ b → if b then Alive else if (i ≡ᵇ 0) then Faded else Broken) b1≡false ⟩
      (if (i ≡ᵇ 0) then Faded else Broken)
        ≡⟨ cong (λ b → if b then Faded else Broken) b2≡true ⟩
      Faded
    ∎
faded-iff-internal-zero : ∀ {O} (cp : CoherentPattern O ⊤)
                        → (CoherentStage cp ≡ Faded → internal cp ≡ 0)
                        × (internal cp ≡ 0 → CoherentStage cp ≡ Faded)
faded-iff-internal-zero cp = faded→internal-zero cp , internal-zero→faded cp
mkFaded : ∀ {O} (cp : CoherentPattern O ⊤) → internal cp ≡ 0 → external cp ≡ 0 → CoherentStage cp ≡ Faded
mkFaded cp i≡0 _ = internal-zero→faded cp i≡0
-- Faded 阶段的不可逆定理
module _ (O : Set) (env : O → ℕ) where
  zero-internal-persist : (cp : CoherentPattern O ⊤)
                        → internal cp ≡ 0
                        → next-internal env cp ≡ 0
  zero-internal-persist cp refl =
    let e = external cp
    in begin
      0 + feedback-gain 0 e
        ≡⟨ +-identityˡ (feedback-gain 0 e) ⟩
      feedback-gain 0 e
        ≡⟨ lemma-zero-feedback e ⟩
      0
    ∎
  theorem-faded-irreversible : ∀ (s : Stream (CoherentPattern O ⊤))
                             → DynamicCoherent env s
                             → CoherentStage (Stream.head s) ≡ Faded
                             → CoherentStage (Stream.head (Stream.tail s)) ≡ Faded
  theorem-faded-irreversible s dyn head-faded =
    let
      head-cp = Stream.head s
      i0≡0 = faded→internal-zero head-cp head-faded
      i1≡0 = trans (dyn .internal-step) (zero-internal-persist head-cp i0≡0)
      next-cp = Stream.head (Stream.tail s)
    in internal-zero→faded next-cp i1≡0
-- Broken 阶段的辅助引理
broken→¬i>e : ∀ {O} (cp : CoherentPattern O ⊤)
            → CoherentStage cp ≡ Broken
            → ¬ (internal cp > external cp)
broken→¬i>e cp broken i>e =
  let
    b1≡true : (external cp <ᵇ internal cp) ≡ true
    b1≡true = my-<⇒<ᵇ i>e
    stage≡Alive : CoherentStage cp ≡ Alive
    stage≡Alive = cong (λ b → if b then Alive else if (internal cp ≡ᵇ 0) then Faded else Broken) b1≡true
    contradiction : Alive ≡ Broken
    contradiction = trans (sym stage≡Alive) broken
  in ⊥-elim (Alive≢Broken contradiction)
broken→¬i≡0 : ∀ {O} (cp : CoherentPattern O ⊤)
            → CoherentStage cp ≡ Broken
            → ¬ (internal cp ≡ 0)
broken→¬i≡0 cp broken i≡0 =
  let
    i = internal cp
    e = external cp
    b2≡true : (i ≡ᵇ 0) ≡ true
    b2≡true = my-≡⇒≡ᵇ i 0 i≡0
    b1≡false : (e <ᵇ i) ≡ false
    b1≡false = subst (λ x → (e <ᵇ x) ≡ false) (sym i≡0) (0<ᵇn≡false e)
    stage≡Faded : CoherentStage cp ≡ Faded
    stage≡Faded =
      begin
        CoherentStage cp
          ≡⟨ refl ⟩
        (if e <ᵇ i then Alive else if (i ≡ᵇ 0) then Faded else Broken)
          ≡⟨ cong (λ b → if b then Alive else if (i ≡ᵇ 0) then Faded else Broken) b1≡false ⟩
        (if (i ≡ᵇ 0) then Faded else Broken)
          ≡⟨ cong (λ b → if b then Faded else Broken) b2≡true ⟩
        Faded
      ∎
    contradiction : Faded ≡ Broken
    contradiction = trans (sym stage≡Faded) broken
  in ⊥-elim (Faded≢Broken contradiction)
broken-internal-non-increasing : ∀ {O} {env : O → ℕ}
                               → (cp : CoherentPattern O ⊤)
                               → CoherentStage cp ≡ Broken
                               → next-internal env cp ≤ internal cp
broken-internal-non-increasing {env = env} cp broken =
  let
    ¬i>e = broken→¬i>e cp broken
    ¬i≡0 = broken→¬i≡0 cp broken
    i = internal cp
    e = external cp
    i>0 = ¬zero→suc ¬i≡0
    i≤e = ≮⇒≥ ¬i>e
    gain-zero = lemma-positive-i-le-e-feedback-zero i>0 i≤e
    eq : next-internal env cp ≡ i
    eq = trans (cong (i +_) gain-zero) (+-identityʳ i)
  in subst (λ x → x ≤ i) (sym eq) Nat-≤-refl
-- 流组合子与 ⊤-张量积
zipWith : ∀ {A B C} → (A → B → C) → Stream A → Stream B → Stream C
zipWith f s1 s2 .Stream.head = f (Stream.head s1) (Stream.head s2)
zipWith f s1 s2 .Stream.tail = zipWith f (Stream.tail s1) (Stream.tail s2)
private
  map-merge : ∀ {O₁ O₂} → Stream (O₁ × ⊤) → Stream (O₂ × ⊤) → Stream ((O₁ × O₂) × ⊤)
  map-merge s₁ s₂ .Stream.head = ((proj₁ (Stream.head s₁) , proj₁ (Stream.head s₂)) , tt)
  map-merge s₁ s₂ .Stream.tail = map-merge (Stream.tail s₁) (Stream.tail s₂)
  map-merge-const : ∀ {O₁ O₂} (s₁ : Stream (O₁ × ⊤)) (s₂ : Stream (O₂ × ⊤))
                  → Always (λ x → proj₂ x ≡ tt) (map-merge s₁ s₂)
  map-merge-const s₁ s₂ .Always.head = refl
  map-merge-const s₁ s₂ .Always.tail = map-merge-const (Stream.tail s₁) (Stream.tail s₂)
_⊗⊤_ : ∀ {O₁ O₂} → Process O₁ ⊤ → Process O₂ ⊤ → Process (O₁ × O₂) ⊤
p1 ⊗⊤ p2 = mkProc (o p1 , o p2) tt
  (map-merge (stream p1) (stream p2))
  (map-merge-const (stream p1) (stream p2))
  (cong₂ _,_ (init-consistent p1) (init-consistent p2))
-- 相干模式的张量积复合
_⊗coh_ : ∀ {O₁ O₂} → CoherentPattern O₁ ⊤ → CoherentPattern O₂ ⊤
       → CoherentPattern (O₁ × O₂) ⊤
cp₁ ⊗coh cp₂ = mkPattern
  (base cp₁ ⊗⊤ base cp₂)
  (internal cp₁ + internal cp₂)
  (external cp₁ + external cp₂)
⊗⊤-next-comm : ∀ {O₁ O₂} (p1 : Process O₁ ⊤) (p2 : Process O₂ ⊤)
             → next (p1) ⊗⊤ next (p2) ≡ next (p1 ⊗⊤ p2)
⊗⊤-next-comm p1 p2 = refl
-- 复合保持相干性与动态一致性
⊗coh-preserves-coherence : ∀ {O₁ O₂} (cp₁ : CoherentPattern O₁ ⊤) (cp₂ : CoherentPattern O₂ ⊤)
                         → is-coherent cp₁ → is-coherent cp₂ → is-coherent (cp₁ ⊗coh cp₂)
⊗coh-preserves-coherence cp₁ cp₂ i1>e1 i2>e2 = +-mono-< i1>e1 i2>e2
⊗coh-preserves-always-coherent : ∀ {O₁ O₂} (s₁ : Stream (CoherentPattern O₁ ⊤)) (s₂ : Stream (CoherentPattern O₂ ⊤))
                               → AlwaysCoherent s₁ → AlwaysCoherent s₂
                               → AlwaysCoherent (zipWith _⊗coh_ s₁ s₂)
⊗coh-preserves-always-coherent s₁ s₂ coh₁ coh₂ .Always.head =
  ⊗coh-preserves-coherence (Stream.head s₁) (Stream.head s₂) (coh₁ .Always.head) (coh₂ .Always.head)
⊗coh-preserves-always-coherent s₁ s₂ coh₁ coh₂ .Always.tail =
  ⊗coh-preserves-always-coherent (Stream.tail s₁) (Stream.tail s₂) (coh₁ .Always.tail) (coh₂ .Always.tail)
+-four-rearrange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-four-rearrange a b c d =
  begin
    (a + b) + (c + d)
      ≡⟨ sym (+-assoc (a + b) c d) ⟩
    ((a + b) + c) + d
      ≡⟨ cong (λ x → x + d) (+-assoc a b c) ⟩
    (a + (b + c)) + d
      ≡⟨ cong (λ x → x + d) (cong (a +_) (+-comm b c)) ⟩
    (a + (c + b)) + d
      ≡⟨ cong (λ x → x + d) (sym (+-assoc a c b)) ⟩
    ((a + c) + b) + d
      ≡⟨ +-assoc (a + c) b d ⟩
    (a + c) + (b + d)
  ∎
⊗coh-preserves-dynamic : ∀ {O₁ O₂} (env₁ : O₁ → ℕ) (env₂ : O₂ → ℕ)
                       (s₁ : Stream (CoherentPattern O₁ ⊤)) (s₂ : Stream (CoherentPattern O₂ ⊤))
                       → DynamicCoherent env₁ s₁ → DynamicCoherent env₂ s₂
                       → AlwaysCoherent s₁ → AlwaysCoherent s₂
                       → DynamicCoherent (λ (o1 , o2) → env₁ o1 + env₂ o2) (zipWith _⊗coh_ s₁ s₂)
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .internal-step =
  let
    left-eq = refl
    dyn1-eq = dyn₁ .internal-step
    dyn2-eq = dyn₂ .internal-step
    left-final = trans left-eq (cong₂ _+_ dyn1-eq dyn2-eq)
    cp1 = Stream.head s₁; cp2 = Stream.head s₂
    i1 = internal cp1; e1 = external cp1
    i2 = internal cp2; e2 = external cp2
    coh1 = coh₁ .Always.head; coh2 = coh₂ .Always.head
    g1 = feedback-gain i1 e1; g2 = feedback-gain i2 e2; g12 = feedback-gain (i1 + i2) (e1 + e2)
    p : g1 + g2 ≡ g12
    p = feedback-gain-additive-coherent coh1 coh2
    next1 = next-internal env₁ cp1; next2 = next-internal env₂ cp2
    next12 = next-internal (λ (o1 , o2) → env₁ o1 + env₂ o2) (cp1 ⊗coh cp2)
    right-eq : next1 + next2 ≡ next12
    right-eq =
      begin
        (i1 + g1) + (i2 + g2)
          ≡⟨ +-four-rearrange i1 g1 i2 g2 ⟩
        (i1 + i2) + (g1 + g2)
          ≡⟨ cong ((i1 + i2) +_) p ⟩
        (i1 + i2) + g12
      ∎
  in trans left-final right-eq
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .external-step =
  cong₂ _+_ (dyn₁ .external-step) (dyn₂ .external-step)
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .process-step =
  cong₂ _⊗⊤_ (dyn₁ .process-step) (dyn₂ .process-step)
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .tail-ok =
  ⊗coh-preserves-dynamic env₁ env₂ (Stream.tail s₁) (Stream.tail s₂)
    (dyn₁ .tail-ok) (dyn₂ .tail-ok) (coh₁ .Always.tail) (coh₂ .Always.tail)
-- 桥梁：相干模式还原为过程
coherent-to-process : ∀ {O C} → CoherentPattern O C → Process O C
coherent-to-process = base
coherent-core-conservation : ∀ {O C} (cp : CoherentPattern O C) → core (coherent-to-process cp) ≡ c (base cp)
coherent-core-conservation cp = refl
-- DynamicCoherent 保持性与步进引理
next-preserves-dynamic : ∀ {O} {env : O → ℕ} {s : Stream (CoherentPattern O ⊤)} →
                         DynamicCoherent env s → DynamicCoherent env (Stream.tail s)
next-preserves-dynamic dyn = dyn .tail-ok
⊗-preserves-dynamic : ∀ {O₁ O₂} {env₁ : O₁ → ℕ} {env₂ : O₂ → ℕ}
                      {s₁ : Stream (CoherentPattern O₁ ⊤)} {s₂ : Stream (CoherentPattern O₂ ⊤)} →
                      DynamicCoherent env₁ s₁ → DynamicCoherent env₂ s₂ →
                      AlwaysCoherent s₁ → AlwaysCoherent s₂ →
                      DynamicCoherent (λ (o1 , o2) → env₁ o1 + env₂ o2) (zipWith _⊗coh_ s₁ s₂)
⊗-preserves-dynamic {env₁ = env₁} {env₂} {s₁} {s₂} dyn1 dyn2 coh1 coh2 =
  ⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn1 dyn2 coh1 coh2
dynamic-implies-steps : ∀ {O} {env : O → ℕ} {s : Stream (CoherentPattern O ⊤)} →
                        DynamicCoherent env s →
                        (∀ n → (Stream.head (stream-tail-n (Stream.tail s) n)) .internal ≡
                               next-internal env (Stream.head (stream-tail-n s n)))
                        ×
                        (∀ n → (Stream.head (stream-tail-n (Stream.tail s) n)) .external ≡
                               env (observe ((Stream.head (stream-tail-n (Stream.tail s) n)) .base) 0))
dynamic-implies-steps {O} {env} {s} dyn =
  ( go-internal s dyn
  , go-external s dyn
  )
  where
    go-internal : ∀ (s' : Stream (CoherentPattern O ⊤)) (dyn' : DynamicCoherent env s') n →
                  (Stream.head (stream-tail-n (Stream.tail s') n)) .internal ≡
                  next-internal env (Stream.head (stream-tail-n s' n))
    go-internal s' dyn' zero    = dyn' .internal-step
    go-internal s' dyn' (suc n) = go-internal (Stream.tail s') (dyn' .tail-ok) n
    go-external : ∀ (s' : Stream (CoherentPattern O ⊤)) (dyn' : DynamicCoherent env s') n →
                  (Stream.head (stream-tail-n (Stream.tail s') n)) .external ≡
                  env (observe ((Stream.head (stream-tail-n (Stream.tail s') n)) .base) 0)
    go-external s' dyn' zero    = dyn' .external-step
    go-external s' dyn' (suc n) = go-external (Stream.tail s') (dyn' .tail-ok) n
-- AlwaysCoherent 保持性引理
next-preserves-always-coherent : ∀ {O} {s : Stream (CoherentPattern O ⊤)} →
                                 AlwaysCoherent s → AlwaysCoherent (Stream.tail s)
next-preserves-always-coherent alw = alw .Always.tail
⊗-preserves-always-coherent : ∀ {O₁ O₂} {s₁ : Stream (CoherentPattern O₁ ⊤)} {s₂ : Stream (CoherentPattern O₂ ⊤)} →
                              AlwaysCoherent s₁ → AlwaysCoherent s₂ →
                              AlwaysCoherent (zipWith _⊗coh_ s₁ s₂)
⊗-preserves-always-coherent {s₁ = s₁} {s₂ = s₂} = ⊗coh-preserves-always-coherent s₁ s₂
always-coherent-implies-all : ∀ {O} {s : Stream (CoherentPattern O ⊤)} →
                              AlwaysCoherent s → ∀ n → is-coherent (Stream.head (stream-tail-n s n))
always-coherent-implies-all alw n = always-implies-all-n alw n
