{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：宇宙结构、投影与不可重构定理
哲学意义：从存在者到存在者整体的跃迁，有限视角与无限本质的关系
-}
module ALMA.Cosmos where
open import ALMA.Beings public
-- 不可消减性与宇宙的基本定义
record IsIndestructible {I A C : Set} (essence : C) (stream : Stream ((I → A) × C)) : Set where
  field
    essencePermanent : Always (λ x → proj₂ x ≡ essence) stream
open IsIndestructible public
record Universe (I A C : Set) : Set where
  constructor mkUniverse
  field
    essence : C
    stream  : Stream ((I → A) × C)
    indestruct : IsIndestructible essence stream
open Universe public
record _≈ᵁ_ {I A C} (u v : Universe I A C) : Set where
  field
    essence≈ : essence u ≡ essence v
    stream≈  : stream u ≈ stream v
open _≈ᵁ_ public
≈ᵁ-refl : ∀ {I A C} {u : Universe I A C} → u ≈ᵁ u
≈ᵁ-refl = record { essence≈ = refl ; stream≈ = ≈-refl }
≈ᵁ-sym : ∀ {I A C} {u v : Universe I A C} → u ≈ᵁ v → v ≈ᵁ u
≈ᵁ-sym eq = record { essence≈ = sym (essence≈ eq) ; stream≈ = ≈-sym (stream≈ eq) }
≈ᵁ-trans : ∀ {I A C} {u v w : Universe I A C} → u ≈ᵁ v → v ≈ᵁ w → u ≈ᵁ w
≈ᵁ-trans eq1 eq2 = record
  { essence≈ = trans (essence≈ eq1) (essence≈ eq2)
  ; stream≈  = ≈-trans (stream≈ eq1) (stream≈ eq2)
  }
-- 观察：从宇宙中提取具体偶性
module _ {I A C : Set} where
  observeAccident : Universe I A C → ℕ → I → A
  observeAccident u n i = proj₁ (Stream.head (stream-tail-n (stream u) n)) i
  univ-core : Universe I A C → C
  univ-core = essence
  cosmicStep : Universe I A C → Universe I A C
  cosmicStep u = record
    { essence = essence u
    ; stream = Stream.tail (stream u)
    ; indestruct = record { essencePermanent = Always.tail (essencePermanent (indestruct u)) }
    }
  cosmicStep-preserves-core : ∀ u → univ-core (cosmicStep u) ≡ univ-core u
  cosmicStep-preserves-core u = refl
  univ-essence-constant : ∀ u n → proj₂ (Stream.head (stream-tail-n (stream u) n)) ≡ univ-core u
  univ-essence-constant u n = always-implies-all-n (essencePermanent (indestruct u)) n
  univ-deterministic-observation : ∀ u n i → Σ A (λ a → observeAccident u n i ≡ a)
  univ-deterministic-observation u n i = observeAccident u n i , refl
-- 通用投影：从无限索引到有限索引
Selector : ℕ → Set
Selector n = Fin n → ℕ
proj-stream : ∀ n {C} → Stream ((ℕ → ℕ) × C) → Selector n → Stream ((Fin n → ℕ) × C)
proj-stream n s sel .Stream.head = (λ i → proj₁ (Stream.head s) (sel i)) , proj₂ (Stream.head s)
proj-stream n s sel .Stream.tail = proj-stream n (Stream.tail s) sel
private
  core-const : ∀ n {C} s sel (c : C) → Always (λ x → proj₂ x ≡ c) s →
               Always (λ x → proj₂ x ≡ c) (proj-stream n s sel)
  core-const n s sel c al .Always.head = al .Always.head
  core-const n s sel c al .Always.tail = core-const n (Stream.tail s) sel c (al .Always.tail)
projGeneric : ∀ n {C} → Selector n → Universe ℕ ℕ C → Universe (Fin n) ℕ C
projGeneric n {C} sel cos = record
  { essence = univ-core cos
  ; stream = proj-stream n (stream cos) sel
  ; indestruct = record
      { essencePermanent = core-const n (stream cos) sel (univ-core cos)
                             (essencePermanent (indestruct cos)) }
  }
proj-preserves-core : ∀ n {C} sel (cos : Universe ℕ ℕ C) →
                      essence (projGeneric n sel cos) ≡ univ-core cos
proj-preserves-core n sel cos = refl
module MergeSelectors (n m : ℕ) where
  merge : (Fin n → ℕ) → (Fin m → ℕ) → Fin (n + m) → ℕ
  merge sel₁ sel₂ i = [_,_] sel₁ sel₂ (splitAt n i)
  merge-preserves-core : ∀ {C} (cos : Universe ℕ ℕ C) (sel₁ : Fin n → ℕ) (sel₂ : Fin m → ℕ) →
                         essence (projGeneric (n + m) (merge sel₁ sel₂) cos) ≡ univ-core cos
  merge-preserves-core cos sel₁ sel₂ = refl
-- Cosmos：唯一本质的宇宙
data Cosmos-C : Set where
  CosmicEssence : Cosmos-C
open Cosmos-C public
Cosmos : Set
Cosmos = Universe ℕ ℕ Cosmos-C
proj-stream-cosmos : ∀ n → Stream ((ℕ → ℕ) × Cosmos-C) → Selector n → Stream ((Fin n → ℕ) × Cosmos-C)
proj-stream-cosmos n s sel .Stream.head = (λ i → proj₁ (Stream.head s) (sel i)) , proj₂ (Stream.head s)
proj-stream-cosmos n s sel .Stream.tail = proj-stream-cosmos n (Stream.tail s) sel
private
  core-const-cosmos : ∀ n s sel (c : Cosmos-C) → Always (λ x → proj₂ x ≡ c) s →
                      Always (λ x → proj₂ x ≡ c) (proj-stream-cosmos n s sel)
  core-const-cosmos n s sel c al .Always.head = al .Always.head
  core-const-cosmos n s sel c al .Always.tail = core-const-cosmos n (Stream.tail s) sel c (al .Always.tail)
-- 投影：将无限宇宙降维到有限视角（G）
projCosmos : ∀ n → Selector n → Cosmos → Universe (Fin n) ℕ Cosmos-C
projCosmos n sel cos = record
  { essence = univ-core cos
  ; stream = proj-stream-cosmos n (stream cos) sel
  ; indestruct = record
      { essencePermanent = core-const-cosmos n (stream cos) sel (univ-core cos)
                             (essencePermanent (indestruct cos)) }
  }
record _≈ᶜ_ (x y : Cosmos) : Set where
  field
    essence≈ : essence x ≡ essence y
    stream≈  : stream x ≈ stream y
open _≈ᶜ_ public
≈ᶜ-refl  : ∀ {x} → x ≈ᶜ x
≈ᶜ-refl = record { essence≈ = refl ; stream≈ = ≈-refl }
≈ᶜ-sym   : ∀ {x y} → x ≈ᶜ y → y ≈ᶜ x
≈ᶜ-sym eq = record { essence≈ = sym (essence≈ eq) ; stream≈ = ≈-sym (stream≈ eq) }
≈ᶜ-trans : ∀ {x y z} → x ≈ᶜ y → y ≈ᶜ z → x ≈ᶜ z
≈ᶜ-trans eq1 eq2 = record
  { essence≈ = trans (essence≈ eq1) (essence≈ eq2)
  ; stream≈  = ≈-trans (stream≈ eq1) (stream≈ eq2)
  }
cosmos-essence-unique : ∀ (cos1 cos2 : Cosmos) → essence cos1 ≡ essence cos2
cosmos-essence-unique cos1 cos2 with essence cos1 | essence cos2
... | CosmicEssence | CosmicEssence = refl
cosmos-initial : (ℕ → ℕ) → Cosmos
cosmos-initial o = record
  { essence = CosmicEssence
  ; stream = constStream (o , CosmicEssence)
  ; indestruct = record { essencePermanent = constStream-always-gen (o , CosmicEssence) refl }
  }
-- 嵌入：从有限视角回升到宇宙（F）
private
  toFin : ∀ {n} → ℕ → Maybe (Fin n)
  toFin {zero} _ = nothing
  toFin {suc n} zero = just zero
  toFin {suc n} (suc i) with toFin {n} i
  ... | just x = just (suc x)
  ... | nothing = nothing
  extend-fun : ∀ {n} → (Fin n → ℕ) → (ℕ → ℕ)
  extend-fun f i = maybe f 0 (toFin i)
  embedToCosmos : ∀ {n} → Stream ((Fin n → ℕ) × Cosmos-C) → Stream ((ℕ → ℕ) × Cosmos-C)
  embedToCosmos s .Stream.head = (extend-fun (proj₁ (Stream.head s))) , proj₂ (Stream.head s)
  embedToCosmos s .Stream.tail = embedToCosmos (Stream.tail s)
  extend-always : ∀ {n} {s : Stream ((Fin n → ℕ) × Cosmos-C)} {c : Cosmos-C}
                  → Always (λ x → proj₂ x ≡ c) s
                  → Always (λ x → proj₂ x ≡ c) (embedToCosmos s)
  extend-always alw .Always.head = alw .Always.head
  extend-always alw .Always.tail = extend-always (alw .Always.tail)
  -- 观察等价关系（有限宇宙流之间）
  record _≈obs_ {n} (s t : Stream ((Fin n → ℕ) × Cosmos-C)) : Set where
    coinductive
    field
      head-obs-equiv : ∀ (i : Fin n) → 
        proj₁ (Stream.head s) i ≡ proj₁ (Stream.head t) i
      head-essence-equiv : proj₂ (Stream.head s) ≡ proj₂ (Stream.head t)
      tail-equiv : Stream.tail s ≈obs Stream.tail t
  open _≈obs_
  ≈obs-refl : ∀ {n} {s : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs s
  ≈obs-refl .head-obs-equiv i = refl
  ≈obs-refl .head-essence-equiv = refl
  ≈obs-refl .tail-equiv = ≈obs-refl
  trans-≈obs : ∀ {n} {s t u : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs t → t ≈obs u → s ≈obs u
  trans-≈obs eq1 eq2 .head-obs-equiv i = trans (eq1 .head-obs-equiv i) (eq2 .head-obs-equiv i)
  trans-≈obs eq1 eq2 .head-essence-equiv = trans (eq1 .head-essence-equiv) (eq2 .head-essence-equiv)
  trans-≈obs eq1 eq2 .tail-equiv = trans-≈obs (eq1 .tail-equiv) (eq2 .tail-equiv)
  ≈obs-sym : ∀ {n} {s t : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs t → t ≈obs s
  ≈obs-sym eq ._≈obs_.head-obs-equiv i = sym (eq ._≈obs_.head-obs-equiv i)
  ≈obs-sym eq ._≈obs_.head-essence-equiv = sym (eq ._≈obs_.head-essence-equiv)
  ≈obs-sym eq ._≈obs_.tail-equiv = ≈obs-sym (eq ._≈obs_.tail-equiv)
  toFin-suc : ∀ {n} (k : ℕ) → toFin {suc n} (suc k) ≡ map suc (toFin {n} k)
  toFin-suc {n} k with toFin {n} k
  ... | just x = refl
  ... | nothing = refl
  toFin-toℕ : ∀ {n} (i : Fin n) → toFin (toℕ i) ≡ just i
  toFin-toℕ zero = refl
  toFin-toℕ (suc i) =
    trans (toFin-suc (toℕ i))
          (trans (cong (map suc) (toFin-toℕ i))
                 refl)
  -- 单位律的核心引理：嵌入再投影回来，观察等价于原有限流
  proj-extend-obs-equiv : ∀ {n} (s : Stream ((Fin n → ℕ) × Cosmos-C))
                         → proj-stream-cosmos n (embedToCosmos s) (λ i → toℕ i) ≈obs s
  proj-extend-obs-equiv {n} s = helper
    where
      helper : proj-stream-cosmos n (embedToCosmos s) (λ i → toℕ i) ≈obs s
      helper .head-obs-equiv i =
        trans refl
        (trans refl
        (trans (cong (maybe (proj₁ (Stream.head s)) 0) (toFin-toℕ i))
        refl))
      helper .head-essence-equiv = refl
      helper .tail-equiv = proj-extend-obs-equiv (Stream.tail s)
-- 嵌入：将有限宇宙提升为无限宇宙（F）
universe-to-cosmos : ∀ {n} → Universe (Fin n) ℕ Cosmos-C → Cosmos
universe-to-cosmos u = record
  { essence    = essence u
  ; stream     = embedToCosmos (stream u)
  ; indestruct = record { essencePermanent = extend-always (essencePermanent (indestruct u)) }
  }
-- 函子性质与单位律
embedToCosmos-preserves-≈ : ∀ {n_len} {s t : Stream ((Fin n_len → ℕ) × Cosmos-C)}
                          → s ≈ t → embedToCosmos s ≈ embedToCosmos t
embedToCosmos-preserves-≈ eq ._≈_.head≈ = 
  cong₂ _,_ (cong extend-fun (cong proj₁ (eq ._≈_.head≈))) (cong proj₂ (eq ._≈_.head≈))
embedToCosmos-preserves-≈ eq ._≈_.tail≈ = embedToCosmos-preserves-≈ (eq ._≈_.tail≈)
proj-≈ᵁ : ∀ {n} (sel : Fin n → ℕ) {cos1 cos2 : Cosmos} → cos1 ≈ᶜ cos2 → projCosmos n sel cos1 ≈ᵁ projCosmos n sel cos2
proj-≈ᵁ {n} sel {cos1} {cos2} eq = record
  { essence≈ = trans (proj-preserves-core n sel cos1)
                     (trans (essence≈ eq)
                            (sym (proj-preserves-core n sel cos2)))
  ; stream≈ = proj-stream-≈ (stream≈ eq)
  }
  where
    proj-stream-≈ : {s1 s2 : Stream ((ℕ → ℕ) × Cosmos-C)} → s1 ≈ s2 →
                    proj-stream-cosmos n s1 sel ≈ proj-stream-cosmos n s2 sel
    proj-stream-≈ eq ._≈_.head≈ = cong (λ x → (λ i → proj₁ x (sel i)) , proj₂ x) (_≈_.head≈ eq)
    proj-stream-≈ eq ._≈_.tail≈ = proj-stream-≈ (_≈_.tail≈ eq)
≈ᵁ-implies-≈obs : ∀ {n} {u1 u2 : Universe (Fin n) ℕ Cosmos-C} → u1 ≈ᵁ u2 → stream u1 ≈obs stream u2
≈ᵁ-implies-≈obs {n} eq = helper {n} (eq .stream≈)
  where
    helper : ∀ {n} {s t : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈ t → s ≈obs t
    helper eq .head-obs-equiv i = cong (λ f → f i) (cong proj₁ (eq ._≈_.head≈))
    helper eq .head-essence-equiv = cong proj₂ (eq ._≈_.head≈)
    helper eq .tail-equiv = helper (eq ._≈_.tail≈)
proj-embed-unit : ∀ {n} (u : Universe (Fin n) ℕ Cosmos-C) →
                  stream (projCosmos n (λ i → toℕ i) (universe-to-cosmos u)) ≈obs stream u
proj-embed-unit u = proj-extend-obs-equiv (stream u)
universe-embedding-uniqueness :
  ∀ {n} (u1 u2 : Universe (Fin n) ℕ Cosmos-C)
  → stream u1 ≈obs stream u2
  → Σ Cosmos (λ cos → 
      (Σ (Fin n → ℕ) (λ sel1 → stream (projCosmos n sel1 cos) ≈obs stream u1)) 
      × 
      (Σ (Fin n → ℕ) (λ sel2 → stream (projCosmos n sel2 cos) ≈obs stream u2))
    )
universe-embedding-uniqueness {n} u1 u2 stream-obs =
  (cos , ((sel1 , bisim1) , (sel2 , bisim2)))
  where
    cos : Cosmos
    cos = universe-to-cosmos u1
    sel1 : Fin n → ℕ
    sel1 i = toℕ i
    sel2 : Fin n → ℕ
    sel2 i = toℕ i
    bisim1 : stream (projCosmos n sel1 cos) ≈obs stream u1
    bisim1 = proj-extend-obs-equiv (stream u1)
    bisim2 : stream (projCosmos n sel2 cos) ≈obs stream u2
    bisim2 = trans-≈obs (proj-extend-obs-equiv (stream u1)) stream-obs
-- 弱伴随：逐点流等价与弱余单位
record _≈∞_ (s t : Stream ((ℕ → ℕ) × Cosmos-C)) : Set where
  coinductive
  field
    head-pointwise : ∀ (k : ℕ) → proj₁ (Stream.head s) k ≡ proj₁ (Stream.head t) k
    head-essence : proj₂ (Stream.head s) ≡ proj₂ (Stream.head t)
    tail-pointwise : Stream.tail s ≈∞ Stream.tail t
open _≈∞_ public
-- 从无限投影再嵌入后，在一切可观察点上与原无限宇宙一致（弱三角恒等式）
triangle1-pointwise : ∀ {n_len} (u : Universe (Fin n_len) ℕ Cosmos-C)
                    → stream (universe-to-cosmos (projCosmos n_len (λ i → toℕ i) (universe-to-cosmos u)))
                    ≈∞ stream (universe-to-cosmos u)
triangle1-pointwise {n_len} u = helper
  where
    f : Fin n_len → ℕ
    f = proj₁ (Stream.head (stream u))
    general-lemma : ∀ (m : Maybe (Fin n_len))
                  → maybe (λ i → maybe f 0 (toFin (toℕ i))) 0 m
                  ≡ maybe f 0 m
    general-lemma nothing = refl
    general-lemma (just i) = cong (λ x → maybe f 0 x) (toFin-toℕ i)
    helper : stream (universe-to-cosmos (projCosmos n_len (λ i → toℕ i) (universe-to-cosmos u)))
           ≈∞ stream (universe-to-cosmos u)
    helper .head-pointwise k = general-lemma (toFin k)
    helper .head-essence = refl
    helper .tail-pointwise = triangle1-pointwise (cosmicStep u)
-- 通用不可重构定理：对任意有限维度，有限观察无法重构唯一无限宇宙
module GeneralNoReconstruction (n : ℕ) where
  obs-selector : Fin n → ℕ
  obs-selector i = toℕ i
  cosmic-view-1 cosmic-view-2 : ℕ → ℕ
  cosmic-view-1 _ = 0
  cosmic-view-2 k = if k <ᵇ n then 0 else 1
  cosmos-instance-1 : Cosmos
  cosmos-instance-1 = cosmos-initial cosmic-view-1
  cosmos-instance-2 : Cosmos
  cosmos-instance-2 = cosmos-initial cosmic-view-2
  <ᵇ-self-false : ∀ n → (n <ᵇ n) ≡ false
  <ᵇ-self-false zero = refl
  <ᵇ-self-false (suc n) = <ᵇ-self-false n
  finite-obs-equiv : stream (projCosmos n obs-selector cosmos-instance-1) ≈obs 
                     stream (projCosmos n obs-selector cosmos-instance-2)
  finite-obs-equiv .head-obs-equiv i =
    sym (cong (λ b → if b then 0 else 1) (my-<⇒<ᵇ (toℕ<n i)))
  finite-obs-equiv .head-essence-equiv = refl
  finite-obs-equiv .tail-equiv = finite-obs-equiv
  ¬cosmos1≈cosmos2 : ¬ (cosmos-instance-1 ≈ᶜ cosmos-instance-2)
  ¬cosmos1≈cosmos2 eq = 0≢1 (trans (f-eq n) view2-n-eq1)
    where
    head≡ : Stream.head (stream cosmos-instance-1) ≡ Stream.head (stream cosmos-instance-2)
    head≡ = stream≈ eq ._≈_.head≈
    view≡ : cosmic-view-1 ≡ cosmic-view-2
    view≡ = cong proj₁ head≡
    f-eq : ∀ (x : ℕ) → cosmic-view-1 x ≡ cosmic-view-2 x
    f-eq x = cong (λ f → f x) view≡
    view2-n-eq1 : cosmic-view-2 n ≡ 1
    view2-n-eq1 rewrite <ᵇ-self-false n = refl
    0≢1 : 0 ≢ 1
    0≢1 ()
  general-no-reconstruction :
    ¬ ( Σ[ recover ∈ (Universe (Fin n) ℕ Cosmos-C → Cosmos) ]
        ( (∀ u v → stream u ≈obs stream v → recover u ≈ᶜ recover v) ×
          (∀ cos → recover (projCosmos n obs-selector cos) ≈ᶜ cos) ) )
  general-no-reconstruction (f , pres , prop) =
    ¬cosmos1≈cosmos2 (≈ᶜ-trans (≈ᶜ-sym (prop cosmos-instance-1))
                             (≈ᶜ-trans (pres _ _ finite-obs-equiv)
                                       (prop cosmos-instance-2)))
