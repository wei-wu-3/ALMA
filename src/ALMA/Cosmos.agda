{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：宇宙结构、投影与不可重构定理
哲学意义：从存在者到存在者整体的跃迁，有限视角与无限本质的关系
-}
module ALMA.Cosmos where
open import ALMA.Beings public
-- 不可消减性：宇宙的本质恒常不变
record IsIndestructible {I A C : Set} (essence : C) (stream : Stream ((I → A) × C)) : Set where
  field
    essencePermanent : Always (λ x → proj₂ x ≡ essence) stream
open IsIndestructible public
-- 宇宙：索引化偶性的存在者整体
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
-- 投影：从宇宙到有限视角的降维（认识论操作）
module Proj (n : ℕ) where
  Selector : Set
  Selector = Fin n → ℕ
  proj-stream : ∀ {C} → Stream ((ℕ → ℕ) × C) → Selector → Stream ((Fin n → ℕ) × C)
  proj-stream s sel .Stream.head = (λ i → proj₁ (Stream.head s) (sel i)) , proj₂ (Stream.head s)
  proj-stream s sel .Stream.tail = proj-stream (Stream.tail s) sel
  private
    core-const : ∀ {C} s sel (c : C) → Always (λ x → proj₂ x ≡ c) s →
                 Always (λ x → proj₂ x ≡ c) (proj-stream s sel)
    core-const s sel c al .Always.head = al .Always.head
    core-const s sel c al .Always.tail = core-const (Stream.tail s) sel c (al .Always.tail)
  project : ∀ {C} → Universe ℕ ℕ C → Selector → Universe (Fin n) ℕ C
  project cos sel = record
    { essence = univ-core cos
    ; stream = proj-stream (stream cos) sel
    ; indestruct = record
        { essencePermanent = core-const (stream cos) sel (univ-core cos)
                               (essencePermanent (indestruct cos)) }
    }
  project-preserves-core : ∀ {C} (cos : Universe ℕ ℕ C) sel →
                           essence (project cos sel) ≡ univ-core cos
  project-preserves-core cos sel = refl
module MergeSelectors (n m : ℕ) where
  open Proj (n + m) using (project)
  merge : (Fin n → ℕ) → (Fin m → ℕ) → Fin (n + m) → ℕ
  merge sel₁ sel₂ i = [_,_] sel₁ sel₂ (splitAt n i)
  merge-preserves-core : ∀ {C} (cos : Universe ℕ ℕ C) (sel₁ : Fin n → ℕ) (sel₂ : Fin m → ℕ) →
                         essence (project cos (merge sel₁ sel₂)) ≡ univ-core cos
  merge-preserves-core cos sel₁ sel₂ = refl
module Simple where
  TrivialUniverse : Set
  TrivialUniverse = Universe ℕ ℕ String
-- Cosmos：唯一本质的宇宙
data Cosmos-C : Set where
  CosmicEssence : Cosmos-C
open Cosmos-C public
Cosmos : Set
Cosmos = Universe ℕ ℕ Cosmos-C
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
≈ᶜ-trans eq1 eq2 = record { essence≈ = trans (essence≈ eq1) (essence≈ eq2)
                          ; stream≈  = ≈-trans (stream≈ eq1) (stream≈ eq2) }
cosmos-essence-unique : ∀ (cos1 cos2 : Cosmos) → essence cos1 ≡ essence cos2
cosmos-essence-unique cos1 cos2 with essence cos1 | essence cos2
... | CosmicEssence | CosmicEssence = refl
cosmos-initial : (ℕ → ℕ) → Cosmos
cosmos-initial o = record
  { essence = CosmicEssence
  ; stream = constStream (o , CosmicEssence)
  ; indestruct = record { essencePermanent = constStream-always-gen (o , CosmicEssence) refl }
  }
-- 嵌入：从有限视角回升到宇宙（与投影形成伴随）
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
  proj-extend-obs-equiv : ∀ {n} (s : Stream ((Fin n → ℕ) × Cosmos-C))
                         → _ ≈obs s
  proj-extend-obs-equiv {n} s = helper
    where
      open Proj n
      helper : proj-stream (embedToCosmos s) (λ i → toℕ i) ≈obs s
      helper .head-obs-equiv i =
        trans refl
        (trans refl
        (trans (cong (maybe (proj₁ (Stream.head s)) 0) (toFin-toℕ i))
        refl))
      helper .head-essence-equiv = refl
      helper .tail-equiv = proj-extend-obs-equiv (Stream.tail s)
  ≈ᵁ-implies-≈obs : ∀ {n} {u1 u2 : Universe (Fin n) ℕ Cosmos-C} → u1 ≈ᵁ u2 → stream u1 ≈obs stream u2
  ≈ᵁ-implies-≈obs {n} eq = helper {n} (eq .stream≈)
    where
      helper : ∀ {n} {s t : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈ t → s ≈obs t
      helper eq .head-obs-equiv i = cong (λ f → f i) (cong proj₁ (eq ._≈_.head≈))
      helper eq .head-essence-equiv = cong proj₂ (eq ._≈_.head≈)
      helper eq .tail-equiv = helper (eq ._≈_.tail≈)
universe-to-cosmos : ∀ {n} → Universe (Fin n) ℕ Cosmos-C → Cosmos
universe-to-cosmos u = record
  { essence    = essence u
  ; stream     = embedToCosmos (stream u)
  ; indestruct = record { essencePermanent = extend-always (essencePermanent (indestruct u)) }
  }
-- 嵌入唯一性：任意两个有限观察等价的宇宙，来自同一Cosmos的投影
universe-embedding-uniqueness :
  ∀ {n} (u1 u2 : Universe (Fin n) ℕ Cosmos-C)
  → stream u1 ≈obs stream u2
  → Σ Cosmos (λ cos → 
      (Σ (Fin n → ℕ) (λ sel1 → stream (Proj.project n cos sel1) ≈obs stream u1)) 
      × 
      (Σ (Fin n → ℕ) (λ sel2 → stream (Proj.project n cos sel2) ≈obs stream u2))
    )
universe-embedding-uniqueness {n} u1 u2 stream-obs =
  (cos , ((sel1 , bisim1) , (sel2 , bisim2)))
  where
    open Proj n
    cos : Cosmos
    cos = universe-to-cosmos u1
    sel1 : Fin n → ℕ
    sel1 i = toℕ i
    sel2 : Fin n → ℕ
    sel2 i = toℕ i
    bisim1 : stream (project cos sel1) ≈obs stream u1
    bisim1 = proj-extend-obs-equiv (stream u1)
    bisim2 : stream (project cos sel2) ≈obs stream u2
    bisim2 = trans-≈obs (proj-extend-obs-equiv (stream u1)) stream-obs
module Framework where
  ultimate-projection : ∀ {n} (u : Universe (Fin n) ℕ Cosmos-C)
                        → Σ[ cos ∈ Cosmos ]
                          ( Σ[ sel ∈ (Fin n → ℕ) ]
                              (stream (Proj.project n cos sel) ≈obs stream u) )
  ultimate-projection u =
    (universe-to-cosmos u , ( (λ i → toℕ i) , proj-extend-obs-equiv (stream u) ))
-- 不可重构定理：有限观察无法重构唯一无限宇宙
module NoReconstruction where
  open Proj 1
  obs-selector : Fin 1 → ℕ
  obs-selector _ = 0
  cosmic-view-1 cosmic-view-2 : ℕ → ℕ
  cosmic-view-1 _ = 0
  cosmic-view-2 n = if n ≡ᵇ 0 then 0 else (if n ≡ᵇ 1 then 1 else 0)
  cosmos-instance-1 : Cosmos
  cosmos-instance-1 = cosmos-initial cosmic-view-1
  cosmos-instance-2 : Cosmos
  cosmos-instance-2 = cosmos-initial cosmic-view-2
  ¬cosmos-instance-1≈ᶜcosmos-instance-2 : ¬ (cosmos-instance-1 ≈ᶜ cosmos-instance-2)
  ¬cosmos-instance-1≈ᶜcosmos-instance-2 eq = 0≢1 (f-eq 1)
    where
    head≡ : Stream.head (stream cosmos-instance-1) ≡ Stream.head (stream cosmos-instance-2)
    head≡ = stream≈ eq ._≈_.head≈
    view≡ : cosmic-view-1 ≡ cosmic-view-2
    view≡ = cong proj₁ head≡
    f-eq : ∀ x → cosmic-view-1 x ≡ cosmic-view-2 x
    f-eq x = cong (λ f → f x) view≡
    0≢1 : 0 ≢ 1
    0≢1 ()
  finite-obs-equiv : stream (project cosmos-instance-1 obs-selector) ≈obs stream (project cosmos-instance-2 obs-selector)
  finite-obs-equiv .head-obs-equiv i = refl
  finite-obs-equiv .head-essence-equiv = refl
  finite-obs-equiv .tail-equiv = finite-obs-equiv
  no-finite-reconstruction :
    ¬ ( Σ[ recover ∈ (Universe (Fin 1) ℕ Cosmos-C → Cosmos) ]
        ( (∀ u v → stream u ≈obs stream v → recover u ≈ᶜ recover v) ×
          (∀ cos → recover (project cos obs-selector) ≈ᶜ cos) ) )
  no-finite-reconstruction (f , pres , prop) =
    ¬cosmos-instance-1≈ᶜcosmos-instance-2 (≈ᶜ-trans (≈ᶜ-sym (prop cosmos-instance-1))
                             (≈ᶜ-trans (pres _ _ finite-obs-equiv)
                                       (prop cosmos-instance-2)))
-- 嵌入-投影伴随的右映射：宇宙等价蕴含有限观察等价
≈obs-sym : ∀ {n} {s t : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs t → t ≈obs s
≈obs-sym eq ._≈obs_.head-obs-equiv i = sym (eq ._≈obs_.head-obs-equiv i)
≈obs-sym eq ._≈obs_.head-essence-equiv = sym (eq ._≈obs_.head-essence-equiv)
≈obs-sym eq ._≈obs_.tail-equiv = ≈obs-sym (eq ._≈obs_.tail-equiv)
proj-embed-unit : ∀ {n} (u : Universe (Fin n) ℕ Cosmos-C) →
                  stream (Proj.project n (universe-to-cosmos u) (λ i → toℕ i)) ≈obs stream u
proj-embed-unit u = proj-extend-obs-equiv (stream u)
embed-proj-counit : ∀ {n} (cos : Cosmos) (sel : Fin n → ℕ) →
                    stream (Proj.project n cos sel) ≈obs
                    stream (Proj.project n (universe-to-cosmos (Proj.project n cos sel)) (λ i → toℕ i))
embed-proj-counit {n} cos sel = ≈obs-sym (proj-extend-obs-equiv {n} (stream (Proj.project n cos sel)))
project-≈ᵁ : ∀ {n} (sel : Fin n → ℕ) {cos1 cos2 : Cosmos} → cos1 ≈ᶜ cos2 → Proj.project n cos1 sel ≈ᵁ Proj.project n cos2 sel
project-≈ᵁ {n} sel {cos1} {cos2} eq = record
  { essence≈ = trans (Proj.project-preserves-core n cos1 sel)
                     (trans (essence≈ eq)
                            (sym (Proj.project-preserves-core n cos2 sel)))
  ; stream≈ = proj-stream-≈ (stream≈ eq)
  }
  where
    proj-stream-≈ : {s1 s2 : Stream ((ℕ → ℕ) × Cosmos-C)} → s1 ≈ s2 →
                    Proj.proj-stream n {C = Cosmos-C} s1 sel ≈ Proj.proj-stream n {C = Cosmos-C} s2 sel
    proj-stream-≈ eq ._≈_.head≈ = cong (λ x → (λ i → proj₁ x (sel i)) , proj₂ x) (_≈_.head≈ eq)
    proj-stream-≈ eq ._≈_.tail≈ = proj-stream-≈ (_≈_.tail≈ eq)
proj-embed-adjunction : ∀ {n} (u : Universe (Fin n) ℕ Cosmos-C) (cos : Cosmos) →
                        universe-to-cosmos u ≈ᶜ cos → stream u ≈obs stream (Proj.project n cos (λ i → toℕ i))
proj-embed-adjunction {n} u cos eq = 
  trans-≈obs (≈obs-sym (proj-embed-unit u))
           (≈ᵁ-implies-≈obs (project-≈ᵁ (λ i → toℕ i) eq))
-- 不可重构性的推论：to 方向不成立
module ToDirectionFalse where
  open NoReconstruction
  to-false : ¬ (∀ {n} (u : Universe (Fin n) ℕ Cosmos-C) (cos : Cosmos) →
                stream u ≈obs stream (Proj.project n cos (λ i → toℕ i)) → universe-to-cosmos u ≈ᶜ cos)
  to-false h = no-finite-reconstruction (recover , pres , prop)
    where
      recover : Universe (Fin 1) ℕ Cosmos-C → Cosmos
      recover = universe-to-cosmos
      pres : ∀ u v → stream u ≈obs stream v → recover u ≈ᶜ recover v
      pres u v eq = h {n = 1} u (recover v) (trans-≈obs eq (≈obs-sym (proj-embed-unit {n = 1} v)))
      prop : ∀ cos → recover (Proj.project 1 cos obs-selector) ≈ᶜ cos
      prop cos = h {n = 1} (Proj.project 1 cos obs-selector) cos
                    (proj-embed-equiv cos)
        where
          proj-embed-equiv : ∀ cos → stream (Proj.project 1 cos obs-selector) ≈obs
                                      stream (Proj.project 1 cos (λ i → toℕ i))
          proj-embed-equiv cos = helper (stream cos)
            where
              helper : ∀ (s : Stream ((ℕ → ℕ) × Cosmos-C)) →
                       Proj.proj-stream 1 {C = Cosmos-C} s obs-selector ≈obs
                       Proj.proj-stream 1 {C = Cosmos-C} s (λ i → toℕ i)
              helper s ._≈obs_.head-obs-equiv i =
                let
                  i≡zero : i ≡ zero
                  i≡zero = fin1-unique i
                in
                trans (cong (proj₁ (Stream.head s) ∘ obs-selector) i≡zero)
                      (sym (cong (proj₁ (Stream.head s) ∘ (λ i → toℕ i)) i≡zero))
              helper s ._≈obs_.head-essence-equiv = refl
              helper s ._≈obs_.tail-equiv = helper (Stream.tail s)
