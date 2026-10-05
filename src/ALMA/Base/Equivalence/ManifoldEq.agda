------------------------------------------------------------------------
-- Local charts as a LayeredEqGen instance, single-directional
-- ManifoldStructure carries support-mono (single-directional support
-- inclusion under restriction), matching standard manifolds where
-- restricting a chart shrinks its support
-- ManifoldEq is a preorder, not an equivalence relation, because the
-- layer relation is single-directional
--
-- 局部坐标卡作为 LayeredEqGen 实例，单向
-- ManifoldStructure 携带 support-mono（限制下的单向支撑包含），
-- 匹配标准流形中限制坐标卡会缩小支撑
-- ManifoldEq 是预序，不是等价关系，因为 layer 关系是单向的
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.ManifoldEq where

open import Agda.Primitive using (lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; subst)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Nullary using (¬_)
open import Data.Nat.Base as ℕ using (z<s)
open import Data.Product.Base using (proj₁; proj₂; _×_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Base using (ℚ; _+_; _-_; -_; _⊔_; _⊓_; _<_; 0ℚ; 1ℚ; *<*)
open import Data.Integer.Base as ℤ using (-<+; +<+)
open import Data.Rational.Properties
  using (+-identityʳ; +-monoʳ-<; ≤-total; <-trans; <-irrefl; ≤-<-trans; <-≤-trans
        ; p≤p⊔q; p≤q⊔p; p⊓q≤p; p⊓q≤q; p≤q⇒p⊓q≡p; p≥q⇒p⊓q≡q; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p)

open import ALMA.Base.IndexedMType using (Mᵢ)
open import ALMA.Base.Equivalence.Core using (LayeredEqGen)
open import ALMA.Base.Equivalence.Properties using (module LayeredEqGen-Properties)

------------------------------------------------------------------------
-- Manifold structure with local charts
-- Chart family, support, readout, restriction, single-directional
-- support inclusion, readout stability, and layer-preservation
-- under restriction
--
-- 带局部坐标卡的流形结构
-- 坐标卡族、支撑、读数、限制、单向支撑包含、读数稳定性、
-- 以及限制下的 layer 保持
record ManifoldStructure {a} (X : Set a) : Set (lsuc a) where
  field
    -- Model space
    --
    -- 模型空间
    E        : Set a

    -- Chart family at each point
    --
    -- 每个点处的坐标卡族
    Chart    : X → Set a

    -- Support of a chart: the points where the chart is defined
    --
    -- 坐标卡的支撑：该坐标卡有定义的点
    Support  : (x : X) → Chart x → X → Set a

    -- Coordinate readout
    --
    -- 坐标读数
    readout  : (x : X) (c : Chart x) (y : X) → Support x c y → E

    -- Restriction of a chart to a point in its support
    --
    -- 坐标卡限制到其支撑中的点
    restrict : (x : X) (c : Chart x) (y : X) (h : Support x c y) → Chart y

    -- Support inclusion under restriction: the support of the
    -- restricted chart is contained in the support of the original
    -- chart. Single-directional, matching standard manifolds
    --
    -- 限制下的支撑包含：受限坐标卡的支撑包含于原坐标卡的支撑
    -- 单向，匹配标准流形
    support-mono
      : (x y : X) (c : Chart x) (h : Support x c y)
      → ∀ w → Support y (restrict x c y h) w → Support x c w

    -- Readout is stable under restriction: the readout at a point in
    -- the restricted support agrees with the readout at the same
    -- point in the original support, after transport along support-mono
    --
    -- 读数在限制下稳定：受限支撑中某点的读数，沿 support-mono
    -- 传输到原支撑后，与原读数一致
    readout-restrict
      : (x y : X) (c : Chart x) (h : Support x c y)
      → (w : X) (hw' : Support y (restrict x c y h) w)
      → readout x c w (support-mono x y c h w hw')
        ≡ readout y (restrict x c y h) w hw'

    -- Restriction preserves layer compatibility: if two charts are
    -- compatible via f and readout agreement coh, then restricting
    -- both charts to a common point pt in the source support yields
    -- compatible restricted charts
    -- This is the naturality of restriction with respect to layer,
    -- a genuine property of standard manifolds
    --
    -- 限制保持 layer 相容性：若两个坐标卡经 f 与读出一致 coh 相容，
    -- 则把二者限制到源支撑中的公共点 pt 后，受限坐标卡仍相容
    -- 这是限制关于 layer 的自然性，是标准流形的真实性质
    layer-preserve
      : (x y : X) (c : Chart x) (d : Chart y)
      → (f : ∀ w → Support x c w → Support y d w)
      → (coh : ∀ w (hw : Support x c w)
               → readout x c w hw ≡ readout y d w (f w hw))
      → (pt : X) (hpt : Support x c pt)
      → Σ (∀ w → Support pt (restrict x c pt hpt) w
                → Support pt (restrict y d pt (f pt hpt)) w)
          (λ f' → ∀ w (hw : Support pt (restrict x c pt hpt) w)
                  → readout pt (restrict x c pt hpt) w hw
                    ≡ readout pt (restrict y d pt (f pt hpt)) w (f' w hw))

------------------------------------------------------------------------
-- ManifoldEq as a LayeredEqGen instance
-- State is a point together with a chart; observation is a point in
-- the support; step restricts the chart; layer is single-directional
-- coverage with readout agreement
-- ManifoldEq is a preorder, not an equivalence relation, because the
-- layer is single-directional
--
-- ManifoldEq 作为 LayeredEqGen 的实例
-- 状态是点加坐标卡；观察是支撑中的点；步进限制坐标卡；
-- layer 是单向覆盖加读出一致
-- ManifoldEq 是预序，不是等价关系，因为 layer 是单向的
module ManifoldEq {a} {X : Set a} (𝕄 : ManifoldStructure X) where
  open ManifoldStructure 𝕄

  -- State: point plus current chart
  --
  -- 状态：点加当前坐标卡
  State : Set a
  State = Σ X Chart

  -- Observation: points in the support of the current chart
  --
  -- 观察：当前坐标卡支撑中的点
  Obs : State → Set a
  Obs (x , c) = Σ X (Support x c)

  -- Step: restrict the chart to a point in its support
  --
  -- 步进：把坐标卡限制到其支撑中的点
  step : (s : State) → Obs s → State
  step (x , c) (y , h) = (y , restrict x c y h)

  -- Layer: single-directional coverage with readout agreement
  -- f maps the support of the source chart into the support of the
  -- target chart, preserving readout
  --
  -- layer：单向覆盖加读出一致
  -- f 将源坐标卡的支撑映入目标坐标卡的支撑，保持读数
  layer : State → State → Set a
  layer (x , c) (y , d) =
    Σ (∀ w → Support x c w → Support y d w)
      (λ f → ∀ w (hw : Support x c w)
             → readout x c w hw ≡ readout y d w (f w hw))

  -- Observation mapping: keeps the point, transports the support
  -- proof from source to target along the coverage
  --
  -- 观察映射：保持点不变，沿覆盖把支撑证明从源搬到目标
  obs-map : (s t : State) → layer s t → Obs s → Obs t
  obs-map (x , c) (y , d) l (w , hw) = (w , proj₁ l w hw)

  -- Reflexivity: identity coverage with refl readout agreement
  --
  -- 自反性：恒等覆盖，读出一致为 refl
  layer-refl : ∀ s → layer s s
  layer-refl (x , c) = (λ w hw → hw) , (λ w hw → refl)

  -- Transitivity: compose coverages and chain readout agreements
  --
  -- 传递性：复合覆盖，串联读出一致
  layer-trans : ∀ {s t u} → layer s t → layer t u → layer s u
  layer-trans {x , c} {y , d} {z , e} (f₁ , coh₁) (f₂ , coh₂) =
    (λ w hw → f₂ w (f₁ w hw))
    , (λ w hw → trans (coh₁ w hw) (coh₂ w (f₁ w hw)))

  -- layer is a preorder: reflexive and transitive, with propositional
  -- equality as the underlying equivalence
  --
  -- layer 是预序：自反、传递，以命题相等为底层等价关系
  layer-isPreorder : IsPreorder _≡_ layer
  layer-isPreorder = record
    { isEquivalence = record
      { refl  = λ {x} → refl
      ; sym   = λ {x} {y} → sym
      ; trans = λ {x} {y} {z} → trans
      }
    ; reflexive = λ { {x} refl → layer-refl x }
    ; trans     = λ {x} {y} {z} → layer-trans {x} {y} {z}
    }

  -- obs-map fixes observations along layer-refl
  --
  -- obs-map 沿 layer-refl 固定观察
  obs-refl-map : ∀ s (obs : Obs s)
               → obs-map s s (layer-refl s) obs ≡ obs
  obs-refl-map (x , c) (w , hw) = refl

  -- obs-map composes along layer-trans
  -- The composite coverage is definitionally f₂ ∘ f₁, so the
  -- equality is refl
  --
  -- obs-map 沿 layer-trans 复合
  -- 复合覆盖定义上为 f₂ ∘ f₁，故相等为 refl
  obs-trans-map : ∀ {s t u} (l : layer s t) (m : layer t u) (obs : Obs s)
                → obs-map t u m (obs-map s t l obs)
                  ≡ obs-map s u (layer-trans l m) obs
  obs-trans-map {x , c} {y , d} {z , e} l m (w , hw) = refl

  -- ManifoldEq as LayeredEqGen
  --
  -- ManifoldEq 作为 LayeredEqGen
  ManifoldEq : State → State → Set _
  ManifoldEq = LayeredEqGen Obs step layer obs-map

  -- Preorder, obtained from the generic properties module
  --
  -- 预序，由通用性质模块给出
  ManifoldEq-isPreorder : IsPreorder _≡_ ManifoldEq
  ManifoldEq-isPreorder =
    LayeredEqGen-Properties.le-isPreorder
      layer-refl
      (λ {s} {t} {u} → layer-trans {s} {t} {u})
      obs-refl-map
      (λ l m obs → obs-trans-map l m obs)

  -- Layer is stable under step: restricting two compatible charts to
  -- a common point yields compatible charts, by layer-preserve
  --
  -- layer 在 step 下稳定：把两个相容坐标卡限制到公共点后仍相容，
  -- 由 layer-preserve 给出
  layer-stable
    : ∀ {s t} (l : layer s t) (pt : X)
      (hpt : Support (proj₁ s) (proj₂ s) pt)
    → layer (step s (pt , hpt)) (step t (obs-map s t l (pt , hpt)))
  layer-stable {s = x , c} {t = y , d} (f , coh) pt hpt =
    layer-preserve x y c d f coh pt hpt

------------------------------------------------------------------------
-- Concrete ℚ instance
-- Charts are open intervals (a, b); support is membership; readout
-- is the identity; restriction intersects the chart with the unit
-- neighbourhood (y - 1, y + 1) of the restriction point
-- The support-mono direction is interval inclusion, matching the
-- single-directional nature of the layer
--
-- ℚ 上的具体实例
-- 坐标卡是开区间 (a, b)；支撑是成员关系；读数是恒等；
-- 限制取坐标卡与限制点单位邻域 (y - 1, y + 1) 的交
-- support-mono 方向是区间包含，匹配 layer 的单向性
private
  -- -1 < 0, 0 < 1 in ℚ, lifted from ℤ
  --
  -- ℚ 中的 -1 < 0 与 0 < 1，由 ℤ 提升
  -1<0 : (- 1ℚ) < 0ℚ
  -1<0 = *<* ℤ.-<+

  0<1 : 0ℚ < 1ℚ
  0<1 = *<* (ℤ.+<+ ℕ.z<s)

  -- y - 1 < y and y < y + 1, by monotonicity of addition
  --
  -- y - 1 < y 与 y < y + 1，由加法单调性得到
  y-1<y : ∀ y → y - 1ℚ < y
  y-1<y y = subst (λ z → y - 1ℚ < z) (+-identityʳ y) (+-monoʳ-< y -1<0)

  y<y+1 : ∀ y → y < y + 1ℚ
  y<y+1 y = subst (λ z → z < y + 1ℚ) (+-identityʳ y) (+-monoʳ-< y 0<1)

  -- Strict bounds for ⊔ and ⊓, obtained by case analysis on ≤-total
  --
  -- ⊔ 与 ⊓ 的严格界，由 ≤-total 分情形得到
  ⊔-< : ∀ {a b c} → a < c → b < c → a ⊔ b < c
  ⊔-< {a} {b} {c} a<c b<c with ≤-total a b
  ... | inj₁ a≤b = subst (λ z → z < c) (sym (p≤q⇒p⊔q≡q a≤b)) b<c
  ... | inj₂ b≤a = subst (λ z → z < c) (sym (p≥q⇒p⊔q≡p b≤a)) a<c

  <-⊓ : ∀ {a b c} → a < b → a < c → a < b ⊓ c
  <-⊓ {a} {b} {c} a<b a<c with ≤-total b c
  ... | inj₁ b≤c = subst (λ z → a < z) (sym (p≤q⇒p⊓q≡p b≤c)) a<b
  ... | inj₂ c≤b = subst (λ z → a < z) (sym (p≥q⇒p⊓q≡q c≤b)) a<c

  -- Combination: a < b, a < d, c < b, c < d imply a ⊔ c < b ⊓ d
  --
  -- 组合：a < b、a < d、c < b、c < d 蕴含 a ⊔ c < b ⊓ d
  max-<min : ∀ {a b c d} → a < b → a < d → c < b → c < d
           → a ⊔ c < b ⊓ d
  max-<min a<b a<d c<b c<d = <-⊓ (⊔-< a<b c<b) (⊔-< a<d c<d)

-- The concrete ManifoldStructure on ℚ
--
-- ℚ 上的具体 ManifoldStructure
ℚManifold : ManifoldStructure ℚ
ℚManifold = record
  { E       = ℚ
  ; Chart   = λ _ → Σ ℚ (λ a → Σ ℚ (λ b → a < b))
  ; Support = λ _ (a , b , _) y → (a < y) × (y < b)
  ; readout = λ _ _ y _ → y
  ; restrict = λ _ (a , b , _) y (ay , yb) →
      let a' = a ⊔ (y - 1ℚ)
          b' = b ⊓ (y + 1ℚ)
      in a' , b' ,
         max-<min (<-trans ay yb) (<-trans ay (y<y+1 y))
                  (<-trans (y-1<y y) yb) (<-trans (y-1<y y) (y<y+1 y))
  ; support-mono = λ _ y (a , b , _) _ w (h₁ , h₂) →
      ≤-<-trans (p≤p⊔q a (y - 1ℚ)) h₁
      , <-≤-trans h₂ (p⊓q≤p b (y + 1ℚ))
  ; readout-restrict = λ _ _ _ _ _ _ → refl
  ; layer-preserve = λ _ _ (a , b , _) (c' , d' , _) f coh pt (pt-a , pt-b) →
      let a'  = a ⊔ (pt - 1ℚ)
          b'  = b ⊓ (pt + 1ℚ)
          c'' = c' ⊔ (pt - 1ℚ)
          d'' = d' ⊓ (pt + 1ℚ)
          f' : ∀ w → (a' < w) × (w < b') → (c'' < w) × (w < d'')
          f' w (h₁ , h₂) =
            let a<w    = ≤-<-trans (p≤p⊔q a (pt - 1ℚ)) h₁
                w<b    = <-≤-trans h₂ (p⊓q≤p b (pt + 1ℚ))
                c'<w , w<d' = f w (a<w , w<b)
                pt-1<w = ≤-<-trans (p≤q⊔p a (pt - 1ℚ)) h₁
                w<pt+1 = <-≤-trans h₂ (p⊓q≤q b (pt + 1ℚ))
            in ⊔-< c'<w pt-1<w , <-⊓ w<d' w<pt+1
      in f' , (λ w hw → refl)
  }

------------------------------------------------------------------------
-- Obstruction: ManifoldEq is not symmetric on ℚManifold
-- Uses the interval (0, 1) and (-1, 1): the former is contained in
-- the latter, but not vice versa. The witness is w = 0
--
-- 障碍：ManifoldEq 在 ℚManifold 上不对称
-- 取区间 (0, 1) 与 (-1, 1)：前者包含于后者，反之不成立。见证点 w = 0
module ℚManifoldEqObstruction where
  open ManifoldEq ℚManifold
  open ManifoldStructure ℚManifold

  -- Reflexivity of ManifoldEq, by guarded coinduction
  --
  -- ManifoldEq 的自反性，由受守卫的余归纳给出
  ManifoldEq-refl : ∀ s → ManifoldEq s s
  ManifoldEq-refl (x , c) .Mᵢ.fst =
    (λ w hw → hw) , (λ w hw → refl)
  ManifoldEq-refl (x , c) .Mᵢ.snd (w , hw) =
    ManifoldEq-refl (w , restrict x c w hw)

  -- Two states: s = (1/2, (0, 1)), t = (0, (-1, 1))
  -- The chart (0, 1) is contained in (-1, 1), so s ≤ t
  --
  -- 两个状态：s = (1/2, (0, 1))，t = (0, (-1, 1))
  -- 坐标卡 (0, 1) 包含于 (-1, 1)，故 s ≤ t
  private
    -1<1 : - 1ℚ < 1ℚ
    -1<1 = <-trans -1<0 0<1

    s : State
    s = 1ℚ , (0ℚ , 1ℚ , 0<1)

    t : State
    t = 0ℚ , (- 1ℚ , 1ℚ , -1<1)

  -- Generic layer-to-ManifoldEq, by guarded coinduction on the layer
  -- witness. This is the coinductive closure of layer-preserve
  --
  -- 从 layer 到 ManifoldEq 的泛型构造，对 layer 见证做受守卫的
  -- 余归纳。这是 layer-preserve 的余归纳闭包
  layer→ManifoldEq : ∀ {s t} → layer s t → ManifoldEq s t
  layer→ManifoldEq {s = x , c} {t = y , d} l .Mᵢ.fst = l
  layer→ManifoldEq {s = x , c} {t = y , d} l .Mᵢ.snd (w , hw) =
    layer→ManifoldEq
      (layer-preserve x y c d (proj₁ l) (proj₂ l) w hw)

  -- ManifoldEq s t: the coverage maps (0,1) into (-1,1) preserving readout
  --
  -- ManifoldEq s t：(0,1) 映入 (-1,1) 且保持读数
  Mst : ManifoldEq s t
  Mst = layer→ManifoldEq
    ( (λ w (h₁ , h₂) → <-trans -1<0 h₁ , h₂)
    , (λ w hw → refl) )

  -- ManifoldEq is not symmetric on this instance: applying symmetry
  -- to Mst yields a coverage of (-1,1) into (0,1), which would send
  -- w = 0 with proof (-1 < 0, 0 < 1) to a proof of 0 < 0
  --
  -- ManifoldEq 在该实例上不对称：把对称性应用于 Mst 得到从
  -- (-1,1) 到 (0,1) 的覆盖，它会把 w = 0 连同证明 (-1 < 0, 0 < 1)
  -- 送到 0 < 0 的证明
  not-symmetric : ¬ (∀ {s t} → ManifoldEq s t → ManifoldEq t s)
  not-symmetric sym =
    let l = proj₁ ((sym Mst) .Mᵢ.fst)
        h = l 0ℚ (-1<0 , 0<1)
    in <-irrefl refl (proj₁ h)
