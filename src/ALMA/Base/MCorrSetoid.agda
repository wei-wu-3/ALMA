------------------------------------------------------------------------
-- Setoid-parameterised carried correspondences (pilot slice)
--
-- MCorr hard-wires propositional equality _≡_ in three places:
--   FiberAdj η/ε, the bisimulation _≈M_.here-eq, and the FMap graph
--   witness / relocation.  This module is the decisive feasibility
--   slice for rebuilding Cosmos on the M base: it replaces the edge/
--   label equality by a CARRIED equivalence on the manifest carrier,
--   without using K and without dependent subst.
--
-- Contents
--   EqOn        an equivalence bundle whose carrier is a MANIFEST
--               parameter (so it sits directly on A x / E x a y)
--   FiberAdjˢ   fibre adjunction between two EqOn carriers (η/ε at _≈_)
--   idAdjˢ / symAdjˢ / compAdjˢ   identity, symmetry, composition
--   _≈Mˢ_       coinductive bisimulation over label/edge equivalences
--   propEqOn / toAdjˢ / fromAdjˢ   the propositional FiberAdj is an
--               INSTANCE (the _≡_ kernel loses nothing)
--   Pilot       a genuinely non-propositional equivalence (a Bool tag
--               that is ignored): two M-trees whose labels are equal
--               in EqOn but NOT propositionally equal are related by
--               _≈Mˢ_; the old _≈M_ cannot relate them.  The same EqOn
--               hosts a container position adjunction whose fro is the
--               old contravariant onPos and whose η/ε are the carried
--               round-trips replacing pts-compat/onActP.
--
-- setoid 参数化的携带式对应（试点切片）
--
-- MCorr 在三处硬编码命题相等 _≡_：FiberAdj 的 η/ε、互模拟 _≈M_ 的
-- here-eq、FMap 图见证/重定位。本模块是"在 M 底座上重建 Cosmos"的
-- 决定性可行性切片：把边/标签等价替换为建立在外显载体上的、被携带
-- 的等价关系，不用 K，也不用依赖 subst。
--
-- 内容
--   EqOn        等价束，其载体是外显参数（故直接坐落在 A x /
--               E x a y 上）
--   FiberAdjˢ   两个 EqOn 载体间的纤维伴随（η/ε 建立在 _≈_ 上）
--   idAdjˢ / symAdjˢ / compAdjˢ   恒等、对称、复合
--   _≈Mˢ_       标签/边等价上的余归纳互模拟
--   propEqOn / toAdjˢ / fromAdjˢ   命题版 FiberAdj 是一个实例（_≡_
--               内核一无所失）
--   Pilot       真正非命题的等价（忽略 Bool 标签）：两棵 M 树的标签
--               在 EqOn 下相等但命题不相等，却被 _≈Mˢ_ 联系；旧 _≈M_
--               无法联系二者。同一 EqOn 承载一个容器位置伴随，其 fro
--               即旧反变 onPos，η/ε 即取代 pts-compat/onActP 的携带
--               式往返律。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrSetoid where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core as Prop using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥)
open import Function.Base using (id; _∘_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product.Base using (_×_; proj₁; proj₂)

open import ALMA.Base.MCorr using (M; FiberAdj; _⍮_)

------------------------------------------------------------------------
-- Equivalence on a manifest carrier
-- This is stdlib's Setoid with the Carrier made a module parameter, so
-- an EqOn (A x) is by construction an equivalence on exactly A x with
-- no coercion between Setoid.Carrier and A x.
--
-- 外显载体上的等价
-- 即 stdlib Setoid 把 Carrier 提为模块参数，故 EqOn (A x) 按构造正是
-- A x 上的等价，无需在 Setoid.Carrier 与 A x 间强制转换。
------------------------------------------------------------------------
record EqOn {a ℓ : Level} (Carrier : Set a) : Set (lsuc (a ⊔ ℓ)) where
  infix 4 _≈_
  field
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_
  open IsEquivalence isEquivalence public using (refl; sym; trans; reflexive)
open EqOn public

------------------------------------------------------------------------
-- Fibre adjunction between two carriers with carried equivalences
-- η/ε live at the carried _≈_, not at propositional equality.  The
-- congruence fields to-cong/fro-cong are the naturality / hom-action
-- coherence (onActP), carried as data.
--
-- 两个载体间、在携带等价上的纤维伴随
-- η/ε 建立在携带的 _≈_ 上而非命题相等。同余字段 to-cong/fro-cong 即
-- 作为数据携带的自然性/态射作用相干（onActP）。
------------------------------------------------------------------------
record FiberAdjˢ {c d ℓc ℓd : Level}
                {P : Set c} {R : Set d}
                (EP : EqOn {ℓ = ℓc} P) (ER : EqOn {ℓ = ℓd} R)
       : Set (c ⊔ d ⊔ ℓc ⊔ ℓd) where
  private
    module EP = EqOn EP
    module ER = EqOn ER
  field
    to       : R → P
    fro      : P → R
    to-cong  : ∀ {r r'} → r ER.≈ r' → to r EP.≈ to r'
    fro-cong : ∀ {p p'} → p EP.≈ p' → fro p ER.≈ fro p'
    η        : (r : R) → fro (to r) ER.≈ r
    ε        : (p : P) → to (fro p) EP.≈ p
open FiberAdjˢ public

-- Identity adjunction
--
-- 恒等伴随
idAdjˢ : ∀ {c ℓ} {P : Set c} (E : EqOn {ℓ = ℓ} P) → FiberAdjˢ E E
idAdjˢ E = record
  { to       = id
  ; fro      = id
  ; to-cong  = λ e → e
  ; fro-cong = λ e → e
  ; η        = λ _ → EqOn.refl E
  ; ε        = λ _ → EqOn.refl E
  }

-- Symmetry swaps the two fibres
--
-- 对称性交换两根纤维
symAdjˢ : ∀ {c d ℓc ℓd} {P : Set c} {R : Set d}
          {EP : EqOn {ℓ = ℓc} P} {ER : EqOn {ℓ = ℓd} R}
        → FiberAdjˢ EP ER → FiberAdjˢ ER EP
symAdjˢ a = record
  { to       = fro a
  ; fro      = to a
  ; to-cong  = fro-cong a
  ; fro-cong = to-cong a
  ; η        = ε a
  ; ε        = η a
  }

-- Composition of fibre adjunctions
--
-- 纤维伴随的复合
compAdjˢ : ∀ {r g h ℓr ℓg ℓh : Level}
           {R : Set r} {G : Set g} {H : Set h}
           (ER : EqOn {ℓ = ℓr} R)
           (EG : EqOn {ℓ = ℓg} G)
           (EH : EqOn {ℓ = ℓh} H)
         → FiberAdjˢ EG ER → FiberAdjˢ EH EG → FiberAdjˢ EH ER
compAdjˢ ER EG EH a₁ a₂ = record
  { to       = to a₂ ∘ to a₁
  ; fro      = fro a₁ ∘ fro a₂
  ; to-cong  = to-cong a₂ ∘ to-cong a₁
  ; fro-cong = fro-cong a₁ ∘ fro-cong a₂
  ; η = λ r → EqOn.trans ER
               (fro-cong a₁ (η a₂ (to a₁ r)))
               (η a₁ r)
  ; ε = λ p → EqOn.trans EH
               (to-cong a₂ (ε a₁ (fro a₂ p)))
               (ε a₂ p)
  }

------------------------------------------------------------------------
-- Coinductive bisimulation over carried label/edge equivalences
--
-- 在携带的标签/边等价上的余归纳互模拟
------------------------------------------------------------------------
record _≈Mˢ_ {i a b ℓa ℓe : Level}
             {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b}
             (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
             (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
             {x : I} (t s : M A E x)
       : Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe) where
  coinductive
  field
    here-eq : EqOn._≈_ (≈A x) (M.here t) (M.here s)
    below-eq : ∀ (y : I)
      → Σ (FiberAdjˢ (≈E x (M.here s) y) (≈E x (M.here t) y)) λ adj
      →   (∀ (e₁ : E x (M.here t) y)
           → _≈Mˢ_ ≈A ≈E (M.below t y e₁)
                           (M.below s y (to adj e₁)))
        × (∀ (e₂ : E x (M.here s) y)
           → _≈Mˢ_ ≈A ≈E (M.below s y e₂)
                           (M.below t y (fro adj e₂)))
open _≈Mˢ_ public

-- Reflexivity
--
-- 自反性
≈Mˢ-refl : ∀ {i a b ℓa ℓe : Level}
             {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b}
             (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
             (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
             {x : I} (t : M A E x) → _≈Mˢ_ ≈A ≈E t t
≈Mˢ-refl ≈A ≈E t .here-eq = EqOn.refl (≈A _)
≈Mˢ-refl ≈A ≈E {x = x} t .below-eq y =
    idAdjˢ (≈E x (M.here t) y)
  , ( (λ e₁ → ≈Mˢ-refl ≈A ≈E (M.below t y e₁))
    , (λ e₂ → ≈Mˢ-refl ≈A ≈E (M.below t y e₂)) )

------------------------------------------------------------------------
-- The propositional equivalence, and the propositional FiberAdj as an
-- instance of the setoid one.  Machine-checked evidence that the _≡_
-- kernel is exactly the EqOn special case at propositional equality.
--
-- 命题等价，以及命题版 FiberAdj 作为 setoid 版的实例。
-- 机检证据：_≡_ 内核恰为 EqOn 在命题相等处的特例。
------------------------------------------------------------------------
propEqOn : ∀ {a} (A : Set a) → EqOn {ℓ = a} A
propEqOn A = record
  { _≈_ = _≡_
  ; isEquivalence = ≡-isEquivalence
  }

fromAdjˢ : ∀ {ℓp ℓr : Level} {P : Set ℓp} {R : Set ℓr}
         → FiberAdj P R → FiberAdjˢ (propEqOn P) (propEqOn R)
fromAdjˢ a = record
  { to       = FiberAdj.to a
  ; fro      = FiberAdj.fro a
  ; to-cong  = cong (FiberAdj.to a)
  ; fro-cong = cong (FiberAdj.fro a)
  ; η        = FiberAdj.η a
  ; ε        = FiberAdj.ε a
  }

toAdjˢ : ∀ {ℓp ℓr : Level} {P : Set ℓp} {R : Set ℓr}
       → FiberAdjˢ (propEqOn P) (propEqOn R) → FiberAdj P R
toAdjˢ a = record
  { to  = to a
  ; fro = fro a
  ; η   = η a
  ; ε   = ε a
  }

------------------------------------------------------------------------
-- Systems carrying label/edge equivalences
-- A SysEq is a MCorr Sys together with a label EqOn at every index
-- and an edge EqOn on every edge fibre.  The M type itself is unchanged
-- (edges are data); only the comparison/coherence regime is carried.
--
-- 携带标签/边等价的系统
-- SysEq 即 MCorr Sys 外加每个索引上的标签 EqOn 与每根边纤维上的边
-- EqOn。M 型本身不变（边是数据）；被携带的只是比较/相干制度。
------------------------------------------------------------------------
record SysEq (i a b ℓa ℓe : Level) : Set (lsuc (i ⊔ a ⊔ ℓa ⊔ b ⊔ ℓe)) where
  field
    I   : Set i
    A   : I → Set a
    E   : (x : I) (a : A x) (y : I) → Set b
    ≈A  : (x : I) → EqOn {ℓ = ℓa} (A x)
    ≈E  : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y)
open SysEq public

------------------------------------------------------------------------
-- One-step carried correspondence over an arbitrary index layer R,
-- with the edge fibre adjunction at the carried EqOn.  The index layer
-- R stays arbitrary (it need not be propositional equality); the tree
-- action mapR only uses fro/pull and contains no equality at all.
--
-- 任意索引层 R 上的一步携带对应，边纤维伴随建立在携带的 EqOn 上。
-- 索引层 R 保持任意（不必是命题相等）；树作用 mapR 仅用 fro/pull，
-- 不含任何相等。
------------------------------------------------------------------------
record Stepˢ {i j a b c d ℓr ℓa ℓe ℓc ℓd : Level}
             (X : SysEq i a b ℓa ℓe)
             (Y : SysEq j c d ℓc ℓd)
             (R : I X → I Y → Set ℓr)
             {x : I X} {y : I Y} (r : R x y)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr ⊔ ℓa ⊔ ℓe ⊔ ℓc ⊔ ℓd) where
  field
    shapeᴿ   : A X x → A Y y
    child    : (a : A X x) (v : I Y) → Σ (I X) λ x' → R x' v
    edge-adj : (a : A X x) (v : I Y)
             → FiberAdjˢ (≈E Y y (shapeᴿ a) v)
                          (≈E X x a (proj₁ (child a v)))

  pullˢ : (a : A X x) (v : I Y) (q : E Y y (shapeᴿ a) v)
        → Σ (I X) λ x' → Σ (E X x a x') λ e → R x' v
  pullˢ a v q =
    let x' , r' = child a v
    in x' , fro (edge-adj a v) q , r'
open Stepˢ public

record Morphˢ {i j a b c d ℓr ℓa ℓe ℓc ℓd : Level}
              (X : SysEq i a b ℓa ℓe)
              (Y : SysEq j c d ℓc ℓd)
              (R : I X → I Y → Set ℓr)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr ⊔ ℓa ⊔ ℓe ⊔ ℓc ⊔ ℓd) where
  field
    step : ∀ {x : I X} {y : I Y} (r : R x y)
         → Stepˢ X Y R r

  mapR : ∀ {x : I X} {y : I Y} → R x y
       → M (A X) (E X) x → M (A Y) (E Y) y
  mapR r t .M.here   = shapeᴿ (step r) (M.here t)
  mapR r t .M.below v q =
    let x' , e , r' = pullˢ (step r) (M.here t) v q
    in mapR r' (M.below t x' e)
open Morphˢ public

------------------------------------------------------------------------
-- Composition of setoid carried correspondences; the edge adjunctions
-- compose via compAdjˢ (round-trips at the carried EqOn).
--
-- setoid 携带式对应的复合；边伴随经 compAdjˢ 复合（往返律建立在携带
-- 的 EqOn 上）。
------------------------------------------------------------------------
compMˢ :
  ∀ {i j k a b c d e f ℓ₁ ℓ₂ ℓa ℓe ℓc ℓd ℓg ℓh : Level}
    {X : SysEq i a b ℓa ℓe}
    {Y : SysEq j c d ℓc ℓd}
    {Z : SysEq k e f ℓg ℓh}
    {R : I X → I Y → Set ℓ₁} {S : I Y → I Z → Set ℓ₂}
  → Morphˢ X Y R → Morphˢ Y Z S → Morphˢ X Z (R ⍮ S)
compMˢ {X = X} {Y = Y} {Z = Z} φ ψ .step {x = x} {y = z} (ym , r , s) =
  let φr = step φ r
      ψs = step ψ s
  in record
  { shapeᴿ = λ a → shapeᴿ ψs (shapeᴿ φr a)
  ; child = λ a w →
      let ym' , s' = child ψs (shapeᴿ φr a) w
          x' , r'  = child φr a ym'
      in x' , (ym' , r' , s')
  ; edge-adj = λ a w →
      let ym' , s' = child ψs (shapeᴿ φr a) w
          x' , r'  = child φr a ym'
      in compAdjˢ (≈E X x a x')
                  (≈E Y ym (shapeᴿ φr a) ym')
                  (≈E Z z (shapeᴿ ψs (shapeᴿ φr a)) w)
                  (edge-adj φr a ym')
                  (edge-adj ψs (shapeᴿ φr a) w)
  }

------------------------------------------------------------------------
-- Identity: the free path groupoid on the index.  The index layer here
-- is propositional equality (matching the old Cosmos index regime),
-- while the edge round-trips are at the carried EqOn.
--
-- 恒等：索引上的自由路径广群。此处索引层为命题相等（与旧 Cosmos 索引
-- 制度一致），而边往返律建立在携带的 EqOn 上。
------------------------------------------------------------------------
idMˢ : ∀ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe)
     → Morphˢ X X (λ (x y : I X) → x ≡ y)
idMˢ X .step {x = x₀} {y = .x₀} ≡refl = record
  { shapeᴿ   = λ a → a
  ; child    = λ a v → v , ≡refl
  ; edge-adj = λ a v → idAdjˢ (≈E X x₀ a v)
  }

------------------------------------------------------------------------
-- Pilot: a genuinely non-propositional equivalence
-- Carrier L = ℕ × Bool; (n , b) ≈L (m , c) iff n ≡ m, ignoring the
-- tag.  Thus (0 , true) ≈L (0 , false) but the two are NOT
-- propositionally equal.  No K is used: the witnesses are equalities
-- of the ℕ component only.
--
-- 试点：真正非命题的等价
-- 载体 L = ℕ × Bool；(n , b) ≈L (m , c) 当且仅当 n ≡ m，忽略标签。
-- 于是 (0 , true) ≈L (0 , false)，但二者命题不相等。不用 K：见证
-- 仅是 ℕ 分量上的等式。
------------------------------------------------------------------------
L : Set lzero
L = ℕ × Bool

infix 4 _≈L_
_≈L_ : Rel L lzero
(n , _) ≈L (m , _) = n ≡ m

LEq : EqOn L
LEq = record
  { _≈_ = _≈L_
  ; isEquivalence = record
    { refl  = ≡refl
    ; sym   = Prop.sym
    ; trans = Prop.trans
    }
  }

-- The two tags are propositionally distinct
--
-- 两个标签命题可区分
bool-neq : true ≡ false → ⊥
bool-neq ()

tag-neq : ¬ ((0 , true) ≡ (0 , false))
tag-neq e = bool-neq (cong proj₂ e)

------------------------------------------------------------------------
-- Container position adjunction on the non-propositional equivalence
--   source positions R = L (tagged), target positions P = ℕ (untagged)
--   to   : L → ℕ = proj₁       carried forward adjoint (NEW)
--   fro  : ℕ → L = (_, true)   the old contravariant onPos
--   η/ε  : round-trips holding only up to _≈L_ (the tag is forgotten
--          and re-attached canonically).
-- In the old container layer fro = onPos is the only map present; the
-- forward to and η/ε are precisely the data formerly rebuilt by subst
-- (pts-compat / onActP).  Here they are carried, at an equivalence
-- strictly coarser than _≡_.
--
-- 非命题等价上的容器位置伴随
--   源位置 R = L（带标签），目标位置 P = ℕ（无标签）
--   to   : L → ℕ = proj₁       携带的前向伴随（新增）
--   fro  : ℕ → L = (_, true)   旧反变 onPos
--   η/ε  ：仅在 _≈L_ 上成立的往返律（遗忘标签后规范重贴）。
-- 旧容器层只有 fro = onPos；前向 to 与 η/ε 正是过去靠 subst
-- （pts-compat / onActP）补造的数据。此处被携带，且建立在严格粗于
-- _≡_ 的等价上。
------------------------------------------------------------------------
onPosAdj : FiberAdjˢ (propEqOn ℕ) LEq
onPosAdj = record
  { to       = proj₁
  ; fro      = λ n → (n , true)
  ; to-cong  = λ e → e
  ; fro-cong = λ e → e
  ; η        = λ { (n , _) → ≡refl }
  ; ε        = λ _ → ≡refl
  }

------------------------------------------------------------------------
-- Expressiveness witness: two M-trees bisimilar under LEq but with
-- propositionally distinct head labels.
-- Single index ⊤; labels and edges both live in L.  t and s differ
-- only by the head tag; every child is the same constant tree K.
-- _≈Mˢ_ relates them; the old _≈M_ cannot, because its here-eq asks
-- for (0 , true) ≡ (0 , false), which tag-neq refutes.
--
-- 表达力见证：两棵 M 树在 LEq 下互模拟，但头部标签命题不相等。
-- 单索引 ⊤；标签与边都取 L。t 与 s 仅头部标签不同，所有子节点都是
-- 同一棵常值树 K。_≈Mˢ_ 联系二者；旧 _≈M_ 不能，因其 here-eq 要求
-- (0 , true) ≡ (0 , false)，被 tag-neq 否定。
------------------------------------------------------------------------
private
  Iᵗ : Set lzero
  Iᵗ = ⊤ {lzero}

  ttᵗ : Iᵗ
  ttᵗ = tt {lzero}

  Aᵗ : Iᵗ → Set lzero
  Aᵗ _ = L

  Eᵗ : (i : Iᵗ) (a : Aᵗ i) (j : Iᵗ) → Set lzero
  Eᵗ _ _ _ = L

  ≈Aᵗ : (x : Iᵗ) → EqOn (Aᵗ x)
  ≈Aᵗ _ = LEq

  ≈Eᵗ : (x : Iᵗ) (a : Aᵗ x) (j : Iᵗ) → EqOn (Eᵗ x a j)
  ≈Eᵗ _ _ _ = LEq

  K : M Aᵗ Eᵗ ttᵗ
  K .M.here = (0 , true)
  K .M.below _ _ = K

  t : M Aᵗ Eᵗ ttᵗ
  t .M.here = (0 , true)
  t .M.below _ _ = K

  s : M Aᵗ Eᵗ ttᵗ
  s .M.here = (0 , false)
  s .M.below _ _ = K

  -- Setoid bisimulation relates the two distinct-tag trees
  --
  -- setoid 互模拟联系这两棵标签不同的树
  t≈Mˢs : _≈Mˢ_ ≈Aᵗ ≈Eᵗ t s
  t≈Mˢs .here-eq = ≡refl
  t≈Mˢs .below-eq _ =
      idAdjˢ LEq
    , ( (λ _ → ≈Mˢ-refl ≈Aᵗ ≈Eᵗ K)
      , (λ _ → ≈Mˢ-refl ≈Aᵗ ≈Eᵗ K) )

  -- The head labels are not propositionally equal: the old
  -- propositional bisimulation is unavailable
  --
  -- 头部标签命题不相等：旧命题互模拟不可用
  t≄Ms-head : ¬ (M.here t ≡ M.here s)
  t≄Ms-head = tag-neq
