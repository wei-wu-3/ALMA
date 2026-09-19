------------------------------------------------------------------------
-- LayerZeroMediator — dependent embedding on a two-object tower
-- LayerZeroMediator —— 两对象塔上的依赖嵌入
--
-- The simplified tower has singleton position sets, so pos-inhabited and
-- its naturality are automatic. This allows a dependent embedding whose
-- F₀ depends on the input cosmos's F₀. Formally, strictEmbed-dependent has
-- the dependent function type
--     (x : Cosmos) → EmbeddingData x → Cosmos′
-- "LayerZero" records compatibility only for layer-0 inputs
-- 简化塔的位置集为单点集，故 pos-inhabited 及其自然性自动成立
-- 这使得依赖嵌入的 F₀ 可以依赖输入宇宙的 F₀。形式上，strictEmbed-dependent
-- 具有依赖函数类型
--     (x : Cosmos) → EmbeddingData x → Cosmos′
-- "LayerZero" 记录只对层 0 的输入刻画相容性
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.LayerZeroMediator where

open import Agda.Primitive using (lzero; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Terminal using (_≈C_; ≈C-refl)
open import ALMA.Cosmos.CumulativeHierarchy using (EmbeddingData)
open import ALMA.Cosmos.StrictLift using (StrictLayer; strictStep-suc)
open import ALMA.Cosmos.CumulativeHierarchyInstances using (module FinCatHierarchy)
open FinCatHierarchy using (FinCat)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (Tower; LimitLayer)
open import ALMA.Cosmos.FinCat2Witness
  using ( TrivialFC; TwoObjLayer; twoIdx; twoTower; cosmos-id; cosmos-const0
        ; cosmos-id≉cosmos-const0; zero≠suc-fzero )
open import ALMA.Cosmos.FinCat2TowerLemmas using (proj-obj; embed-obj; embed-shape)

open StrictLayer
open EmbeddingData
open Unfolding
open Tower
open LimitLayer
open _≈C_

-- pos-inhabited on the simplified tower (automatic: singleton position sets)
-- 简化塔上的 pos-inhabited（自动：位置集为单点集）
pos-inhabited-trivial
  : ∀ {A : Category.Obj (FinCat 2)}
  → (s : ShapeOf TrivialFC A) → PosOf TrivialFC {A = A} s
pos-inhabited-trivial _ = lift tt

-- Dependent unfoldFunctor (concrete on L = TwoObjLayer)
-- F₀((A,s),u) = (x.F₀(A,s), x.pos-to-shape s (lift tt)); F₀ depends on x
-- 依赖展开函子（在 L = TwoObjLayer 上具体给出）
-- F₀((A,s),u) = (x.F₀(A,s), x.pos-to-shape s (lift tt))；F₀ 依赖 x
private
  CL   = C TwoObjLayer
  FCL  = FC TwoObjLayer
  CL′  = C (strictStep-suc TwoObjLayer)
  FCL′ = FC (strictStep-suc TwoObjLayer)

dependent-F₀
  : (x : Cosmos CL FCL)
  → Category.Obj (ShapeCat CL′ FCL′) → Category.Obj CL′
dependent-F₀ x ((A , s) , _) =
  ( x .out .unfoldFunctor .Functor.F₀ (A , s)
  , x .out .pos-to-shape {A = A} s (pos-inhabited-trivial {A = A} s) )

-- The sym below reverses the direction of pos-actS-compat so that the
-- second component matches the shape transport in F₁
-- 下面的 sym 反转 pos-actS-compat 的方向，使第二分量与 F₁ 中的形状传输匹配
dependent-F₁
  : (x : Cosmos CL FCL)
  → {u₀ u₁ : Category.Obj (ShapeCat CL′ FCL′)}
  → Category._⇒_ (ShapeCat CL′ FCL′) u₀ u₁
  → Category._⇒_ CL′ (dependent-F₀ x u₀) (dependent-F₀ x u₁)
dependent-F₁ x {u₀ = u₀} {u₁ = u₁} f =
  ( x .out .unfoldFunctor .Functor.F₁ {A = proj₁ u₀} {B = proj₁ u₁}
      (proj₁ f)
  , sym (x .out .pos-actS-compat
           {A = proj₁ (proj₁ u₀)} {B = proj₁ (proj₁ u₁)}
           {s = proj₂ (proj₁ u₀)} {t = proj₂ (proj₁ u₁)}
           (proj₁ (proj₁ f)) (proj₂ (proj₁ f)) (lift tt)) )

dependent-unfoldFunctor
  : (x : Cosmos CL FCL) → Functor (ShapeCat CL′ FCL′) CL′
dependent-unfoldFunctor x = record
  { F₀ = dependent-F₀ x
  ; F₁ = λ {A} {B} f → dependent-F₁ x {u₀ = A} {u₁ = B} f
  ; identity     = λ {A} → x .out .unfoldFunctor .Functor.identity {A = proj₁ A}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
      x .out .unfoldFunctor .Functor.homomorphism
        {X = proj₁ X} {Y = proj₁ Y} {Z = proj₁ Z}
        {f = proj₁ f} {g = proj₁ g}
  ; F-resp-≈ = λ {A} {B} {f} {g} f≈g →
      x .out .unfoldFunctor .Functor.F-resp-≈
        {A = proj₁ A} {B = proj₁ B}
        {f = proj₁ f} {g = proj₁ g} f≈g
  }

-- strictEmbed-dependent: a dependent embedding of one cosmos into the next layer
-- Its type is the dependent function type (x : Cosmos) → EmbeddingData x → Cosmos′
-- strictEmbed-dependent：把一个宇宙依赖嵌入到下一层
-- 其类型为依赖函数类型 (x : Cosmos) → EmbeddingData x → Cosmos′
strictEmbed-dependent
  : (x : Cosmos CL FCL)
  → EmbeddingData x
  → Cosmos CL′ FCL′
strictEmbed-dependent x ed .out = record
  { unfoldFunctor   = dependent-unfoldFunctor x
  ; unfold-next     = λ { {A} u →
      strictEmbed-dependent
        (x .out .unfold-next {A = proj₁ A} (lower u))
        (next ed {A = proj₁ A} (lower u)) }
  ; pos-to-shape = λ {A} _ _ →
      lift (x .out .pos-to-shape {A = proj₁ A} (proj₂ A) (lift tt))
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- strictEmbed-dependent preserves F₀-distinctness
-- At ((fsuc fzero, lift tt), lift (lift tt)): F₀ of cosmos-id is fsuc fzero,
-- F₀ of cosmos-const0 is fzero; the first components differ
-- strictEmbed-dependent 保持 F₀ 上的可区分性
-- 在 ((fsuc fzero, lift tt), lift (lift tt)) 处：cosmos-id 的 F₀ 是 fsuc fzero，
-- cosmos-const0 的 F₀ 是 fzero，第一分量不同
strictEmbed-dependent-id≉const0
  : (ed-id : EmbeddingData cosmos-id)
  → (ed-const0 : EmbeddingData cosmos-const0)
  → ¬ (strictEmbed-dependent cosmos-id ed-id
       ≈C strictEmbed-dependent cosmos-const0 ed-const0)
strictEmbed-dependent-id≉const0 ed-id ed-const0 eq =
  zero≠suc-fzero
    (sym (cong proj₁
      (unfoldFunctor₀-eq eq
        {A = (fsuc fzero , lift tt)}
        (lift (lift tt)))))

-- LayerZeroCocone and LayerZeroMediator (layer-0 compatibility only)
-- step-compat, liftAt-step, mediate-coh, mediate-unique quantify only over
-- layer-0 inputs
-- LayerZeroCocone 与 LayerZeroMediator（仅限层 0 的相容性）
-- step-compat、liftAt-step、mediate-coh、mediate-unique 只对层 0 输入量化
record LayerZeroCocone (D : StrictLayer lzero lzero lzero lzero lzero) : Setω where
  private
    C0  = C (layer twoTower 0)
    FC0 = FC (layer twoTower 0)
    CD  = C D
    FCD = FC D
  field
    map : ∀ n → Cosmos (C (layer twoTower n)) (FC (layer twoTower n))
              → Cosmos CD FCD
    map-resp : ∀ n {x y}
      → _≈C_ {C = C (layer twoTower n)} {FC = FC (layer twoTower n)} x y
      → _≈C_ {C = CD} {FC = FCD} (map n x) (map n y)
    step-compat :
      ∀ (x : Cosmos C0 FC0) (ed : EmbeddingData x) →
      _≈C_ {C = CD} {FC = FCD}
        (map 1 (strictEmbed-dependent x ed))
        (map 0 x)

record LayerZeroMediator : Setω where
  field
    liftAt : ∀ n → Cosmos (C (layer twoTower n)) (FC (layer twoTower n))
                    → Cosmos (FinCat 2) TrivialFC
    liftAt-resp : ∀ n {x y}
      → _≈C_ {C = C (layer twoTower n)} {FC = FC (layer twoTower n)} x y
      → _≈C_ {C = FinCat 2} {FC = TrivialFC} (liftAt n x) (liftAt n y)
    liftAt-step :
      ∀ (x : Cosmos (C (layer twoTower 0)) (FC (layer twoTower 0)))
        (ed : EmbeddingData x) →
      _≈C_ {C = FinCat 2} {FC = TrivialFC}
        (liftAt 1 (strictEmbed-dependent x ed))
        (liftAt 0 x)
    mediate : ∀ (D : StrictLayer lzero lzero lzero lzero lzero)
            → LayerZeroCocone D
            → Cosmos (FinCat 2) TrivialFC → Cosmos (C D) (FC D)
    mediate-resp : ∀ {D} (cone : LayerZeroCocone D) {x y}
      → _≈C_ {C = FinCat 2} {FC = TrivialFC} x y
      → _≈C_ {C = C D} {FC = FC D} (mediate D cone x) (mediate D cone y)

    -- Compatibility on layer 0 only: mediate = map 0, liftAt 0 = id
    -- 仅限层 0 上的相容性：mediate = map 0，liftAt 0 = id
    mediate-coh : ∀ {D} (cone : LayerZeroCocone D)
      → (x : Cosmos (C (layer twoTower 0)) (FC (layer twoTower 0)))
      → _≈C_ {C = C D} {FC = FC D}
          (mediate D cone (liftAt 0 x))
          (LayerZeroCocone.map cone 0 x)

    -- Layer-0 mediator uniqueness: follows from g-coh alone since
    -- mediate = map 0 and liftAt 0 = id
    -- 层 0 上的中介唯一性：由 g-coh 直接得到（mediate = map 0 且 liftAt 0 = id）
    mediate-unique : ∀ {D} (cone : LayerZeroCocone D)
      → (g : Cosmos (FinCat 2) TrivialFC → Cosmos (C D) (FC D))
      → (∀ {x y} → _≈C_ {C = FinCat 2} {FC = TrivialFC} x y
                   → _≈C_ {C = C D} {FC = FC D} (g x) (g y))
      → (∀ (x : Cosmos (C (layer twoTower 0)) (FC (layer twoTower 0))) →
           _≈C_ {C = C D} {FC = FC D}
             (g (liftAt 0 x)) (LayerZeroCocone.map cone 0 x))
      → ∀ z → _≈C_ {C = C D} {FC = FC D} (g z) (mediate D cone z)

-- liftAt-dependent: coinductive projection from layer n to FinCat 2
-- liftAt 0 = id; liftAt (suc n) projects F₀ via proj-obj and recurses
-- liftAt-dependent：从第 n 层到 FinCat 2 的余归纳投影
-- liftAt 0 = id；liftAt (suc n) 经 proj-obj 投影 F₀ 并递归
liftAt-dependent : ∀ n
  → Cosmos (C (layer twoTower n)) (FC (layer twoTower n))
  → Cosmos (FinCat 2) TrivialFC
liftAt-dependent zero x = x
liftAt-dependent (suc n) x .out = record
  { unfoldFunctor = record
    { F₀ = λ { (A , _) →
        proj-obj (suc n)
          (Functor.F₀ (Unfolding.unfoldFunctor (x .out))
            ( embed-obj (suc n) A
            , embed-shape (suc n) (embed-obj (suc n) A))) }
    ; F₁ = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }
  ; unfold-next = λ { {A} _ →
      liftAt-dependent (suc n)
        (Unfolding.unfold-next (x .out)
          {A = embed-obj (suc n) A}
          (embed-shape (suc n) (embed-obj (suc n) A))) }
  ; pos-to-shape = λ _ _ → lift tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- liftAt-step: liftAt 1 (strictEmbed x) ≈C liftAt 0 x = x
-- F₀ component by refl; unfold-next by coinduction
-- liftAt-step：liftAt 1 (strictEmbed x) ≈C liftAt 0 x = x
-- F₀ 分量由 refl 得证；unfold-next 由余归纳得证
liftAt-step-dependent
  : (x : Cosmos (C (layer twoTower 0)) (FC (layer twoTower 0)))
  → (ed : EmbeddingData x)
  → liftAt-dependent 1 (strictEmbed-dependent x ed)
    ≈C liftAt-dependent 0 x
liftAt-step-dependent x ed = bisim
  where
    bisim : _ ≈C _
    bisim .unfoldFunctor₀-eq {A} s = refl
    bisim .pos-to-shape-eq  {A} s p = refl
    bisim .unfold-next-eq   {A} s =
      liftAt-step-dependent
        (Unfolding.unfold-next (x .out) {A = A} s)
        (next ed {A = A} s)

-- liftAt-resp: liftAt-dependent preserves ≈C
-- liftAt-resp：liftAt-dependent 保持 ≈C
liftAt-resp-dependent
  : ∀ n {x y : Cosmos (C (layer twoTower n)) (FC (layer twoTower n))}
  → _≈C_ {C = C (layer twoTower n)} {FC = FC (layer twoTower n)} x y
  → _≈C_ {C = FinCat 2} {FC = TrivialFC} (liftAt-dependent n x) (liftAt-dependent n y)
liftAt-resp-dependent zero eq = eq
liftAt-resp-dependent (suc n) eq = bisim
  where
    bisim : _ ≈C _
    bisim .unfoldFunctor₀-eq {A} s =
      cong (proj-obj (suc n))
        (unfoldFunctor₀-eq eq
          {A = embed-obj (suc n) A}
          (embed-shape (suc n) (embed-obj (suc n) A)))
    bisim .pos-to-shape-eq {A} s p = refl
    bisim .unfold-next-eq {A} s =
      liftAt-resp-dependent (suc n)
        (unfold-next-eq eq
          {A = embed-obj (suc n) A}
          (embed-shape (suc n) (embed-obj (suc n) A)))

-- LimitLayer
-- 极限层
dependentLimit : LimitLayer twoIdx twoTower
dependentLimit = record
  { o∞ = lzero ; h∞ = lzero ; e∞ = lzero ; s∞ = lzero ; p∞ = lzero
  ; layer∞ = TwoObjLayer
  ; projC = λ n → record
    { F₀ = proj-obj n
    ; F₁ = λ _ → tt
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ _ → refl
    }
  }

-- Unconditional LayerZeroMediator
-- mediate ignores its second argument z: layer-0 compatibility does not
-- constrain higher-layer inputs, so any z yields map cone 0 z
-- 无条件的 LayerZeroMediator
-- mediate 忽略第二个参数 z：层 0 相容性不约束更高层的输入，
-- 因此任意 z 都返回 map cone 0 z
dependentLayerZeroMediator : LayerZeroMediator
dependentLayerZeroMediator = record
  { liftAt         = liftAt-dependent
  ; liftAt-resp    = liftAt-resp-dependent
  ; liftAt-step    = liftAt-step-dependent
  ; mediate        = λ D cone z → LayerZeroCocone.map cone 0 z
  ; mediate-resp   = λ {D} cone {x} {y} eq → LayerZeroCocone.map-resp cone 0 eq
  ; mediate-coh    = λ {D} cone x → ≈C-refl
  ; mediate-unique = λ {D} cone g g-resp g-coh z → g-coh z
  }

-- Non-triviality witness
-- liftAt 0 = id, so cosmos-id and cosmos-const0 stay distinct after lifting
-- 非平凡性见证
-- liftAt 0 = id，故 cosmos-id 与 cosmos-const0 提升后仍不互模拟
record LayerZeroNontrivialLimit (UL : LayerZeroMediator) : Setω where
  field
    n : ℕ
    x : Cosmos (C (layer twoTower n)) (FC (layer twoTower n))
    y : Cosmos (C (layer twoTower n)) (FC (layer twoTower n))
    x≉y : ¬ (LayerZeroMediator.liftAt UL n x
             ≈C LayerZeroMediator.liftAt UL n y)

dependent-nontrivial : LayerZeroNontrivialLimit dependentLayerZeroMediator
dependent-nontrivial = record
  { n = 0
  ; x = cosmos-id
  ; y = cosmos-const0
  ; x≉y = cosmos-id≉cosmos-const0
  }
