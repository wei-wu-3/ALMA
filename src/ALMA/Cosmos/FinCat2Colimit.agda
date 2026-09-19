------------------------------------------------------------------------
-- FinCat2Colimit — dependent embedding and LimitLayer for the FinCat 2 tower
-- FinCat2Colimit —— FinCat 2 塔的依赖嵌入与极限层
--
-- Provides dep-F₀, dep-F₁, dep-embed, the LimitLayer with
-- layer∞ = TwoObjLayer, the LimitCompatible proof, the layer lifting map
-- dep-liftAt with its resp/step lemmas, and the conditional framework
-- WithSurjectivity (parameterised by R, fams, embed-eq, surj)
-- 提供 dep-F₀、dep-F₁、dep-embed、layer∞ = TwoObjLayer 的 LimitLayer、
-- LimitCompatible 证明、层提升映射 dep-liftAt 及其 resp/step 引理，
-- 以及条件性框架 WithSurjectivity（以 R、fams、embed-eq、surj 为参数）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2Colimit where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (ntHelper)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actPOf; actSOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import ALMA.Cosmos.CumulativeHierarchy using (EmbeddingData)
open import ALMA.Cosmos.StrictLift using (StrictLayer; EmbeddingRule; EmbedFamily)
open import ALMA.Cosmos.CumulativeHierarchyInstances using (module FinCatHierarchy)
open FinCatHierarchy using (FinCat)
open import ALMA.Cosmos.CumulativeHierarchyLimit
  using (Tower; LimitLayer; LimitCompatible; EnrichedTower)
open import ALMA.Cosmos.FinCat2Witness
  using (TrivialFC; twoIdx; twoTower; TwoObjLayer; cosmos-id; cosmos-const0; cosmos-id≉cosmos-const0)
open import ALMA.Cosmos.FinCat2TowerLemmas
  using (proj-obj; embed-obj; embed-shape; shape-singleton-at)
open import ALMA.Cosmos.ConditionalNontrivialLimit
  using (Cocone; UniversalLimit; NontrivialLimit)

-- Position inhabitants and singletons for tower layers
-- Every shape at every layer of twoTower has a position, and any two
-- positions at the same shape are propositionally equal
-- Each shape of the n-th tower layer has an inhabitant of its position type
-- 塔层的位置居民与单点性
-- 塔的每一层、每个形状都有位置；同一形状上的任意两个位置命题相等
-- 第 n 层塔的每个形状都有位置类型的居民
pos-inhabited-tower
  : ∀ n (A : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
  → (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  → PosOf (StrictLayer.FC (Tower.layer twoTower n)) {A = A} s
pos-inhabited-tower zero    A         (lift tt) = lift tt
pos-inhabited-tower (suc n) (A , _)   (lift u)  = lift (pos-inhabited-tower n A u)

-- Any two positions at the same shape of the n-th layer are equal
-- 第 n 层同一形状上的任意两个位置相等
pos-singleton-tower
  : ∀ n (A : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
  → (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  → (p q : PosOf (StrictLayer.FC (Tower.layer twoTower n)) {A = A} s) → p ≡ q
pos-singleton-tower zero    A         (lift tt) (lift tt) (lift tt) = refl
pos-singleton-tower (suc n) (A , _)   (lift u)  (lift p)  (lift q) =
  cong lift (pos-singleton-tower n A u p q)

-- The pair (embed-obj (suc n) A, embed-shape (suc n) (embed-obj (suc n) A))
-- as a single object of the (suc n)-th layer's ShapeCat
-- 把 (embed-obj (suc n) A, embed-shape (suc n) (embed-obj (suc n) A)) 作为
-- 第 (suc n) 层 ShapeCat 的单个对象
private
  embed-pair
    : (n : ℕ) (A : Category.Obj (FinCat 2))
    → Σ (Category.Obj (StrictLayer.C (Tower.layer twoTower (suc n))))
        (λ X → ShapeOf (StrictLayer.FC (Tower.layer twoTower (suc n))) X)
  embed-pair n A =
    embed-obj (suc n) A , embed-shape (suc n) (embed-obj (suc n) A)

-- Dependent unfoldFunctor and dependent embedding
-- dep-F₀, dep-F₁, dep-unfoldFunctor, dep-embed: F₀ depends on the input
-- cosmos x, using pos-inhabited-tower to supply a position for
-- x's pos-to-shape
-- Dependent F₀: maps a lifted shape ((A, s), u) to the pair
-- (x.F₀ (A, s), x.pos-to-shape s (pos-inhabited-tower n A s))
-- 依赖展开函子与依赖嵌入
-- dep-F₀、dep-F₁、dep-unfoldFunctor、dep-embed：F₀ 依赖输入宇宙 x，
-- 用 pos-inhabited-tower 为 x 的 pos-to-shape 提供位置
-- 依赖 F₀：将提升形状 ((A, s), u) 映为
-- (x.F₀ (A, s), x.pos-to-shape s (pos-inhabited-tower n A s))
dep-F₀
  : ∀ n (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
  → Category.Obj (ShapeCat
      (StrictLayer.C (Tower.layer twoTower (suc n)))
      (StrictLayer.FC (Tower.layer twoTower (suc n))))
  → Category.Obj (StrictLayer.C (Tower.layer twoTower (suc n)))
dep-F₀ n x z =
  ( Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)
  , Unfolding.pos-to-shape (out x)
      {A = proj₁ (proj₁ z)} (proj₂ (proj₁ z))
      (pos-inhabited-tower n (proj₁ (proj₁ z)) (proj₂ (proj₁ z))) )

-- Dependent F₁: applies x.F₁ on the first component; the second
-- component is the shape-level proof, completed via pos-actS-compat
-- and pos-singleton-tower
-- 依赖 F₁：第一分量施加 x.F₁；第二分量是形状层证明，经
-- pos-actS-compat 与 pos-singleton-tower 补全
dep-F₁
  : ∀ n (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
  → {u v : Category.Obj (ShapeCat
      (StrictLayer.C (Tower.layer twoTower (suc n)))
      (StrictLayer.FC (Tower.layer twoTower (suc n))))}
  → Category._⇒_ (ShapeCat
      (StrictLayer.C (Tower.layer twoTower (suc n)))
      (StrictLayer.FC (Tower.layer twoTower (suc n)))) u v
  → Category._⇒_ (StrictLayer.C (Tower.layer twoTower (suc n)))
      (dep-F₀ n x u) (dep-F₀ n x v)
dep-F₁ n x {u} {v} f = (F₁-part , eq-part)
  where
    Cₙ  = StrictLayer.C (Tower.layer twoTower n)
    FCₙ = StrictLayer.FC (Tower.layer twoTower n)
    UXF = Unfolding.unfoldFunctor (out x)

    uA = proj₁ u
    vA = proj₁ v
    A  = proj₁ uA
    s  = proj₂ uA
    B  = proj₁ vA
    t  = proj₂ vA
    g  = proj₁ (proj₁ f)
    q  = proj₂ (proj₁ f)

    -- First component of the ShapeCat morphism
    -- 第一分量：x.F₁ 作用在 f 的第一分量上
    F₁-part : Category._⇒_ Cₙ (Functor.₀ UXF uA) (Functor.₀ UXF vA)
    F₁-part = UXF .Functor.F₁ (proj₁ f)

    posAtA : PosOf FCₙ s → ShapeOf FCₙ (Functor.₀ UXF uA)
    posAtA = Unfolding.pos-to-shape (out x) {A = A} s

    posAtB : PosOf FCₙ t → ShapeOf FCₙ (Functor.₀ UXF vA)
    posAtB = Unfolding.pos-to-shape (out x) {A = B} t

    p' = pos-inhabited-tower n B (actSOf FCₙ g s)

    -- pos-actS-compat: pos-to-shape commutes with the functorial action
    -- pos-actS-compat：pos-to-shape 与函子作用交换
    a1 : posAtB (subst (PosOf FCₙ) q p')
       ≡ actSOf FCₙ F₁-part (posAtA (actPOf FCₙ g s p'))
    a1 = Unfolding.pos-actS-compat (out x)
           {A = A} {B = B} {s = s} {t = t} g q p'

    -- Position singletons collapse the transported positions
    -- 位置单点性合并传输后的位置
    a2 : actPOf FCₙ g s p' ≡ pos-inhabited-tower n A s
    a2 = pos-singleton-tower n A s
           (actPOf FCₙ g s p') (pos-inhabited-tower n A s)
    a3 : subst (PosOf FCₙ) q p' ≡ pos-inhabited-tower n B t
    a3 = pos-singleton-tower n B t
           (subst (PosOf FCₙ) q p') (pos-inhabited-tower n B t)

    -- Second component: shape-level equation, assembled via three steps
    -- 第二分量：形状层等式，由三步组合
    eq-part : actSOf FCₙ F₁-part (posAtA (pos-inhabited-tower n A s))
            ≡ posAtB (pos-inhabited-tower n B t)
    eq-part = begin
      actSOf FCₙ F₁-part (posAtA (pos-inhabited-tower n A s))
        ≡⟨ cong (actSOf FCₙ F₁-part) (sym (cong posAtA a2)) ⟩
      actSOf FCₙ F₁-part (posAtA (actPOf FCₙ g s p'))
        ≡⟨ sym a1 ⟩
      posAtB (subst (PosOf FCₙ) q p')
        ≡⟨ cong posAtB a3 ⟩
      posAtB (pos-inhabited-tower n B t)
      ∎

-- The dependent unfold functor assembling dep-F₀ and dep-F₁
-- 组装 dep-F₀ 与 dep-F₁ 的依赖展开函子
dep-unfoldFunctor
  : ∀ n (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
  → Functor (ShapeCat
      (StrictLayer.C (Tower.layer twoTower (suc n)))
      (StrictLayer.FC (Tower.layer twoTower (suc n))))
      (StrictLayer.C (Tower.layer twoTower (suc n)))
dep-unfoldFunctor n x = record
  { F₀           = dep-F₀ n x
  ; F₁           = dep-F₁ n x
  ; identity     = Unfolding.unfoldFunctor (out x) .Functor.identity
  ; homomorphism = Unfolding.unfoldFunctor (out x) .Functor.homomorphism
  ; F-resp-≈     = λ f≈g → Unfolding.unfoldFunctor (out x) .Functor.F-resp-≈ f≈g
  }

-- The dependent strict embedding of the n-th layer into the (suc n)-th
-- 将第 n 层依赖严格嵌入到第 suc n 层
dep-embed
  : ∀ n (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
           (StrictLayer.FC (Tower.layer twoTower (suc n)))
dep-embed n x ed .out = record
  { unfoldFunctor = dep-unfoldFunctor n x
  ; unfold-next = λ { {A} s →
      dep-embed n
        (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
        (EmbeddingData.next ed {A = proj₁ A} (proj₂ A)) }
  ; pos-to-shape = λ { {A} _ _ →
      lift (Unfolding.pos-to-shape (out x) {A = proj₁ A} (proj₂ A)
              (pos-inhabited-tower n (proj₁ A) (proj₂ A))) }
  ; pos-actS-compat = λ { {A} {B} {s} {t} f eq p →
      let
        FC' = StrictLayer.FC (Tower.layer twoTower (suc n))
        UF  = dep-unfoldFunctor n x
        lhs = lift (Unfolding.pos-to-shape (out x) {A = proj₁ B} (proj₂ B)
                       (pos-inhabited-tower n (proj₁ B) (proj₂ B)))
        rhs = actSOf FC' (UF .Functor.F₁ (f , eq))
                (lift (Unfolding.pos-to-shape (out x) {A = proj₁ A} (proj₂ A)
                           (pos-inhabited-tower n (proj₁ A) (proj₂ A))))
        C₀  = UF .Functor.F₀ (B , t)
      in shape-singleton-at (suc n) C₀ lhs rhs }
  }

-- Colimit layer for the FinCat 2 tower: layer∞ = TwoObjLayer (FinCat 2 with
-- TrivialFC), projC n .F₀ = proj-obj n, projC n .F₁ = λ _ → tt. Type-correctness
-- of F₁ = tt follows from FinCat 2's hom-set being ⊤; faithfulness holds because
-- every tower layer's hom-set is ⊤ up to propositional equality (Lift ⊤ is a set),
-- so F₁ is a bijection on hom-sets. LimitCompatible is trivial: both sides of
-- proj-step-coh are constant on hom-sets, so the natural isomorphism is the
-- identity
-- 塔的余极限层：layer∞ = TwoObjLayer（FinCat 2 配 TrivialFC），
-- projC n .F₀ = proj-obj n，projC n .F₁ = λ _ → tt。F₁ = tt 的类型正确性源于
-- FinCat 2 的 hom 集为 ⊤；忠实性成立是因为每层塔的 hom 集在命题相等下为 ⊤
-- （Lift ⊤ 是集合），故 F₁ 在 hom 集上是双射。LimitCompatible 平凡：
-- proj-step-coh 两边在 hom 集上均为常值，自然同构即为恒等
colimitLayer : LimitLayer twoIdx twoTower
colimitLayer = record
  { o∞ = lzero ; h∞ = lzero ; e∞ = lzero ; s∞ = lzero ; p∞ = lzero
  ; layer∞ = TwoObjLayer
  ; projC = λ n → record
      { F₀           = proj-obj n
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
  }

-- Compatibility: projC (suc n) ≅ projC n ∘F π; both sides are
-- constant on hom-sets, so the natural isomorphism is trivial
-- 相容性：projC (suc n) ≅ projC n ∘F π；两边在 hom 集上均为常值，
-- 自然同构平凡
colimitLayer-compatible : LimitCompatible colimitLayer
colimitLayer-compatible = record
  { proj-step-coh = λ n → record
      { F⇒G  = ntHelper record { η = λ _ → tt ; commute = λ _ → refl }
      ; F⇐G  = ntHelper record { η = λ _ → tt ; commute = λ _ → refl }
      ; iso  = λ _ → record { isoˡ = refl ; isoʳ = refl }
      }
  }

-- Layer lifting map dep-liftAt and its lemmas
-- dep-liftAt 0 = id; dep-liftAt (suc n) projects F₀ via proj-obj and
-- recurses on unfold-next. dep-liftAt-resp preserves _≈C_; 
-- dep-liftAt-step witnesses dep-liftAt (suc n) ∘ dep-embed n ≈C dep-liftAt n
-- Layer lifting map from the n-th layer to FinCat 2
-- 层提升映射 dep-liftAt 及其引理
-- dep-liftAt 0 = id；dep-liftAt (suc n) 经 proj-obj 投影 F₀ 并在
-- unfold-next 上递归。dep-liftAt-resp 保持 _≈C_；
-- dep-liftAt-step 见证 dep-liftAt (suc n) ∘ dep-embed n ≈C dep-liftAt n
-- 从第 n 层到 FinCat 2 的层提升映射
dep-liftAt
  : ∀ n → Cosmos (StrictLayer.C (Tower.layer twoTower n))
                  (StrictLayer.FC (Tower.layer twoTower n))
        → Cosmos (FinCat 2) TrivialFC
dep-liftAt zero    x = x
dep-liftAt (suc n) x .out = record
  { unfoldFunctor = record
      { F₀ = λ { (A , _) →
          proj-obj (suc n)
            (Unfolding.unfoldFunctor (out x) .Functor.F₀ (embed-pair n A)) }
      ; F₁ = λ _ → tt
      ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ _ → refl }
  ; unfold-next = λ { {A = A} _ →
      let p = embed-pair n A
      in dep-liftAt (suc n)
           (Unfolding.unfold-next (out x) {A = proj₁ p} (proj₂ p)) }
  ; pos-to-shape    = λ _ _ → lift tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- dep-liftAt preserves _≈C_
-- dep-liftAt 保持 _≈C_
dep-liftAt-resp
  : ∀ n {x y : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                       (StrictLayer.FC (Tower.layer twoTower n))}
  → x ≈C y → dep-liftAt n x ≈C dep-liftAt n y
dep-liftAt-resp zero    p = p
dep-liftAt-resp (suc n) p ._≈C_.unfoldFunctor₀-eq {A} s =
  let q = embed-pair n A
  in cong (proj-obj (suc n))
       (p ._≈C_.unfoldFunctor₀-eq {A = proj₁ q} (proj₂ q))
dep-liftAt-resp (suc n) p ._≈C_.pos-to-shape-eq s q = refl
dep-liftAt-resp (suc n) p ._≈C_.unfold-next-eq {A} s =
  let q = embed-pair n A
  in dep-liftAt-resp (suc n)
       (p ._≈C_.unfold-next-eq {A = proj₁ q} (proj₂ q))

-- dep-liftAt-step: lifting after embedding equals lifting directly
-- dep-liftAt-step：嵌入后再提升等于直接从上一层提升
dep-liftAt-step
  : ∀ n
    (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                 (StrictLayer.FC (Tower.layer twoTower n)))
    (ed : EmbeddingData x)
  → dep-liftAt (suc n) (dep-embed n x ed) ≈C dep-liftAt n x
dep-liftAt-step zero x ed ._≈C_.unfoldFunctor₀-eq {A} s = refl
dep-liftAt-step zero x ed ._≈C_.pos-to-shape-eq  s p = refl
dep-liftAt-step zero x ed ._≈C_.unfold-next-eq  {A = A} s =
  dep-liftAt-step zero
    (Unfolding.unfold-next (out x) {A = A} s)
    (EmbeddingData.next ed {A = A} s)
dep-liftAt-step (suc m) x ed ._≈C_.unfoldFunctor₀-eq {A} s = refl
dep-liftAt-step (suc m) x ed ._≈C_.pos-to-shape-eq  s p = refl
dep-liftAt-step (suc m) x ed ._≈C_.unfold-next-eq {A = A} s =
  let p = embed-pair m A
  in dep-liftAt-step (suc m)
       (Unfolding.unfold-next (out x) {A = proj₁ p} (proj₂ p))
       (EmbeddingData.next ed {A = proj₁ p} (proj₂ p))

-- embed-eq is a genuine constraint: it does NOT hold for R = outer-rule
-- (see FinCat2EmbeddingMismatch). For a rule-independent framework that
-- uses dep-embed-tower directly, see FinCat2ColimitWithDep
-- embed-eq 是实质约束，对 R = outer-rule 不成立（见 FinCat2EmbeddingMismatch）
-- 直接使用 dep-embed-tower 的规则无关框架见 FinCat2ColimitWithDep
module WithSurjectivity
  (R : EmbeddingRule)
  (fams : ∀ n → EmbedFamily R (Tower.layer twoTower n))
  (embed-eq : ∀ n → EmbeddingRule.Embed R (Tower.layer twoTower n) ≡ dep-embed n)
  (surj : ∀ n
          (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
                       (StrictLayer.FC (Tower.layer twoTower (suc n))))
        → Σ (Cosmos (StrictLayer.C (Tower.layer twoTower n))
                     (StrictLayer.FC (Tower.layer twoTower n)))
            (λ y → x ≈C EmbeddingRule.Embed R (Tower.layer twoTower n) y
                     (EmbedFamily.getData (fams n) y))) where
  private
    ET : EnrichedTower R twoIdx
    ET = record { tower = twoTower ; fams = fams }

  -- liftAt-step expressed via Embed R, using embed-eq to reduce to
  -- dep-liftAt-step
  -- 用 Embed R 表达的 liftAt-step，经 embed-eq 归约为 dep-liftAt-step
  liftAt-step-R
    : ∀ n
      (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                   (StrictLayer.FC (Tower.layer twoTower n)))
    → dep-liftAt (suc n)
        (EmbeddingRule.Embed R (Tower.layer twoTower n) x
          (EmbedFamily.getData (fams n) x))
      ≈C dep-liftAt n x
  liftAt-step-R n x rewrite embed-eq n =
    dep-liftAt-step n x (EmbedFamily.getData (fams n) x)

  -- mediate-coh for dep-liftAt: map cone 0 ∘ dep-liftAt n ≈C map cone n,
  -- by induction on n using surj to recover the layer-n input
  -- dep-liftAt 的 mediate-coh：map cone 0 ∘ dep-liftAt n ≈C map cone n，
  -- 对 n 归纳，用 surj 恢复第 n 层输入
  dep-mediate-coh
    : ∀ {oD hD eD sD pD}
      {D : StrictLayer oD hD eD sD pD}
      (cone : Cocone ET D) (n : ℕ)
      (x : Cosmos (StrictLayer.C (Tower.layer twoTower n))
                   (StrictLayer.FC (Tower.layer twoTower n)))
    → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
        (Cocone.map cone 0 (dep-liftAt n x))
        (Cocone.map cone n x)
  dep-mediate-coh cone zero    x = ≈C-refl
  dep-mediate-coh cone (suc n) x =
    let (y , p) = surj n x
        q1 = Cocone.map-resp cone 0 (dep-liftAt-resp (suc n) p)
        q2 = Cocone.map-resp cone 0 (liftAt-step-R n y)
        q3 = dep-mediate-coh cone n y
        q4 = ≈C-trans (≈C-sym (Cocone.step-compat cone n y))
                      (Cocone.map-resp cone (suc n) (≈C-sym p))
    in ≈C-trans q1 (≈C-trans q2 (≈C-trans q3 q4))

  -- The universal limit assembled from dep-liftAt, mediate = map cone 0
  -- 由 dep-liftAt 组装的通用极限，mediate = map cone 0
  dependentUniversalLimit : UniversalLimit ET
  dependentUniversalLimit = record
    { limit          = colimitLayer
    ; liftAt         = dep-liftAt
    ; liftAt-resp    = λ n {x} {y} → dep-liftAt-resp n
    ; liftAt-step    = λ n x → liftAt-step-R n x
    ; mediate        = λ D cone z → Cocone.map cone 0 z
    ; mediate-resp   = λ {D} cone {x} {y} eq → Cocone.map-resp cone 0 eq
    ; mediate-coh    = λ {D} cone n x → dep-mediate-coh cone n x
    ; mediate-unique = λ {D} cone g g-resp g-coh z → g-coh 0 z
    }

  -- liftAt 0 is the identity, hence injective
  -- liftAt 0 是恒等，故为单射
  lift0-inj
    : ∀ {x y : Cosmos (FinCat 2) TrivialFC}
    → _≈C_ {C = StrictLayer.C
              (LimitLayer.layer∞ (UniversalLimit.limit dependentUniversalLimit))}
           {FC = StrictLayer.FC
              (LimitLayer.layer∞ (UniversalLimit.limit dependentUniversalLimit))}
           (UniversalLimit.liftAt dependentUniversalLimit 0 x)
           (UniversalLimit.liftAt dependentUniversalLimit 0 y)
    → x ≈C y
  lift0-inj p = p

  -- Non-triviality witness: cosmos-id and cosmos-const0 remain
  -- distinguishable after lifting at layer 0
  -- 非平凡见证：cosmos-id 与 cosmos-const0 在层 0 提升后仍可区分
  dependentNontrivial : NontrivialLimit dependentUniversalLimit
  dependentNontrivial = record
    { n    = 0
    ; x    = cosmos-id
    ; y    = cosmos-const0
    ; x≉y  = cosmos-id≉cosmos-const0
    }
