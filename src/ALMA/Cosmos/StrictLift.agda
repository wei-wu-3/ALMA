------------------------------------------------------------------------
-- StrictLift: level raising for the cumulative hierarchy
-- 严格层级提升：累积层级的层级递增迭代
--
-- LiftContainerFunctor — Functor (ContCat s p) → Functor (ContCat (s ⊔ s′) (p ⊔ p′))
-- StrictLayer / strictStep / strictStep-suc — layer stepping
-- strictEmbed — embedding a cosmos into the strictly-raised next layer
-- LiftContainerFunctor —— 函子 ContCat s p → ContCat (s ⊔ s′) (p ⊔ p′)
-- StrictLayer / strictStep / strictStep-suc —— 层级步进
-- strictEmbed —— 将宇宙嵌入严格提升后的下一层
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.StrictLift where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Container.Core using (Container; Shape; Position; _⇒_)
open import Data.Container.Morphism using (id; _∘_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (_∘F_)

open import ALMA.Cosmos.ContCategory using (ContCat; _≈M_)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out; UnitCat; UnitContainerFunctor)
open import ALMA.Cosmos.CumulativeHierarchy
  using (FC∘π; EmbeddingData; UniformEmbeddingFamily)
open import ALMA.Cosmos.Terminal using (_≈C_)
open import ALMA.Cosmos.Lambek using (in-F; in∘out≈id)

-- Level-raising preliminaries
-- 层级提升的预备构造

-- Eta rule for Lift: lift ∘ lower is the identity
-- Lift 的 eta 规则：lift ∘ lower 是恒等
lift-lower : ∀ {a b : Level} {A : Set a} (x : Lift b A) → lift (lower x) ≡ x
lift-lower (lift _) = refl

-- subst along a lift-equality commutes with lift, for the specific shape
-- of P used by position types: the input is an arbitrary lifted element,
-- and the family is applied after lowering
-- 沿 lift 等式的 subst 与 lift 交换，针对位置类型所用的 P 的形状：
-- 输入为任意提升元素，族在降层后应用
subst-lift-pos : ∀ {a b c d : Level} {A : Set a} {P : A → Set b} {x y : A}
                   (q : x ≡ y) (p : Lift {b} d (P x))
                 → subst (λ z → Lift {b} d (P (lower {a} {c} z)))
                         (cong (lift {a} {c}) q)
                         p
                   ≡ lift (subst P q (lower p))
subst-lift-pos refl p = sym (lift-lower p)

-- lower of subst-lift-pos: the result is the unlifted substitution on
-- the lowered input
-- subst-lift-pos 的降层形式：结果为对降层输入的未提升替换
lower-subst-lift : ∀ {a b c d : Level} {A : Set a} {P : A → Set b} {x y : A}
                     (q : x ≡ y) (p : Lift {b} d (P x))
                   → lower (subst (λ z → Lift {b} d (P (lower {a} {c} z)))
                                  (cong (lift {a} {c}) q) p)
                     ≡ subst P q (lower p)
lower-subst-lift q p = cong lower (subst-lift-pos q p)

-- Lift shape and position types by levels s′ and p′
-- Position is defined via lower so that its interaction with subst stays definitional
-- 将形状与位置类型的层级分别提升 s′、p′
-- Position 用 lower 定义，使与 subst 的交互保持定义性
LiftContainer : ∀ {s p : Level} (s′ p′ : Level) → Container s p
              → Container (s ⊔ s′) (p ⊔ p′)
LiftContainer {s} {p} s′ p′ C = record
  { Shape    = Lift {s} s′ (Shape C)
  ; Position = λ z → Lift {p} p′ (Position C (lower z))
  }

-- General form: subst along a lift-equality commutes with lift for an
-- arbitrary family P, with input given as lift u
-- 一般形式：沿 lift 等式的 subst 对任意族 P 与 lift 交换，
-- 输入以 lift u 的形式给出
subst-lift : ∀ {a b c d : Level} {A : Set a} (P : A → Set b)
               {x y : A} (e : x ≡ y) (u : P x)
             → subst (λ (z : Lift {a} c A) → Lift {b} d (P (lower z)))
                     (cong (lift {a} {c}) e)
                     (lift {b} {d} u)
               ≡ lift {b} {d} (subst P e u)
subst-lift P refl u = refl

-- lower of subst-lift applied to lift u: simplifies to the unlifted
-- substitution on u
-- subst-lift 作用于 lift u 后的降层形式：化简为对 u 的未提升替换
subst-lift-lower : ∀ {a b c d : Level} {A : Set a} (P : A → Set b)
                     {x y : A} (e : x ≡ y) (u : P x)
                   → lower (subst (λ (z : Lift {a} c A) → Lift {b} d (P (lower z)))
                                  (cong (lift {a} {c}) e)
                                  (lift {b} {d} u))
                     ≡ subst P e u
subst-lift-lower P e u = cong lower (subst-lift P e u)

-- Lift a ContCat-valued functor one level up
-- 将 ContCat 值函子提升一层
LiftContainerFunctor : ∀ {s p : Level} (s′ p′ : Level)
                     → Functor (ContCat s p) (ContCat (s ⊔ s′) (p ⊔ p′))
LiftContainerFunctor {s} {p} s′ p′ = record
  { F₀           = LiftContainer s′ p′
  ; F₁           = liftF₁
  ; identity     = lift-id
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                    lift-hom {X = X} {Y = Y} {Z = Z} {f = f} {g = g}
  ; F-resp-≈     = lift-resp
  }
  where
    liftF₁ : ∀ {X Y : Container s p} → X ⇒ Y
           → LiftContainer s′ p′ X ⇒ LiftContainer s′ p′ Y
    liftF₁ f = record
      { shape    = λ { (lift sh) → lift (_⇒_.shape f sh) }
      ; position = λ { {sh} q → lift (_⇒_.position f {lower sh} (lower q)) }
      }

    lift-id : ∀ {X} → liftF₁ {X = X} {Y = X} (id X)
                      ≈M id (LiftContainer s′ p′ X)
    lift-id = record
      { shape-eq = λ { (lift sh) → refl }
      ; position-eq   = λ { (lift sh) (lift q) → refl }
      }

    lift-hom : ∀ {X Y Z : Container s p} {f : X ⇒ Y} {g : Y ⇒ Z}
             → liftF₁ (g ∘ f) ≈M (liftF₁ g ∘ liftF₁ f)
    lift-hom {X = X} {Y = Y} {Z = Z} {f = f} {g = g} = record
      { shape-eq = λ { (lift sh) → refl }
      ; position-eq   = λ { (lift sh) (lift q) → refl }
      }

    lift-resp : ∀ {X Y} {f g : X ⇒ Y} → f ≈M g → liftF₁ f ≈M liftF₁ g
    lift-resp {X} {Y} {f} {g} f≈g = record
      { shape-eq = λ { (lift sh) → cong lift (Fe.shape-eq sh) }
      ; position-eq   = λ { (lift sh) (lift q) →
          trans (cong lift (Fe.position-eq sh q))
                (cong (λ u → lift (_⇒_.position g {sh} u))
                      (sym (subst-lift-lower (Position Y) (Fe.shape-eq sh) q))) }
      }
      where
        module Fe = _≈M_ f≈g

-- Strict layers and strictly-growing step
-- 严格层级与严格增长的步进

-- Universally quantifies over the source category's levels, hence resides in Setω
-- 对源范畴的层级做全称量化，故位于 Setω
LiftFC-Strategy : ∀ {s p s′ p′ : Level} → Setω
LiftFC-Strategy {s} {p} {s′} {p′} =
  ∀ {o h e} {C : Category o h e}
  → Functor C (ContCat s p)
  → Functor C (ContCat (s ⊔ s′) (p ⊔ p′))

concreteLiftFC : ∀ {s p s′ p′} {o h e} {C : Category o h e}
  → Functor C (ContCat s p)
  → Functor C (ContCat (s ⊔ s′) (p ⊔ p′))
concreteLiftFC {s} {p} {s′} {p′} FC =
  LiftContainerFunctor {s} {p} s′ p′ ∘F FC

-- Layer record and the strictly-growing step operation
-- 层级记录与严格增长的步进操作
record StrictLayer (o h e s p : Level) : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    C  : Category o h e
    FC : Functor C (ContCat s p)

open StrictLayer public

strictStep : ∀ {o h e s p s′ p′ : Level}
           → LiftFC-Strategy {s} {p} {s′} {p′}
           → StrictLayer o h e s p
           → StrictLayer (o ⊔ s) (h ⊔ s) e (s ⊔ s′) (p ⊔ p′)
strictStep liftFC L = record
  { C  = ShapeCat (StrictLayer.C L) (StrictLayer.FC L)
  ; FC = liftFC (FC∘π (StrictLayer.FC L))
  }

concreteStrictStep : ∀ {o h e s p s′ p′}
  → StrictLayer o h e s p
  → StrictLayer (o ⊔ s) (h ⊔ s) e (s ⊔ s′) (p ⊔ p′)
concreteStrictStep {s = s} {p = p} {s′ = s′} {p′ = p′} L =
  strictStep {s = s} {p = p} {s′ = s′} {p′ = p′}
    (concreteLiftFC {s = s} {p = p} {s′ = s′} {p′ = p′})
    L

-- Type depends on Agda's level normalization:
-- s ⊔ lsuc (s ⊔ p) = lsuc (s ⊔ p) since s ≤ s ⊔ p
-- 类型依赖 Agda 的层级归一化：
-- 因 s ≤ s ⊔ p，故 s ⊔ lsuc (s ⊔ p) = lsuc (s ⊔ p)
strictStep-suc : ∀ {o h e s p}
  → StrictLayer o h e s p
  → StrictLayer (o ⊔ s) (h ⊔ s) e (lsuc (s ⊔ p)) (lsuc (s ⊔ p))
strictStep-suc {s = s} {p = p} =
  concreteStrictStep {s = s} {p = p}
                     {s′ = lsuc (s ⊔ p)} {p′ = lsuc (s ⊔ p)}

-- strictEmbed — embedding into the strictly-raised next layer
-- strictEmbed —— 嵌入到严格提升后的下一层

-- lift ∘ lower is the identity on equality proofs
-- 在等式证明上，lift ∘ lower 是恒等
lift-lower-cong : ∀ {a b : Level} {A : Set a} {x y : Lift b A}
                  (q : x ≡ y) → cong lift (cong lower q) ≡ q
lift-lower-cong refl = refl

-- The unfold functor of the strict embedding:
-- forgets the outer shape and keeps the inner one
-- 严格嵌入的展开函子：遗忘外层形状，保留内层形状
strictEmbed-unfoldFunctor
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → Functor (ShapeCat (StrictLayer.C (strictStep-suc L))
                      (StrictLayer.FC (strictStep-suc L)))
            (ShapeCat (StrictLayer.C L) (StrictLayer.FC L))
strictEmbed-unfoldFunctor L = record
  { F₀           = λ z → proj₁ (proj₁ z) , lower (proj₂ z)
  ; F₁           = λ f → proj₁ (proj₁ f) , cong lower (proj₂ f)
  ; identity     = λ {z} →
                     Category.Equiv.refl (StrictLayer.C L)
                       {x = Category.id (StrictLayer.C L)}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                     Category.Equiv.refl (StrictLayer.C L)
                       {x = Category._∘_ (StrictLayer.C L)
                                         (proj₁ (proj₁ g))
                                         (proj₁ (proj₁ f))}
  ; F-resp-≈     = λ ff≈gg → ff≈gg
  }

strictEmbed
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (strictStep-suc L))
           (StrictLayer.FC (strictStep-suc L))
strictEmbed L x ed .out = record
  { unfoldFunctor   = strictEmbed-unfoldFunctor L
  ; unfold-next     = λ { {A} u →
      -- Recurse on the inner shape: lower the lifted shape u,
      -- unfold the source, and embed the result
      -- 对内层形状递归：对提升形状 u 降层，展开源宇宙，再嵌入结果
      strictEmbed L
        (UX.unfold-next {A = proj₁ A} (lower u))
        (EmbeddingData.next ed {A = proj₁ A} (lower u)) }
  ; pos-to-shape    = λ {A} s p →
      -- Position-to-shape is the retract action on the unlifted data,
      -- then re-lifted
      -- 位置到形状的映射：先对未提升数据做 retract 作用，再重新提升
      lift (actSOf FC_L (EmbeddingData.retract ed (lower s))
                       (UX.pos-to-shape (lower s) (lower p)))
  ; pos-actS-compat = λ {A} {B} {s} {t} g p p₁ →
      cong lift (begin
        actSOf FC_L (EmbeddingData.retract ed {A = proj₁ B} (lower t))
          (UX.pos-to-shape {A = proj₁ B} (lower t)
             (lower (subst (PosOf FC′ {A = B}) p p₁)))
        ≡⟨ cong (actSOf FC_L (EmbeddingData.retract ed {A = proj₁ B} (lower t)))
                (cong (UX.pos-to-shape {A = proj₁ B} (lower t))
                      (bridge {A = A} {B = B} {s = s} {t = t} g p p₁)) ⟩
        actSOf FC_L (EmbeddingData.retract ed {A = proj₁ B} (lower t))
          (UX.pos-to-shape {A = proj₁ B} (lower t)
             (subst (PosOf FC_L {A = proj₁ B}) (cong lower p) (lower p₁)))
        ≡⟨ compat {A = proj₁ A} {B = proj₁ B}
                  {s = lower s} {t = lower t}
                  (proj₁ g) (cong lower p) (lower p₁) ⟩
        actSOf FC_L (proj₁ g)
          (actSOf FC_L (EmbeddingData.retract ed {A = proj₁ A} (lower s))
             (UX.pos-to-shape {A = proj₁ A} (lower s)
                (actPOf FC_L (proj₁ g) (lower s) (lower p₁))))
        ≡⟨ refl ⟩
        actSOf FC_L (proj₁ g)
          (actSOf FC_L (EmbeddingData.retract ed {A = proj₁ A} (lower s))
             (UX.pos-to-shape {A = proj₁ A} (lower s)
                (lower (actPOf FC′ g s p₁))))
      ∎)
  }
  where
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    C′   = StrictLayer.C (strictStep-suc L)
    FC′  = StrictLayer.FC (strictStep-suc L)
    module FCat  = Category C_L
    module C′Cat = Category C′
    open ≡-Reasoning
    UX = out x
    module UX = Unfolding UX

    -- Lower of subst along a lifted equality agrees with subst along
    -- the lowered equality (for the inner container)
    -- 沿提升等式的 subst 的降层结果与沿已降层等式的 subst 一致（对内部容器）
    bridge : ∀ {A B : Category.Obj C′}
               {s : ShapeOf FC′ A} {t : ShapeOf FC′ B}
             (g : A C′Cat.⇒ B) (p : actSOf FC′ g s ≡ t)
             (p₁ : PosOf FC′ {A = B} (actSOf FC′ g s))
           → lower (subst (PosOf FC′ {A = B}) p p₁)
             ≡ subst (PosOf FC_L {A = proj₁ B}) (cong lower p) (lower p₁)
    bridge {A} {B} {s} {t} g p p₁ =
      begin
        lower (subst (PosOf FC′ {A = B}) p p₁)
          ≡⟨ cong lower (cong (λ e → subst (PosOf FC′ {A = B}) e p₁)
                              (sym (lift-lower-cong p))) ⟩
        lower (subst (PosOf FC′ {A = B}) (cong lift (cong lower p)) p₁)
          ≡⟨ lower-subst-lift {P = PosOf FC_L {A = proj₁ B}}
                              (cong lower p) p₁ ⟩
        subst (PosOf FC_L {A = proj₁ B}) (cong lower p) (lower p₁)
      ∎

    -- Compatibility of retract with the container functor's action,
    -- transported through the source cosmos's pos-actS-compat
    -- retract 与容器函子作用的相容性，经源宇宙的 pos-actS-compat 传输
    compat : ∀ {A B : Category.Obj C_L}
               {s : ShapeOf FC_L A} {t : ShapeOf FC_L B}
            → (f : A FCat.⇒ B)
            → (q : actSOf FC_L f s ≡ t)
            → (p : PosOf FC_L (actSOf FC_L f s))
            → actSOf FC_L (EmbeddingData.retract ed t)
                (UX.pos-to-shape t (subst (PosOf FC_L) q p))
            ≡ actSOf FC_L f
                (actSOf FC_L (EmbeddingData.retract ed s)
                   (UX.pos-to-shape s (actPOf FC_L f s p)))
    compat {A} {B} {s} {t} f q p = begin
        actSOf FC_L (EmbeddingData.retract ed t)
          (UX.pos-to-shape t (subst (PosOf FC_L) q p))
        ≡⟨ cong (actSOf FC_L (EmbeddingData.retract ed t))
                (UX.pos-actS-compat f q p) ⟩
        actSOf FC_L (EmbeddingData.retract ed t) (actSOf FC_L g₁ x₀)
        ≡⟨ sym (_≈M_.shape-eq
                (Functor.homomorphism FC_L {f = g₁}
                 {g = EmbeddingData.retract ed t}) x₀) ⟩
        actSOf FC_L (EmbeddingData.retract ed t FCat.∘ g₁) x₀
        ≡⟨ sym (_≈M_.shape-eq
                (Functor.F-resp-≈ FC_L
                 {f = f FCat.∘ EmbeddingData.retract ed s}
                 {g = EmbeddingData.retract ed t FCat.∘ g₁}
                 (EmbeddingData.retract-natural ed f q)) x₀) ⟩
        actSOf FC_L (f FCat.∘ EmbeddingData.retract ed s) x₀
        ≡⟨ _≈M_.shape-eq
             (Functor.homomorphism FC_L {f = EmbeddingData.retract ed s}
                {g = f}) x₀ ⟩
        actSOf FC_L f (actSOf FC_L (EmbeddingData.retract ed s) x₀)
      ∎
      where
        x₀ = UX.pos-to-shape s (actPOf FC_L f s p)
        g₁ = Functor.₁ UX.unfoldFunctor (f , q)

-- Example: strictly-growing Unit hierarchy
-- 示例：严格增长的单位层级
module StrictUnitHierarchyExample {ℓ : Level} where

  L₀ : StrictLayer ℓ ℓ ℓ ℓ ℓ
  L₀ = record { C = UnitCat {ℓ} ; FC = UnitContainerFunctor {ℓ} }

  L₁ : StrictLayer ℓ ℓ ℓ (lsuc ℓ) (lsuc ℓ)
  L₁ = strictStep-suc L₀

  L₂ : StrictLayer (lsuc ℓ) (lsuc ℓ) ℓ (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  L₂ = strictStep-suc L₁

-- StrictFunctorialEmbeddingFamily: packages a UniformEmbeddingFamily
-- with the property that strictEmbed preserves _≈C_
-- StrictFunctorialEmbeddingFamily：将 UniformEmbeddingFamily
-- 连同 strictEmbed 保持 _≈C_ 的性质封装
record StrictFunctorialEmbeddingFamily {o h e s p}
  (L : StrictLayer o h e s p) : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    uniform : UniformEmbeddingFamily {C = StrictLayer.C L} {FC = StrictLayer.FC L}
  open UniformEmbeddingFamily uniform public
  field
    -- strictEmbed preserves bisimulation: bisimilar cosmos objects in layer L
    -- map to bisimilar cosmos objects in the strictly-raised next layer
    -- strictEmbed 保持互模拟：层 L 中互模拟的宇宙
    -- 映射为严格提升后下一层中互模拟的宇宙
    resp-≈C : ∀ {x y} → _≈C_ {C = StrictLayer.C L} {FC = StrictLayer.FC L} x y
            → _≈C_ {C = StrictLayer.C (strictStep-suc L)}
                    {FC = StrictLayer.FC (strictStep-suc L)}
                    (strictEmbed L x (getData x))
                    (strictEmbed L y (getData y))

-- StrictLambekConsistency: Lambek-consistency for the strict embedding
-- StrictLambekConsistency：严格嵌入的 Lambek 一致性
record StrictLambekConsistency {o h e s p}
  (L : StrictLayer o h e s p)
  (uniform : UniformEmbeddingFamily {C = StrictLayer.C L} {FC = StrictLayer.FC L})
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  private
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    C_L'  = StrictLayer.C (strictStep-suc L)
    FC_L' = StrictLayer.FC (strictStep-suc L)
    getData = UniformEmbeddingFamily.getData uniform
    se : Cosmos C_L FC_L → Cosmos C_L' FC_L'
    se x = strictEmbed L x (getData x)
    in-F' : Unfolding FC_L' (Cosmos C_L' FC_L') → Cosmos C_L' FC_L'
    in-F' = in-F {C = C_L'} {FC = FC_L'}
    in∘out≈id' : ∀ z → in-F' (out z) ≈C z
    in∘out≈id' = in∘out≈id {C = C_L'} {FC = FC_L'}
  field
    -- in-F′ ∘ out is bisimilar to the identity on strict embeddings
    -- in-F′ ∘ out 与严格嵌入上的恒等互模拟
    in-F-consistency : ∀ y
                     → in-F' (out (se (in-F {C = C_L} {FC = FC_L} y)))
                       ≈C se (in-F {C = C_L} {FC = FC_L} y)
    -- unfold-next commutes with strictEmbed on the lifted shape
    -- unfold-next 与 strictEmbed 在提升形状上交换
    out-consistency  : ∀ (x : Cosmos C_L FC_L) {A : Category.Obj C_L'}
                         (s : ShapeOf FC_L' A)
                     → Unfolding.unfold-next (out (se x)) {A = A} s
                       ≡ se (Unfolding.unfold-next (out x) {A = proj₁ A}
                                                    (lower s))
