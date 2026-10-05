------------------------------------------------------------------------
-- Cosmos rebuilt on the setoid-parameterised M base: object layer
--
-- This is the strictly stronger M-Cosmos.  The index is a base object
-- together with a shape; the label at a node carries the unfolding
-- functor uf and the position-to-shape map pts; an edge is a source
-- position together with the HOMOGENEOUS equation pinning the target
-- index to uf/pts applied at that position.
--
-- Where the two equalities live (decisive design point):
--   * The edge/index equation is propositional and CONSTRUCTIVE: edges
--     are always introduced as (p , refl), exactly like MCorr's
--     identity/child graph witnesses.  It is never eliminated with J or
--     subst, so it carries no transport debt.  Base OBJECTS and shapes
--     are legitimately propositional (a Category has no setoid on its
--     objects); the non-propositional C._≈_ equates morphisms, not
--     objects.
--   * The non-propositional equivalence lives in the LABEL: two nodes'
--     uf functors may be related up to the base-category setoid
--     (natural isomorphism).  It is carried as the label EqOn ≈CD, an
--     argument to sys / ≈CosmosM.  The container instance supplies the
--     propositional EqOn (see ContainerInstance); the general category
--     supplies a natural-isomorphism EqOn at the morphism layer.
--   * Position edges are sets, so their fibre EqOn is propositional.
--
-- The object system is packaged as a MCorrSetoid SysEq; the coinductive
-- bisimulation _≈Mˢ_ relates nodes up to the carried label EqOn rather
-- than propositional field equality.
--
-- 在 setoid 参数化 M 底座上重建的 Cosmos：对象层
--
-- 这是严格更强的 M-Cosmos。索引为基对象连同形状；节点标签携带展开
-- 函子 uf 与位置到形状映射 pts；边是源位置连同把目标索引钉为该位置
-- 处 uf/pts 作用结果的同质等式。
--
-- 两类等式的位置（决定性设计点）：
--   * 边/索引等式是命题且构造性的：边总以 (p , refl) 引入，恰如
--     MCorr 的恒等/child 图见证。绝不用 J 或 subst 消去，故不携带传输
--     债务。基对象与形状合法地是命题的（范畴在对象上无 setoid）；非
--     命题 C._≈_ 联系的是态射而非对象。
--   * 非命题等价活在标签层：两节点的 uf 函子可在底范畴 setoid（自然
--     同构）意义下相关。它作为标签 EqOn ≈CD（sys / ≈CosmosM 的参数）
--     被携带。容器实例提供命题 EqOn（见 ContainerInstance）；一般范畴
--     在态射层提供自然同构 EqOn。
--   * 位置边是集合，故其纤维 EqOn 是命题的。
--
-- 对象系统打包为 MCorrSetoid 的 SysEq；余归纳互模拟 _≈Mˢ_ 按携带的
-- 标签 EqOn（而非命题字段相等）联系节点。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.Object where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (EqOn; SysEq; propEqOn; _≈Mˢ_; ≈Mˢ-refl)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  ----------------------------------------------------------------------
  -- Index: a base object together with a shape over it.
  -- 索引：基对象连同其上的形状。
  ----------------------------------------------------------------------
  I : Set (o ⊔ s)
  I = Σ (Category.Obj C) (ShapeOf FC)

  ----------------------------------------------------------------------
  -- Per-layer unfolding data (uf + pts); the other two old Unfolding
  -- fields have native counterparts in M (below) and the morphism layer.
  -- 每层展开数据（uf + pts）；旧 Unfolding 的另两字段在 M（below）与
  -- 态射层有原生对应。
  ----------------------------------------------------------------------
  record CosmosData : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    field
      uf  : Functor (ShapeCat C FC) C
      pts : ∀ {A} (s : ShapeOf FC A) → PosOf FC s
          → ShapeOf FC (Functor.F₀ uf (A , s))
  open CosmosData public

  A : I → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  A _ = CosmosData

  ----------------------------------------------------------------------
  -- Edge: a source position plus the constructive homogeneous equation
  -- pinning the target index.  Always introduced as (p , ≡refl); never
  -- eliminated by J/subst.
  -- 边：源位置加钉住目标索引的构造性同质等式。总以 (p , ≡refl) 引入；
  -- 绝不用 J/subst 消去。
  ----------------------------------------------------------------------
  E : (i : I) (d : A i) (j : I) → Set (o ⊔ s ⊔ p)
  E (A₀ , s) d (A₁ , s₁) =
    Σ (PosOf FC s) λ p →
      (A₁ , s₁) ≡ ( Functor.F₀ (uf d) (A₀ , s)
                  , pts d s p )

  ----------------------------------------------------------------------
  -- Nodes and the derived step / root.
  -- 节点与派生的 step / root。
  ----------------------------------------------------------------------
  CosmosM : I → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  CosmosM i = M A E i

  next : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i)) → I
  next (A₀ , s) t p =
    ( Functor.F₀ (uf (M.here t)) (A₀ , s)
    , pts (M.here t) s p )

  step : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i))
       → CosmosM (next i t p)
  step (A₀ , s) t p =
    M.below t (next (A₀ , s) t p) (p , ≡refl)

  Rooted : (A₀ : Category.Obj C) → ShapeOf FC A₀
         → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  Rooted A₀ s₀ = CosmosM (A₀ , s₀)

  ----------------------------------------------------------------------
  -- The object system as a SysEq carrying a label EqOn ≈CD; position
  -- fibres use the propositional EqOn.  ≈CD is the single seam at which
  -- the equivalence regime (propositional vs natural-isomorphism) is
  -- chosen.
  -- 对象系统作为携带标签 EqOn ≈CD 的 SysEq；位置纤维取命题 EqOn。
  -- ≈CD 是选择等价制度（命题还是自然同构）的唯一接缝。
  ----------------------------------------------------------------------
  sys : ∀ {ℓd : Level}
        (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
      → SysEq (o ⊔ s) (o ⊔ h ⊔ e ⊔ s ⊔ p) (o ⊔ s ⊔ p) ℓd (o ⊔ s ⊔ p)
  sys ≈CD = record
    { I  = I
    ; A  = A
    ; E  = E
    ; ≈A = ≈CD
    ; ≈E = λ i d j → propEqOn (E i d j)
    }

  ----------------------------------------------------------------------
  -- Coinductive bisimulation up to the carried label EqOn.
  -- 在携带标签 EqOn 下的余归纳互模拟。
  ----------------------------------------------------------------------
  ≈CosmosM : ∀ {ℓd : Level}
             (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
           → ∀ {i : I} → CosmosM i → CosmosM i
           → Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ ℓd)
  ≈CosmosM ≈CD = _≈Mˢ_ (SysEq.≈A (sys ≈CD)) (SysEq.≈E (sys ≈CD))

  ≈CosmosM-refl : ∀ {ℓd : Level}
                  (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
                → ∀ {i : I} (t : CosmosM i) → ≈CosmosM ≈CD t t
  ≈CosmosM-refl ≈CD = ≈Mˢ-refl (SysEq.≈A (sys ≈CD)) (SysEq.≈E (sys ≈CD))
