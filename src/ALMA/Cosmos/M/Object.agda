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

open import ALMA.Base.MCorr using (M; _⍮_)
open import ALMA.Base.MCorrSetoid
  using (EqOn; SysEq; propEqOn; FiberAdjˢ; idAdjˢ
       ; _≈Mˢ_; here-eq; below-eq; ≈Mˢ-refl
       ; Morphˢ; compMˢ; idMˢ)
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

  -- Successor index determined by a label and a source position.
  -- 由标签与源位置确定的后继索引。
  nextOf : (i : I) (d : A i) (p : PosOf FC (proj₂ i)) → I
  nextOf (A₀ , s) d p =
    ( Functor.F₀ (uf d) (A₀ , s)
    , pts d s p )

  next : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i)) → I
  next i t p = nextOf i (M.here t) p

  step : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i))
       → CosmosM (next i t p)
  step (A₀ , s) t p =
    M.below t (next (A₀ , s) t p) (p , ≡refl)

  Rooted : (A₀ : Category.Obj C) → ShapeOf FC A₀
         → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  Rooted A₀ s₀ = CosmosM (A₀ , s₀)

  ----------------------------------------------------------------------
  -- Terminality corecursor: a one-step coalgebra over a state family
  -- Xst gives, at each index i, a label d and for every source position
  -- p a child state at nextOf i d p.  ana produces a CosmosM by the
  -- native guarded corecursion of M; the edge (p , ≡refl) is matched
  -- constructively (never J/subst).  This replaces the old
  -- seed-threaded unfold: self-reference is native.
  -- 终性余递归子：状态族 Xst 上的一步余代数在每个索引 i 给出标签 d，
  -- 并对每个源位置 p 给出 nextOf i d p 处的子状态。ana 借 M 内建的受
  -- 保护余递归产生 CosmosM；边 (p , ≡refl) 被构造性匹配（不用
  -- J/subst）。这取代了旧的经种子绕行的 unfold：自指是内建的。
  ----------------------------------------------------------------------
  record Coalgebra (u : Level) (Xst : I → Set u)
         : Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u) where
    field
      label : (i : I) → Xst i → A i
      child : (i : I) (x : Xst i) (p : PosOf FC (proj₂ i))
            → Xst (nextOf i (label i x) p)
  open Coalgebra public

  ana : ∀ {u : Level} {Xst : I → Set u}
        (γ : Coalgebra u Xst)
      → (i : I) (x : Xst i) → CosmosM i
  ana γ i x .M.here = label γ i x
  ana γ i x .M.below j (p , ≡refl) = ana γ j (child γ i x p)

  -- Observation coalgebra of a node: its state is CosmosM itself; label
  -- reads the head, child steps along the edge.  ana of this coalgebra
  -- rebuilds the tree.  The eta/terminal lemma ana-unfold shows the
  -- rebuild is bisimilar to the original, up to the carried label EqOn.
  -- 节点的观察余代数：状态即 CosmosM；label 读头部，child 沿边 step。
  -- 对该余代数取 ana 即重建该树。eta/终性引理 ana-unfold 表明重建树在
  -- 携带标签 EqOn 下与原树互模拟。
  unfold-coalgebra : Coalgebra (o ⊔ h ⊔ e ⊔ s ⊔ p) CosmosM
  unfold-coalgebra .label i t = M.here t
  unfold-coalgebra .child i t p = step i t p

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

  ----------------------------------------------------------------------
  -- Terminality / eta: ana of a node's observation coalgebra rebuilds
  -- a tree bisimilar to the original, up to the carried label EqOn.
  -- 终性 / eta：对节点观察余代数取 ana，重建出与原树在携带标签 EqOn
  -- 下互模拟的树。
  ----------------------------------------------------------------------
  mutual
    ana-unfold : ∀ {ℓd : Level}
                 (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
               → ∀ {i : I} (t : CosmosM i)
               → ≈CosmosM ≈CD (ana unfold-coalgebra i t) t
    ana-unfold ≈CD {i = i} t .here-eq = EqOn.refl (≈CD i)
    ana-unfold ≈CD {i = i} t .below-eq y =
        idAdjˢ (SysEq.≈E (sys ≈CD) i (M.here t) y)
      , ( (λ { (p , ≡refl) → ana-unfold ≈CD (step i t p) })
        , (λ { (p , ≡refl) → ana-unfold˘ ≈CD (step i t p) }) )

    ana-unfold˘ : ∀ {ℓd : Level}
                  (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
                → ∀ {i : I} (t : CosmosM i)
                → ≈CosmosM ≈CD t (ana unfold-coalgebra i t)
    ana-unfold˘ ≈CD {i = i} t .here-eq = EqOn.refl (≈CD i)
    ana-unfold˘ ≈CD {i = i} t .below-eq y =
        idAdjˢ (SysEq.≈E (sys ≈CD) i (M.here t) y)
      , ( (λ { (p , ≡refl) → ana-unfold˘ ≈CD (step i t p) })
        , (λ { (p , ≡refl) → ana-unfold ≈CD (step i t p) }) )

  ----------------------------------------------------------------------
  -- Carried correspondences between M-Cosmos nodes.
  --
  -- A CosmosM⇒ is a MCorrSetoid Morphˢ over an arbitrary index relation
  -- R; R need not be propositional (it may carry ShapeCat morphism data
  -- up to C._≈_).  The categorical identity and composition are the
  -- generic carried ones (idMˢ on the index path groupoid, compMˢ via
  -- compAdjˢ) instantiated at sys: they contain no subst.
  --
  -- The DETERMINISTIC endomorphism of the old code (_⇒ℱ[S]_, with the
  -- reverse onPos map and pts-compat / onActP) is recovered at the
  -- container instance by taking R to be the graph of S.₀ and the edge
  -- FiberAdjˢ to be onPosAdj; see ContainerInstance.
  --
  -- M-Cosmos 节点间的携带式对应。
  --
  -- CosmosM⇒ 是任意索引关系 R 上的 MCorrSetoid Morphˢ；R 不必是命题的
  -- （可携带 C._≈_ 下的 ShapeCat 态射数据）。范畴恒等与复合即通用携带
  -- 版本（索引路径广群上的 idMˢ、经 compAdjˢ 的 compMˢ）在 sys 处的
  -- 实例化：不含 subst。
  --
  -- 旧代码的确定性自态射（_⇒ℱ[S]_，含反向 onPos 与 pts-compat /
  -- onActP）在容器实例处通过令 R 为 S.₀ 的图、边 FiberAdjˢ 为
  -- onPosAdj 而恢复；见 ContainerInstance。
  ----------------------------------------------------------------------
  CosmosM⇒ : ∀ {ℓd ℓr : Level}
             (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
             (R : I → I → Set ℓr)
           → Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ ℓd ⊔ ℓr)
  CosmosM⇒ ≈CD R = Morphˢ (sys ≈CD) (sys ≈CD) R

  idCosmosM : ∀ {ℓd : Level}
              (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
            → CosmosM⇒ ≈CD (λ (x y : I) → x ≡ y)
  idCosmosM ≈CD = idMˢ (sys ≈CD)

  compCosmosM : ∀ {ℓd ℓ₁ ℓ₂ : Level}
                (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
              → ∀ {R : I → I → Set ℓ₁} {S : I → I → Set ℓ₂}
              → CosmosM⇒ ≈CD R → CosmosM⇒ ≈CD S
              → CosmosM⇒ ≈CD (R ⍮ S)
  compCosmosM ≈CD φ ψ = compMˢ φ ψ
