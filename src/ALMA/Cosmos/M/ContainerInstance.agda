------------------------------------------------------------------------
-- Container instance of the M-Cosmos: type seam
--
-- This module pins down where the OLD container Cosmos (the terminal
-- coalgebra with its deterministic shape-functor morphisms _⇒ℱ[S]_)
-- lives as a SPECIAL CASE of the strictly stronger M-Cosmos.
--
-- The old morphism _⇒ℱ[S]_ is parameterised by a shape endofunctor
-- S : Functor (ShapeCat C FC) (ShapeCat C FC).  The objects of
-- ShapeCat are exactly the M-Cosmos index I = Σ Obj Shape.  Hence:
--
--   * the index relation R is the PROPOSITIONAL GRAPH of S.₀:
--         Graph S i j = S.₀ i ≡ j ;
--   * the label EqOn is propositional (propEqOn on CosmosData): in the
--     container regime labels are compared up to propositional equality;
--   * the edge FiberAdjˢ is the onPos adjunction (fro = onPos), with
--     η/ε replacing the old pts-compat / onActP (no subst).
--
-- DetCosmosM⇒ S is therefore the exact carried type of the old
-- _⇒ℱ[S]_; inhabiting it from an onPos map and the round-trip laws is
-- the next slice.  The general M-Cosmos strictly generalises this by
-- allowing a non-propositional label EqOn (natural isomorphism at
-- C._≈_) and an arbitrary (non-graph) index relation.
--
-- M-Cosmos 的容器实例：类型接缝
--
-- 本模块钉住旧容器 Cosmos（带确定性形状函子态射 _⇒ℱ[S]_ 的终余代数）
-- 作为严格更强 M-Cosmos 的特例所处的位置。
--
-- 旧态射 _⇒ℱ[S]_ 以形状自函子 S : Functor (ShapeCat C FC)
-- (ShapeCat C FC) 为参数。ShapeCat 的对象恰为 M-Cosmos 索引
-- I = Σ Obj Shape。因此：
--
--   * 索引关系 R 是 S.₀ 的命题图：Graph S i j = S.₀ i ≡ j；
--   * 标签 EqOn 是命题的（CosmosData 上的 propEqOn）：容器制度下标签
--     按命题相等比较；
--   * 边 FiberAdjˢ 是 onPos 伴随（fro = onPos），η/ε 取代旧
--     pts-compat / onActP（不用 subst）。
--
-- 故 DetCosmosM⇒ S 正是旧 _⇒ℱ[S]_ 的携带式类型；由 onPos 映射与往返
-- 律构造其 inhabitant 是下一切片。一般 M-Cosmos 严格地推广它：允许非
-- 命题标签 EqOn（C._≈_ 处的自然同构）与任意（非图）索引关系。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ContainerInstance where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Base.MCorrSetoid
  using (EqOn; propEqOn; FiberAdjˢ; SysEq; Stepˢ; Morphˢ)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  -- The propositional graph of a shape endofunctor on the index.
  -- 形状自函子在索引上的命题图。
  Graph : Functor (ShapeCat C FC) (ShapeCat C FC)
        → MO.I C FC → MO.I C FC → Set (o ⊔ s)
  Graph S i j = Functor.F₀ S i ≡ j

  -- Propositional label equivalence: the container regime.
  -- 命题标签等价：容器制度。
  propLabel : (i : MO.I C FC)
            → EqOn {ℓ = o ⊔ h ⊔ e ⊔ s ⊔ p} (MO.CosmosData C FC)
  propLabel _ = propEqOn _

  -- The carried type of the old deterministic _⇒ℱ[S]_: a M-Cosmos
  -- correspondence over the propositional graph of S with propositional
  -- labels.  Inhabiting it is the onPos/η/ε construction (next slice).
  -- 旧确定性 _⇒ℱ[S]_ 的携带式类型：S 的命题图上、命题标签的 M-Cosmos
  -- 对应。其 inhabitant 为 onPos/η/ε 构造（下一切片）。
  DetCosmosM⇒ : Functor (ShapeCat C FC) (ShapeCat C FC)
              → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  DetCosmosM⇒ S = MO.CosmosM⇒ C FC propLabel (Graph S)

  -- The identity shape functor gives the identity deterministic Cosmos
  -- morphism: Graph id is (definitionally) the index path relation, so
  -- the carried morphism is idCosmosM.  This recovers the old id⇒ℱ (the
  -- only deterministic endomorphism that exists canonically).
  --
  -- 恒等形状函子给出恒等确定性 Cosmos 态射：Graph id（定义地）即索引
  -- 路径关系，故携带态射为 idCosmosM。这恢复了旧 id⇒ℱ（唯一典范存在
  -- 的确定性自态射）。
  Det-id : DetCosmosM⇒ idF
  Det-id = MO.idCosmosM C FC propLabel

  ----------------------------------------------------------------------
  -- Carried construction data for a deterministic S-morphism.
  --
  -- The old MorphismObject/MorphismMorphism only carry ONE direction of
  -- the position map (onPos, the reverse/fro side); the forward embedding
  -- and the round-trip laws were reconstructed by subst along the shape
  -- equations.  In the carried architecture those become FIRST-CLASS
  -- DATA with no equality:
  --
  --   labelMap : the per-layer label (uf/pts) map;
  --   pullback : surjectivity/coverage of S.₀ — for every target index v
  --              a source index x' with S.₀ x' ≡ v (the deterministic
  --              analogue of MCorr's FMap.childF);
  --   edgeAdj  : the fibre adjunction at every edge, where fro is the old
  --              onPos and to/η/ε are the carried replacements for
  --              pts-compat / onActP (no subst).
  --
  -- A deterministic M-Cosmos morphism therefore exists only when the
  -- container morphism genuinely carries the adjunction (onPos has a
  -- forward section).  This is the _⊣_ hypothesis made explicit; it is not
  -- derivable for an arbitrary non-surjective onPos.
  --
  -- 确定性 S-态射的携带式构造数据。
  --
  -- 旧 MorphismObject/MorphismMorphism 只携带位置映射的一个方向
  -- （onPos，反向 fro 侧）；正向嵌入与往返律当年靠沿形状等式 subst 补
  -- 造。携带式架构把它们变为不含等式的一等数据：
  --
  --   labelMap：每层标签（uf/pts）映射；
  --   pullback：S.₀ 的满射/覆盖——每个目标索引 v 给出源索引 x' 使
  --             S.₀ x' ≡ v（MCorr FMap.childF 的确定性对应物）；
  --   edgeAdj ：每条边上的纤维伴随，fro 即旧 onPos，to/η/ε 是
  --             pts-compat / onActP 的携带式替代（无 subst）。
  --
  -- 故确定性 M-Cosmos 态射仅当容器态射确带伴随（onPos 有正截面）时存
  -- 在。这是显式化的 _⊣_ 假设；任意非满射 onPos 无法导出它。
  ----------------------------------------------------------------------
  private
    f₀ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
       → MO.I C FC → MO.I C FC
    f₀ S = Functor.F₀ S

    sysP = MO.sys C FC propLabel

  record DetData (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    field
      labelMap : MO.CosmosData C FC → MO.CosmosData C FC
      pullback : (d : MO.CosmosData C FC) (v : MO.I C FC)
               → Σ (MO.I C FC) λ x' → f₀ S x' ≡ v
      edgeAdj  : (x : MO.I C FC) (d : MO.CosmosData C FC)
                 (v : MO.I C FC)
                 (pb : Σ (MO.I C FC) λ x' → f₀ S x' ≡ v)
               → FiberAdjˢ (propEqOn (MO.E C FC (f₀ S x) (labelMap d) v))
                            (propEqOn (MO.E C FC x d (proj₁ pb)))
  open DetData public

  -- One deterministic step: matching the graph witness ≡refl pins the
  -- target index to S.₀ x; child is the supplied pullback and edge-adj is
  -- the supplied adjunction.  No equality is ever eliminated.
  --
  -- 一个确定性步：匹配图见证 ≡refl 把目标索引钉为 S.₀ x；child 取所供
  -- pullback，edge-adj 取所供伴随。不消去任何等式。
  private
    detStep : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (dd : DetData S)
            → ∀ {x y : MO.I C FC} (r : Graph S x y)
            → Stepˢ sysP sysP (Graph S) r
    detStep S dd {x = x₀} {y = .(f₀ S x₀)} ≡refl = record
      { shapeᴿ = labelMap dd
      ; child   = λ d v → pullback dd d v
      ; edge-adj = λ d v → edgeAdj dd x₀ d v (pullback dd d v)
      }

  -- Construct a deterministic M-Cosmos morphism from carried data.
  -- 由携带数据构造确定性 M-Cosmos 态射。
  mkDetCosmosM⇒ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                → DetData S → DetCosmosM⇒ S
  mkDetCosmosM⇒ S dd = record { step = detStep S dd }
