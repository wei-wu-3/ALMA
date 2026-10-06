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
open import Relation.Binary.PropositionalEquality.Core using (cong)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Base.MCorrSetoid
  using (EqOn; propEqOn; FiberAdjˢ; idAdjˢ; SysEq; Stepˢ; Morphˢ)
open import ALMA.Base.MCorrSetoidCat
  using (FMapˢ; FMˢ; idFMˢ)
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
      -- Index-aware label map: the target label at S.₀ x for the source
      -- label d at x.  The old morphism builds this layerwise from the
      -- two unfoldings and the shape natural isomorphism, so it must see
      -- the source index x.
      -- 索引感知的标签映射：x 处源标签 d 在 S.₀ x 处的目标标签。旧态射
      -- 由两个 unfolding 与形状自然同构逐层构造它，故必须见到源索引 x。
      labelMap : (x : MO.I C FC) (d : MO.CosmosData C FC)
               → MO.CosmosData C FC
      pullback : (d : MO.CosmosData C FC) (v : MO.I C FC)
               → Σ (MO.I C FC) λ x' → f₀ S x' ≡ v
      edgeAdj  : (x : MO.I C FC) (d : MO.CosmosData C FC)
                 (v : MO.I C FC)
                 (pb : Σ (MO.I C FC) λ x' → f₀ S x' ≡ v)
               → FiberAdjˢ (propEqOn (MO.E C FC (f₀ S x) (labelMap x d) v))
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
      { shapeᴿ = labelMap dd x₀
      ; child   = λ d v → pullback dd d v
      ; edge-adj = λ d v → edgeAdj dd x₀ d v (pullback dd d v)
      }

  -- Construct a deterministic M-Cosmos morphism from carried data.
  -- 由携带数据构造确定性 M-Cosmos 态射。
  mkDetCosmosM⇒ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                → DetData S → DetCosmosM⇒ S
  mkDetCosmosM⇒ S dd = record { step = detStep S dd }

  ----------------------------------------------------------------------
  -- Scope of the endo instance (what recovering old _⇒ℱ[S]_ requires).
  --
  -- CosmosData (uf , pts) corresponds to Unfolding.(unfoldFunctor,
  -- pos-to-shape); a single Cosmos carries ONE such label, repeated at
  -- every node (A _ = CosmosData).  The old _⇒ℱ[S]_ is an ENDO morphism
  -- on the fixed C FC, so the target label is always the single label of
  -- the target Cosmos G: labelMap = const d_G.  No uf natural
  -- isomorphism is involved.
  --
  -- The ContCatEquivFunctor natural-isomorphism machine (H : C → D,
  -- α : FC ⟹ FD ∘ H) serves only CROSS-BASE morphisms between different
  -- FC / base categories — a generalisation strictly BEYOND the old
  -- _⇒ℱ[S]_, not part of this endo instance (which fixes C FC).  A
  -- cross-base M-Cosmos relation would relate two systems over distinct
  -- FC and is a separate construction.
  --
  -- Hence for the endo case the only substantive premises are S.₀
  -- coverage (pullback) and the per-edge position adjunction (edgeAdj);
  -- both are mathematically necessary — a bare container morphism is a
  -- contravariant pullback with no forward section.  mkDetCosmosM⇒ is
  -- therefore the complete endo answer; a non-identity S is inhabited by
  -- supplying its coverage and adjunction, never by eliminating equality.
  --
  -- 自态射实例的范围（恢复旧 _⇒ℱ[S]_ 所需）。
  --
  -- CosmosData（uf , pts）对应 Unfolding 的（unfoldFunctor,
  -- pos-to-shape）；单个 Cosmos 只携带一份这样的标签并在每个节点重复
  -- （A _ = CosmosData）。旧 _⇒ℱ[S]_ 是固定 C FC 上的自态射，故目标标签
  -- 恒为目标 Cosmos G 的那一份：labelMap = const d_G，不涉及 uf 自然同构。
  --
  -- ContCatEquivFunctor 的自然同构机器（H : C → D、α : FC ⟹ FD ∘ H）
  -- 只服务不同 FC / 基范畴之间的跨基态射——那是严格超出旧 _⇒ℱ[S]_ 的
  -- 推广，不属于本固定 C FC 的自态射实例。跨基 M-Cosmos 关系将联系不同
  -- FC 上的两个系统，是独立构造。
  --
  -- 故自态射情形唯一的实质前提是 S.₀ 覆盖（pullback）与逐边位置伴随
  -- （edgeAdj）；两者数学上均必要——裸容器态射是无正截面的反变 pullback。
  -- mkDetCosmosM⇒ 因而是自态射的完整答案；非恒等 S 通过供给其覆盖与伴随
  -- 而有 inhabitant，绝不靠消去等式。
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Identity lifting (base case of the adjunction+coverage supply).
  --
  -- The identity container morphism canonically carries the three
  -- premises: labelMap is the identity; coverage is trivial (S.₀ is the
  -- identity, so the pullback of v is (v , ≡refl)); the edge adjunction
  -- is the identity fibre adjunction (the (v , ≡refl) pattern forces the
  -- pullback source index to equal v).  This constructs DetData for the
  -- identity shape functor directly from the carried premises, validating
  -- the DetData interface end to end (independently of Det-id).
  --
  -- 恒等提升（伴随+覆盖供给的基例）。
  --
  -- 恒等容器态射典范携带三前提：labelMap 为恒等；覆盖平凡（S.₀ 为恒等，
  -- 故 v 的 pullback 为 (v , ≡refl)）；边伴随为恒等纤维伴随（(v ,
  -- ≡refl) 模式强制 pullback 源索引等于 v）。这直接由携带前提构造恒等
  -- 形状函子的 DetData，端到端验证 DetData 接口（独立于 Det-id）。
  ----------------------------------------------------------------------
  detData-id : DetData idF
  DetData.labelMap detData-id _ d = d
  DetData.pullback detData-id _ v = v , ≡refl
  DetData.edgeAdj  detData-id x d v₀ (v , ≡refl) =
    idAdjˢ (propEqOn (MO.E C FC x d v))

  ----------------------------------------------------------------------
  -- Deterministic carried FUNCTOR (FMapˢ) from DetData.
  --
  -- The pointwise fields of DetData assemble the underlying FMapˢ with
  -- no transport: u is S.₀ (whose propositional graph is the unique
  -- witness ≡refl used by asMorphˢ), shape is labelMap, the canonical
  -- child is the pullback and the edge adjunction is edgeAdj.
  --
  -- 由 DetData 构造确定性携带函子（FMapˢ）。
  --
  -- DetData 的逐点字段无传输地装配底层 FMapˢ：u 为 S.₀（其命题图即
  -- asMorphˢ 所用的唯一见证 ≡refl），shape 为 labelMap，规范子节点为
  -- pullback，边伴随为 edgeAdj。
  ----------------------------------------------------------------------
  detFMapˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
           → DetData S → FMapˢ sysP sysP
  FMapˢ.u      (detFMapˢ S dd) = f₀ S
  FMapˢ.shape  (detFMapˢ S dd) x d = labelMap dd x d
  FMapˢ.childF (detFMapˢ S dd) x d v = pullback dd d v
  FMapˢ.adjFˢ  (detFMapˢ S dd) x d v =
    edgeAdj dd x d v (pullback dd d v)

  ----------------------------------------------------------------------
  -- The categorical endomorphism bundle FMˢ.
  --
  -- A setoid functor must CARRY its congruence (FMˢ.map-cong); it cannot
  -- be reconstructed from the pointwise DetData fields.  The reason is
  -- the decisive negative boundary already recorded for MCorrCatˢ:
  -- map-cong must relate image trees whose source heads are only
  -- propositionally equal (here t ≡ here s), and the canonical child
  -- depends on that head; aligning the two children across the head
  -- equality would require either K (matching the two neutral head
  -- projections against ≡refl, rejected under --cubical-compatible) or
  -- subst.  FMapˢ deliberately drops the old childF-coh, so no such
  -- link is derivable pointwise.  The congruence is therefore supplied
  -- as data — exactly the coinductive witness the setoid category
  -- requires (the carried counterpart of the old coinductive _≈ℱ_).
  --
  -- mkDetFMˢ packages detFMapˢ together with the label congruence
  -- (cong labelMap, a legal J step since the two labels are rigid
  -- variables) and a caller-supplied coinductive tree congruence.  The
  -- identity S supplies its bundle canonically as detFMˢ-id = idFMˢ;
  -- a non-identity S supplies its map-cong from its onPos round-trip
  -- data (the gow-style coinductive engine), which is a separate
  -- construction and is never obtained by eliminating equality.
  --
  -- 范畴自态射束 FMˢ。
  --
  -- setoid 函子必须携带其同余（FMˢ.map-cong）；它无法由 DetData 的逐点
  -- 字段重建。原因即 MCorrCatˢ 已记录的决定性否定边界：map-cong 须联系
  -- 源头部仅命题相等（here t ≡ here s）的像树，而规范子节点依赖该头
  -- 部；跨头部等式对齐两个子节点要么需要 K（把两个中性头部投影匹配为
  -- ≡refl，--cubical-compatible 拒绝），要么需要 subst。FMapˢ 刻意删除
  -- 旧 childF-coh，故该联系无法逐点导出。同余因而是数据——恰为 setoid
  -- 范畴所需的余归纳见证（旧余归纳 _≈ℱ_ 的携带式对应物）。
  --
  -- mkDetFMˢ 把 detFMapˢ 与标签同余（cong labelMap，因两标签为刚性变
  -- 量而是合法 J 步骤）及调用方供给的余归纳树同余打包。恒等 S 典范地
  -- 以 detFMˢ-id = idFMˢ 供给其束；非恒等 S 由其 onPos 往返数据供给
  -- map-cong（gow 式余归纳引擎），那是独立构造，绝不靠消去等式获得。
  ----------------------------------------------------------------------
  mkDetFMˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
             (dd : DetData S)
           → ( ∀ {x : MO.I C FC} {t s : MO.CosmosM C FC x}
             → MO.≈CosmosM C FC propLabel t s
             → MO.≈CosmosM C FC propLabel
                 (FMapˢ.mapFˢ (detFMapˢ S dd) x t)
                 (FMapˢ.mapFˢ (detFMapˢ S dd) x s) )
           → FMˢ sysP sysP
  mkDetFMˢ S dd mc = record
    { mor        = detFMapˢ S dd
    ; shape-cong = λ {x = x} {a₁} {a₂} ea → cong (labelMap dd x) ea
    ; map-cong   = mc
    }

  -- The canonical deterministic identity endomorphism bundle.
  --
  -- 典范确定性恒等自态射束。
  detFMˢ-id : FMˢ sysP sysP
  detFMˢ-id = idFMˢ {X = sysP}
