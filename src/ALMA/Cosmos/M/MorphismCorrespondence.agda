------------------------------------------------------------------------
-- Structured carried endomorphisms versus coalgebra homomorphisms:
-- the non-fullness counterexample, rebuilt on the M base.
--
-- Legacy result (Cosmos/MorphismCorrespondence + Cosmos/ListCosmos):
-- every CoalgHom induces a StructuredFunc (the forgetful map), but the
-- inclusion is NOT full — otherSF (the constant OtherCosmos relabelling,
-- pos-to-shape = 0, witnessed by the one-way simulation toOther) is a
-- StructuredFunc yet fails the coalgebra commutation at ListCosmos,
-- shape 2, position pos2 = fsuc fzero (child shape 1 vs 0).
--
-- M-base reconstruction.  Two things change, both sharpening the result:
--
--   1. A carried categorical morphism FMˢ must CARRY an index pullback
--      (coverage) and a whole-fibre adjunction FiberAdjˢ (a forward
--      section together with both round-trips); see
--      ContainerInstance.DetData.  The legacy collapse toOther
--      (shapeTrans = 0, onPos = id) has NEITHER: the constant index map
--      is not surjective (no pullback for target shapes ≠ 0) and the
--      position fibres have different cardinality (Fin n vs Fin 0), so no
--      fibre bijection exists.  The one-way collapse simulation is
--      therefore refused as a morphism altogether — it is not even a
--      StructuredEndo here.  This is the _⊣_ hypothesis made explicit:
--      a bare contravariant container morphism carries no forward
--      section.
--
--   2. The genuine non-fullness is nevertheless witnessed by a morphism
--      that DOES carry a fibre bijection: the swap01 label-changing
--      deterministic endomorphism swapFMˢ (see ListSwap).  Applied to the
--      constant dList tree it produces the constant dSwap tree, whose
--      head label routes position 0 of shape 2 to child shape 1, whereas
--      dList routes it to 0.  The two trees are not bisimilar (the head
--      labels are not propositionally equal), so swapFMˢ is a carried
--      structured endomorphism that is NOT a coalgebra endomorphism.
--
-- The forward inclusion (every coalgebra homomorphisms into the terminal
-- coalgebra is, up to bisimulation, the anamorphism) is the terminality
-- theorem !-unique in CoalgCat.  This module supplies the strictness
-- witness: the forgetful map is not full.  Everything is propositional
-- and constructive; no subst, no K/UIP — the head mismatch is absorbed by
-- the empty pattern, exactly as in the legacy proof.
--
-- 结构化携带自态射与余代数同态：在 M 底座上重建的非满性反例。
--
-- 旧结果（Cosmos/MorphismCorrespondence + Cosmos/ListCosmos）：每个
-- CoalgHom 诱导一个 StructuredFunc（忘却映射），但该包含非满——
-- otherSF（常值 OtherCosmos 重标签，pos-to-shape = 0，由单向模拟
-- toOther 见证）是 StructuredFunc，却在 ListCosmos 的形状 2、位置
-- pos2 = fsuc fzero 处不满足余代数交换（子形状 1 对 0）。
--
-- M 底座重建。两处变化都使结论更锐利：
--
--   1. 携带式范畴态射 FMˢ 必须携带索引 pullback（覆盖）与整纤维伴随
--      FiberAdjˢ（正截面及两条往返律），见
--      ContainerInstance.DetData。旧折叠 toOther（shapeTrans = 0、
--      onPos = id）两者皆无：常值索引映射不满（形状 ≠ 0 的目标无
--      pullback），位置纤维基数不同（Fin n 对 Fin 0），不存在纤维双
--      射。故单向折叠模拟在新塔根本不被承认为态射，甚至不是
--      StructuredEndo。这是显式化的 _⊣_ 假设：裸反变容器态射不携带
--      正截面。
--
--   2. 尽管如此，真正的非满性由一个确带纤维双射的态射见证：swap01
--      改标签确定性自态射 swapFMˢ（见 ListSwap）。作用于常 dList 树
--      得到常 dSwap 树，其头标签把形状 2 的位置 0 路由到子形状 1，而
--      dList 路由到 0。两树不互模拟（头标签不命题相等），故 swapFMˢ
--      是携带式结构化自态射，却不是余代数自态射。
--
-- 正向包含（每个到终余代数的余代数同态在互模拟意义下即 anamorphism）
-- 即 CoalgCat 的终性定理 !-unique。本模块供给严格性见证：忘却映射非
-- 满。全部命题且构造性；无 subst、无 K/UIP——头部失配由空模式吸收，
-- 与旧证明一致。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.M.MorphismCorrespondence where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

open import ALMA.Base.MCorrSetoid using (propEqOn; here-eq)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.ListSwap as LS

------------------------------------------------------------------------
-- The list universe and the carried system, reused from ListSwap.
-- 列表宇宙与携带系统，复用 ListSwap。
------------------------------------------------------------------------
private
  C₀ = LS.C₀
  ListFC = LS.ListFC

  sysP = MO.sys C₀ ListFC (λ _ → propEqOn _)

  dList = LS.dList
  dSwap = LS.dSwap

  ----------------------------------------------------------------------
  -- A StructuredEndo is a carried congruent system endomorphism (an FMˢ
  -- bundle): it induces a tree map mapFˢ and carries its own label/tree
  -- congruence.  This is the M-base counterpart of the legacy
  -- StructuredFunc (a function f : T → T carrying _⇒ℱ_ witnesses).
  --
  -- StructuredEndo 是携带式同余系统自态射（FMˢ 束）：它诱导树映射
  -- mapFˢ 并自带标签/树同余。这是旧 StructuredFunc（携带 _⇒ℱ_ 见证
  -- 的函数 f : T → T）的 M 底座对应物。
  ----------------------------------------------------------------------
  StructuredEndo : Set lzero
  StructuredEndo = FMˢ sysP sysP

  -- The swap01 label-changing structured endomorphism (carried fibre
  -- bijection, index-preserving u = id), reused from ListSwap.
  --
  -- swap01 改标签结构化自态射（携带纤维双射，索引保持 u = id），复用
  -- 自 ListSwap。
  swapSF : StructuredEndo
  swapSF = LS.swapFMˢ

  -- A structured endomorphism is a coalgebra endomorphism exactly when
  -- its induced tree map commutes with the terminal observation
  -- coalgebra at every node, i.e. it fixes every tree up to ≈CosmosM.
  -- The terminality theorem (!-unique in CoalgCat) says a coalgebra
  -- homomorphism into the terminal coalgebra is, up to bisimulation, the
  -- anamorphism; this predicate is that commutation at the tree level.
  --
  -- 一个结构化自态射是余代数自态射，当且仅当其诱导树映射在每个节点
  -- 与终观察余代数交换，即在 ≈CosmosM 下固定每棵树。终性定理
  -- （CoalgCat 的 !-unique）表明到终余代数的余代数同态在互模拟意义下
  -- 即 anamorphism；此谓词即树级交换。
  -- The coalgebra-endo commutation for an INDEX-PRESERVING structured
  -- endomorphism (the GenDet S = id regime: u is definitionally the
  -- identity, so the mapped tree lives at the same index and can be
  -- compared without any relocation): its tree map fixes every tree up
  -- to ≈CosmosM.  swapFMˢ is index-preserving (u = id), so the predicate
  -- is stated concretely at it; a general FMˢ with non-identity u is a
  -- map between distinct indices and is not a terminal-coalgebra
  -- endomorphism in this sense.
  --
  -- 索引保持型结构化自态射（GenDet S = id 制度：u 定义性为恒等，故像树
  -- 与原树同索引，无需重定位即可比较）的余代数自态射交换：树映射在
  -- ≈CosmosM 下固定每棵树。swapFMˢ 索引保持（u = id），故谓词对其具体
  -- 陈述；u 非恒等的一般 FMˢ 是不同索引间的映射，不属于此意义下的终余
  -- 代数自态射。
  swap-commutes : Set lzero
  swap-commutes =
    ∀ (i : MO.I C₀ ListFC) (t : MO.CosmosM C₀ ListFC i)
    → MO.≈CosmosM C₀ ListFC (λ _ → propEqOn _)
        (FMapˢ.mapFˢ (FMˢ.mor swapSF) i t) t

  ----------------------------------------------------------------------
  -- The constant dList coalgebra: a single state, head label dList at
  -- every index, every child the unique state.
  --
  -- 常 dList 余代数：单一状态，每个索引处头标签为 dList，每个子节点
  -- 为唯一状态。
  ----------------------------------------------------------------------
  γList : MO.Coalgebra C₀ ListFC lzero (λ _ → ⊤)
  MO.Coalgebra.label γList _ tt = dList
  MO.Coalgebra.child γList _ tt _ = tt

  -- The constant dList tree at an index.
  -- 某索引处的常 dList 树。
  listTree : (i : MO.I C₀ ListFC) → MO.CosmosM C₀ ListFC i
  listTree i = MO.ana C₀ ListFC γList i tt

  -- The image of the constant dList tree under the swap structured
  -- endomorphism: a constant dSwap tree (the head is σlabel dList).
  --
  -- 常 dList 树在 swap 结构化自态射下的像：常 dSwap 树（头部为
  -- σlabel dList）。
  swappedTree : (i : MO.I C₀ ListFC) → MO.CosmosM C₀ ListFC i
  swappedTree i = FMapˢ.mapFˢ (FMˢ.mor LS.swapFMˢ) i (listTree i)

  ----------------------------------------------------------------------
  -- Pointwise failure at shape 2, position fzero.
  --
  --   pts dList 2 fzero = toℕ fzero                 = 0
  --   pts dSwap 2 fzero = toℕ (swap01 2 fzero)
  --                     = toℕ (opposite fzero)      = 1
  --
  -- The n = 2 clause of swap01 is definitionally opposite (see
  -- ListSwap), so this is a definitional 1 vs 0 mismatch.  A bisimulation
  -- would carry a head-label equality dSwap ≡ dList; projecting the
  -- routing at shape 2 position fzero yields 1 ≡ 0, which is absurd.
  --
  -- 形状 2、位置 fzero 处的点态失败。
  --
  --   pts dList 2 fzero = toℕ fzero                 = 0
  --   pts dSwap 2 fzero = toℕ (swap01 2 fzero)
  --                     = toℕ (opposite fzero)      = 1
  --
  -- swap01 的 n = 2 子句定义性为 opposite（见 ListSwap），故这是定义
  -- 性的 1 对 0 失配。互模拟会携带头标签等式 dSwap ≡ dList；投影出形
  -- 状 2、位置 fzero 处的路由得到 1 ≡ 0，矛盾。
  ----------------------------------------------------------------------
  swap-not-commute :
    ¬ MO.≈CosmosM C₀ ListFC (λ _ → propEqOn _)
        (swappedTree (tt , 2)) (listTree (tt , 2))
  swap-not-commute b
    with cong (λ d → MO.CosmosData.pts d 2 fzero) (here-eq b)
  ... | ()

  ----------------------------------------------------------------------
  -- swapFMˢ is a StructuredEndo but not a coalgebra endomorphism.
  -- swapFMˢ 是 StructuredEndo，但不是余代数自态射。
  ----------------------------------------------------------------------
  swapSF-not-CoalgEndo : ¬ swap-commutes
  swapSF-not-CoalgEndo h =
    swap-not-commute (h (tt , 2) (listTree (tt , 2)))

  ----------------------------------------------------------------------
  -- Unconditional non-fullness: there is a carried structured
  -- endomorphism whose induced tree map does not commute with the
  -- terminal coalgebra.  This is the M-base counterpart of the legacy
  -- not-full : the forgetful map CoalgHom → StructuredFunc is not full.
  --
  -- 无条件非满性：存在携带式结构化自态射，其诱导树映射不与终余代数
  -- 交换。这是旧 not-full 的 M 底座对应物：忘却映射
  -- CoalgHom → StructuredFunc 非满。
  ----------------------------------------------------------------------
  not-full : Σ StructuredEndo λ _ → ¬ swap-commutes
  not-full = swapSF , swapSF-not-CoalgEndo
