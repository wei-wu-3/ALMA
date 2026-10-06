------------------------------------------------------------------------
-- Conditional non-triviality of a limit, rebuilt on the carried M base.
--
-- M-base replacement for the legacy Cosmos/ConditionalNontrivialLimit.agda.
-- The legacy file defined an ideal universal limit over an enriched
-- tower, called the target "trivial" when every cosmos in it is
-- bisimilar (AllCosmosBisim), and showed that no non-trivial limit
-- (one whose liftAt separates a pair) can land in such a target; it
-- then recorded, CONDITIONALLY on an injectivity hypothesis lift0-inj,
-- that the FinCat n tower carries a separated pair.
--
-- On the carried M base the same fact is expressed without any of the
-- legacy StrictLayer / Embed / subst machinery, and it splits into three
-- constructive pieces:
--
--   1. Totality.  A target fibre is "trivial" when its bisimulation is
--      total: AllBisim j holds iff any two nodes at j are related.  A
--      total fibre admits no distinguished (negated-bisimulation) pair
--      (no-distinguishing-pair).
--
--   2. Reflection dichotomy.  A limit's liftAt is a map L from source
--      nodes to target nodes.  The only way a source separation can be
--      SEEN at the target is for L to REFLECT bisimulation
--      (target-bisimulation implies source-bisimulation -- the carried
--      form of the legacy lift0-inj).  Reflection preserves separation
--      (separation-survives, a one-line contrapositive), and therefore a
--      reflecting lift into a total target forces the SOURCE to be total
--      too (total-target-collapses): a genuinely separated source cannot
--      have a reflecting lift into a trivial target.  This is the M form
--      of no-nontrivial-limit-of-singleton-target (no-nontrivial-limit).
--
--   3. Terminality supplies the trivial target.  The terminal M-Cosmos
--      is CosmosM with unfold-coalgebra; any candidate mediating map m
--      carrying its commutation is bisimilar to the anamorphism
--      (terminal-unique, = ana-unfold˘ then comm), so any two mediating
--      maps have pointwise-bisimilar images
--      (terminal-mediators-coincide).  A limit whose target is terminal
--      therefore collapses every cone to one image: it cannot separate.
--
-- The genuinely separated SOURCE that makes a limit non-trivial is not
-- rebuilt here: it is the M-tower witness idN ≉ const0N over FinCat n
-- (n ≥ 2) in Cosmos/M/TowerSeparation (slice 13), with the routing
-- divergence of non-commuting permutations in
-- Cosmos/M/PermutationNonCommutative (slice 14) supplying the group-
-- level precondition.  Combining that source x≉y with any concrete
-- reflecting lift is exactly separation-survives below.  Nothing here
-- uses subst, cast, Maybe, K or UIP: totality is a carried hypothesis,
-- reflection is a carried function, and terminality is the eta pair.
--
-- 在携带式 M 底座上重建的极限条件性非平凡性。
--
-- 旧 Cosmos/ConditionalNontrivialLimit.agda 的 M 底座替代。旧文件定义
-- 丰富塔上理想的泛极限，把“其中所有宇宙互模拟”的目标称为平凡目标
-- （AllCosmosBisim），证明非平凡极限（其 liftAt 能区分一对）不能落入
-- 这种目标；并在单射假设 lift0-inj 下条件性地记录 FinCat n 塔携带分离
-- 对。
--
-- 在携带式 M 底座上，同一事实无需任何旧 StrictLayer / Embed / subst
-- 机器，分为三个构造性片段：
--
--   1. 全体性。目标纤维在其互模拟为全关系时“平凡”：AllBisim j 即 j
--      处任意两节点都相关。全纤维不允许被区分（互模拟之否定）的对
--      （no-distinguishing-pair）。
--
--   2. 反射二分。极限的 liftAt 是从源节点到目标节点的映射 L。源分离
--      能在目标被“看见”的唯一方式，是 L 反射互模拟（目标互模拟蕴含源
--      互模拟——即旧 lift0-inj 的携带式形态）。反射保持分离
--      （separation-survives，一行逆否命题），因此向全目标的反射提升
--      迫使源也全体（total-target-collapses）：真正分离的源不可能有向
--      平凡目标的反射提升。这就是 no-nontrivial-limit-of-singleton-
--      target 的 M 形态（no-nontrivial-limit）。
--
--   3. 终性给出平凡目标。终 M-Cosmos 是带 unfold-coalgebra 的
--      CosmosM；任何携带交换的候选中介映射 m 都与 anamorphism 互模拟
--      （terminal-unique，= ana-unfold˘ 再接交换），故任意两个中介映
--      射的像逐点互模拟（terminal-mediators-coincide）。目标为终对象
--      的极限因此把每个锥塌缩为单一像：它无法分离。
--
-- 使极限非平凡的真正被分离“源”不在此重建：它是 FinCat n（n ≥ 2）上
-- 的 M 塔见证 idN ≉ const0N，见 Cosmos/M/TowerSeparation（切片13）；
-- 非交换置换的路由发散（切片14
-- Cosmos/M/PermutationNonCommutative）供给群级前提。把该源 x≉y 与任
-- 何具体反射提升结合，恰是下方 separation-survives。此处不用 subst、
-- cast、Maybe、K 或 UIP：全体性是携带假设，反射是携带函数，终性是 eta
-- 对。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.NontrivialLimit where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid using (EqOn)
open import ALMA.Cosmos.M.Object as MO
open import ALMA.Cosmos.M.Terminal
  using (≈CosmosM-sym; ≈CosmosM-trans)

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)}
         {ℓd : Level}
         (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
       where

  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

  ----------------------------------------------------------------------
  -- 1. Totality of a target fibre.
  -- 1. 目标纤维的全体性。
  ----------------------------------------------------------------------

  -- A fibre is trivial when every two nodes are bisimilar.
  --
  -- 纤维在任意两节点都互模拟时平凡。
  AllBisim : (j : MO.I C FC) → Set (L ⊔ ℓd)
  AllBisim j = ∀ (t u : MO.CosmosM C FC j)
             → MO.≈CosmosM C FC ≈CD t u

  -- A total fibre has no distinguished pair: a claimed ¬bisimulation
  -- between any two nodes is directly contradicted by totality.
  --
  -- 全纤维没有可区分对：任意两节点间所谓的 ¬互模拟 都被全体性直接反驳。
  no-distinguishing-pair : ∀ {j : MO.I C FC}
    → AllBisim j
    → ¬ Σ (MO.CosmosM C FC j) λ t →
        Σ (MO.CosmosM C FC j) λ u →
          ¬ MO.≈CosmosM C FC ≈CD t u
  no-distinguishing-pair all (t , u , t≉u) = t≉u (all t u)

  ----------------------------------------------------------------------
  -- 2. Reflection dichotomy for a limit lift.
  -- 2. 极限提升的反射二分。
  ----------------------------------------------------------------------

  -- A node-to-node lift (the carried form of liftAt); it may move a
  -- node within its fibre.  It REFLECTS bisimulation when bisimilar
  -- target images force bisimilar sources -- the carried lift0-inj.
  --
  -- 节点到节点的提升（liftAt 的携带式形态），可在纤维内移动节点。当目
  -- 标像互模拟即迫使源互模拟时，它反射互模拟——即携带式 lift0-inj。
  ReflectsBisim : ((j : MO.I C FC) → MO.CosmosM C FC j
                 → MO.CosmosM C FC j) → Set (L ⊔ ℓd)
  ReflectsBisim lift =
    ∀ {j : MO.I C FC} (t u : MO.CosmosM C FC j)
    → MO.≈CosmosM C FC ≈CD (lift j t) (lift j u)
    → MO.≈CosmosM C FC ≈CD t u

  -- Reflection preserves separation: if the source pair is not
  -- bisimilar, neither are their lifted images.  Pure contrapositive,
  -- no transport.
  --
  -- 反射保持分离：若源对不互模拟，则其提升像也不互模拟。纯逆否，无传输。
  separation-survives : ∀ lift → ReflectsBisim lift
    → ∀ {j : MO.I C FC} (t u : MO.CosmosM C FC j)
    → ¬ MO.≈CosmosM C FC ≈CD t u
    → ¬ MO.≈CosmosM C FC ≈CD (lift j t) (lift j u)
  separation-survives lift refl-bisim t u t≉u eq =
    t≉u (refl-bisim t u eq)

  -- A reflecting lift into a total target forces the source fibre to be
  -- total as well: totality relates the images, reflection pulls the
  -- relation back to the sources.
  --
  -- 向全目标的反射提升迫使源纤维也全体：全体性联系两像，反射把该关系拉
  -- 回源。
  total-target-collapses : ∀ lift → ReflectsBisim lift
    → (j : MO.I C FC) → AllBisim j
    → ∀ (t u : MO.CosmosM C FC j)
    → MO.≈CosmosM C FC ≈CD t u
  total-target-collapses lift refl-bisim j all t u =
    refl-bisim t u (all (lift j t) (lift j u))

  -- The negative theorem: a genuinely separated source pair cannot be
  -- lifted by a bisimulation-reflecting map into a trivial (total)
  -- target.  This is the M form of the legacy
  -- no-nontrivial-limit-of-singleton-target: a limit over a separated
  -- tower whose target is terminal/total cannot have liftAt both
  -- reflecting and defined.
  --
  -- 否定定理：真正分离的源对不能经互模拟反射映射提升到平凡（全）目标。
  -- 这是旧 no-nontrivial-limit-of-singleton-target 的 M 形态：对分离塔
  -- 而目标为终/全的极限，其 liftAt 不可能既反射又有定义。
  no-nontrivial-limit : ∀ lift → ReflectsBisim lift
    → (j : MO.I C FC) → AllBisim j
    → (t u : MO.CosmosM C FC j)
    → ¬ MO.≈CosmosM C FC ≈CD t u
    → ⊥
  no-nontrivial-limit lift refl-bisim j all t u t≉u =
    t≉u (total-target-collapses lift refl-bisim j all t u)

  ----------------------------------------------------------------------
  -- 3. Terminality supplies the trivial (collapsing) target.
  -- 3. 终性给出平凡（塌缩）目标。
  ----------------------------------------------------------------------

  -- A candidate mediating map from a state coalgebra γ into the terminal
  -- M-Cosmos, carrying its commutation: the unfolding of the mapped
  -- state rebuilds the unfolding of the source state.
  --
  -- 从状态余代数 γ 到终 M-Cosmos 的候选中介映射，携带其交换：被映射状
  -- 态的展开重建源状态的展开。
  record TerminalMediator {u : Level}
      (Xst : MO.I C FC → Set u)
      (γ   : MO.Coalgebra C FC u Xst)
      : Set (L ⊔ ℓd ⊔ u) where
    field
      med      : ∀ (j : MO.I C FC) (x : Xst j) → MO.CosmosM C FC j
      med-comm : ∀ (j : MO.I C FC) (x : Xst j)
        → MO.≈CosmosM C FC ≈CD
            (MO.ana C FC (MO.unfold-coalgebra C FC) j (med j x))
            (MO.ana C FC γ j x)
  open TerminalMediator public

  -- Every terminal mediator is bisimilar to the anamorphism: the eta
  -- direction ana-unfold˘ turns med j x into its own unfolding, and
  -- med-comm identifies that unfolding with ana γ.
  --
  -- 每个终中介都与 anamorphism 互模拟：eta 方向 ana-unfold˘ 把 med j x
  -- 变为其自身展开，med-comm 再把该展开认作 ana γ。
  terminal-unique : ∀ {u : Level}
      {Xst : MO.I C FC → Set u}
      {γ   : MO.Coalgebra C FC u Xst}
      (m   : TerminalMediator Xst γ)
      (j   : MO.I C FC) (x : Xst j)
    → MO.≈CosmosM C FC ≈CD (med m j x) (MO.ana C FC γ j x)
  terminal-unique {γ = γ} m j x =
    ≈CosmosM-trans ≈CD
      (MO.ana-unfold˘ C FC ≈CD (med m j x))
      (med-comm m j x)

  -- Any two terminal mediators of the same coalgebra have pointwise-
  -- bisimilar images: each coincides with ana γ, and bisimulation
  -- symmetry/transitivity close the triangle.  Hence a limit whose
  -- target is the terminal M-Cosmos collapses every cone to a single
  -- image and cannot separate any pair -- the constructive reason a
  -- trivial target admits no non-trivial limit.
  --
  -- 同一余代数的任意两个终中介其像逐点互模拟：二者都与 ana γ 重合，互
  -- 模拟对称/传递闭合三角。故目标为终 M-Cosmos 的极限把每个锥塌缩为单
  -- 一像，无法区分任何对——这是平凡目标无非平凡极限的构造性原因。
  terminal-mediators-coincide : ∀ {u : Level}
      {Xst : MO.I C FC → Set u}
      {γ   : MO.Coalgebra C FC u Xst}
      (m n : TerminalMediator Xst γ)
      (j   : MO.I C FC) (x : Xst j)
    → MO.≈CosmosM C FC ≈CD (med m j x) (med n j x)
  terminal-mediators-coincide {γ = γ} m n j x =
    ≈CosmosM-trans ≈CD
      (terminal-unique m j x)
      (≈CosmosM-sym ≈CD (terminal-unique n j x))
