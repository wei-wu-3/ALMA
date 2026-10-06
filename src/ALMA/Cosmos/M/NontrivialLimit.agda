------------------------------------------------------------------------
-- Conditional non-triviality of a limit, on the carried M base.
-- A target fibre is trivial when its bisimulation is total; a
-- bisimulation-reflecting lift into a total target forces the source
-- to be total as well, so a genuinely separated source cannot have a
-- reflecting lift into a trivial target. Terminality supplies the
-- trivial target: any two mediating maps into the terminal M-Cosmos
-- have pointwise-bisimilar images. The separated source itself is not
-- rebuilt here: it is the M-tower witness idN ≉ const0N over FinCat n
-- (TowerSeparation), with the group-level precondition from
-- PermutationNonCommutative.
--
-- 在携带式 M 底座上的极限条件性非平凡性。目标纤维在其互模拟为全关
-- 系时平凡；向全目标的反射提升迫使源也全体，故真正分离的源不可能有
-- 向平凡目标的反射提升。终性给出平凡目标：任何两个到终 M-Cosmos 的
-- 中介映射其像逐点互模拟。被分离的“源”不在此重建：它是 FinCat n 上
-- 的 M 塔见证 idN ≉ const0N（TowerSeparation），群级前提由
-- PermutationNonCommutative 供给。
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
open import ALMA.Cosmos.M.Terminal using (≈CosmosM-sym; ≈CosmosM-trans)

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)}
         {ℓd : Level}
         (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
       where

  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

  ----------------------------------------------------------------------
  -- 1. Totality of a target fibre
  -- 1. 目标纤维的全体性

  AllBisim : (j : MO.I C FC) → Set (L ⊔ ℓd)
  AllBisim j = ∀ (t u : MO.CosmosM C FC j)
             → MO.≈CosmosM C FC ≈CD t u

  -- A total fibre has no distinguished pair.
  -- 全纤维没有可区分对。
  no-distinguishing-pair : ∀ {j : MO.I C FC}
    → AllBisim j
    → ¬ Σ (MO.CosmosM C FC j) λ t →
        Σ (MO.CosmosM C FC j) λ u →
          ¬ MO.≈CosmosM C FC ≈CD t u
  no-distinguishing-pair all (t , u , t≉u) = t≉u (all t u)

  ----------------------------------------------------------------------
  -- 2. Reflection dichotomy for a limit lift
  -- A lift REFLECTS bisimulation when bisimilar target images force
  -- bisimilar sources -- the carried form of lift0-inj.
  -- 2. 极限提升的反射二分
  -- 提升在“目标像互模拟即迫使源互模拟”时反射互模拟——即携带式
  -- lift0-inj。

  ReflectsBisim : ((j : MO.I C FC) → MO.CosmosM C FC j
                 → MO.CosmosM C FC j) → Set (L ⊔ ℓd)
  ReflectsBisim lift =
    ∀ {j : MO.I C FC} (t u : MO.CosmosM C FC j)
    → MO.≈CosmosM C FC ≈CD (lift j t) (lift j u)
    → MO.≈CosmosM C FC ≈CD t u

  -- Reflection preserves separation; pure contrapositive, no transport.
  -- 反射保持分离；纯逆否，无传输。
  separation-survives : ∀ lift → ReflectsBisim lift
    → ∀ {j : MO.I C FC} (t u : MO.CosmosM C FC j)
    → ¬ MO.≈CosmosM C FC ≈CD t u
    → ¬ MO.≈CosmosM C FC ≈CD (lift j t) (lift j u)
  separation-survives lift refl-bisim t u t≉u eq =
    t≉u (refl-bisim t u eq)

  -- Totality relates the images; reflection pulls the relation back to
  -- the sources.
  -- 全体性联系两像；反射把关系拉回源。
  total-target-collapses : ∀ lift → ReflectsBisim lift
    → (j : MO.I C FC) → AllBisim j
    → ∀ (t u : MO.CosmosM C FC j)
    → MO.≈CosmosM C FC ≈CD t u
  total-target-collapses lift refl-bisim j all t u =
    refl-bisim t u (all (lift j t) (lift j u))

  -- A separated source pair cannot be lifted by a reflecting map into a
  -- total target.
  -- 分离的源对不能经反射映射提升到全目标。
  no-nontrivial-limit : ∀ lift → ReflectsBisim lift
    → (j : MO.I C FC) → AllBisim j
    → (t u : MO.CosmosM C FC j)
    → ¬ MO.≈CosmosM C FC ≈CD t u
    → ⊥
  no-nontrivial-limit lift refl-bisim j all t u t≉u =
    t≉u (total-target-collapses lift refl-bisim j all t u)

  ----------------------------------------------------------------------
  -- 3. Terminality supplies the trivial (collapsing) target
  -- A candidate mediating map from γ into the terminal M-Cosmos,
  -- carrying its commutation.
  -- 3. 终性给出平凡（塌缩）目标
  -- 从 γ 到终 M-Cosmos 的候选中介映射，携带其交换。

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

  -- Every terminal mediator is bisimilar to the anamorphism.
  -- 每个终中介都与 anamorphism 互模拟。
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
  -- bisimilar images, so a limit into the terminal M-Cosmos collapses
  -- every cone to a single image.
  -- 同一余代数的任意两个终中介其像逐点互模拟，故到终 M-Cosmos 的极限
  -- 把每个锥塌缩为单一像。
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
