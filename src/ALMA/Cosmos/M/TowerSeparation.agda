------------------------------------------------------------------------
-- Tower separation witness on the carried M base: two distinguished
-- M-Cosmoi over FinCat n (n ≥ 2) are not bisimilar.
--
-- Legacy result (Cosmos/FinCatNWitness): over the trivial-fibre tower on
-- FinCat n = Indiscrete (Fin n), the identity-like cosmos (uf F₀ = proj₁)
-- and the constant-first cosmos (uf F₀ = const fzero) differ at the
-- object fsuc fzero, hence are not bisimilar.  The threshold is n ≥ 2: at
-- n = 1 the object set Fin 1 is a singleton, the two uf maps coincide
-- (both send the unique object to itself), and no separation exists.
--
-- M-base reconstruction.  The base category is Indiscrete (Fin n) with a
-- singleton-shape / singleton-position container; the M-Cosmos index is
-- Σ (Fin n) (λ _ → ⊤), isomorphic to Fin n.  The two constant trees carry
-- head labels whose only difference is the object map uf.F₀:
--
--   dId : uf.F₀ (x , tt) = x          (identity-like)
--   dC0 : uf.F₀ (x , tt) = fzero      (constant on the first object)
--
-- A propositional bisimulation ≈CosmosM carries a head-label equality
-- here-eq : dId ≡ dC0.  Projecting uf.F₀ at the index (fsuc fzero , tt)
-- yields fsuc fzero ≡ fzero, which is absurd: the Fin constructors zero
-- and suc are disjoint.  As in MorphismCorrespondence.swap-not-commute
-- the mismatch is absorbed by the empty pattern — a constructive
-- no-confusion, not the K/UIP axiom — so there is no subst, cast, Maybe,
-- K or UIP.  The parameter m encodes n = suc (suc m), so n ≥ 2 holds
-- definitionally; this is exactly why the witness is stated only there.
--
-- 携带式 M 底座上的塔层分离见证：FinCat n（n ≥ 2）上两个被区分的
-- M-Cosmos 不互模拟。
--
-- 旧结果（Cosmos/FinCatNWitness）：在 FinCat n = Indiscrete (Fin n) 的
-- 平凡纤维塔上，类恒等宇宙（uf F₀ = proj₁）与常值首对象宇宙
-- （uf F₀ = const fzero）在对象 fsuc fzero 处不同，故不互模拟。阈值为
-- n ≥ 2：n = 1 时对象集 Fin 1 为单点，两个 uf 映射重合（都把唯一对象
-- 送到自身），不存在分离。
--
-- M 底座重建。基范畴为 Indiscrete (Fin n)，配单点形状/单点位置容器；
-- M-Cosmos 索引为 Σ (Fin n) (λ _ → ⊤)，与 Fin n 同构。两棵常树携带的
-- 头标签唯一差别是对象映射 uf.F₀：
--
--   dId : uf.F₀ (x , tt) = x          （类恒等）
--   dC0 : uf.F₀ (x , tt) = fzero      （常值于首对象）
--
-- 命题互模拟 ≈CosmosM 携带头标签等式 here-eq : dId ≡ dC0。在索引
-- (fsuc fzero , tt) 处投影 uf.F₀ 得 fsuc fzero ≡ fzero，矛盾：Fin 构造
-- 子 zero 与 suc 不相交。与 MorphismCorrespondence.swap-not-commute
-- 一样，失配由空模式吸收——构造性无混淆，而非 K/UIP 公理——故无
-- subst、cast、Maybe、K 或 UIP。参数 m 编码 n = suc (suc m)，使 n ≥ 2
-- 定义性成立；这正是见证仅在此陈述的原因。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.TowerSeparation where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

open import Data.Container.Core using (Container)
open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)
open Functor using (F₀)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

open import ALMA.Base.MCorrSetoid using (propEqOn; here-eq)
import ALMA.Cosmos.M.Object as MO

------------------------------------------------------------------------
-- The FinCat n tower stage, parameterised by m with n = suc (suc m), so
-- n ≥ 2 holds definitionally.
-- FinCat n 塔层，以 m 为参数，n = suc (suc m)，故 n ≥ 2 定义性成立。
------------------------------------------------------------------------
module TowerSeparation (m : ℕ) where

  -- n = suc (suc m), hence n ≥ 2.
  -- n = suc (suc m)，故 n ≥ 2。
  n : ℕ
  n = suc (suc m)

  -- FinCat n = Indiscrete (Fin n): every hom is the unique (lift tt),
  -- equality on homs is propositional equality.
  -- FinCat n = Indiscrete (Fin n)：每个 hom 为唯一的 (lift tt)，hom 相
  -- 等即命题相等。
  Cn : Category lzero lzero lzero
  Cn = Indiscrete (Fin n)

  -- Trivial-fibre container: singleton shapes and singleton positions.
  -- 平凡纤维容器：单点形状、单点位置。
  TrivContainer : Container lzero lzero
  TrivContainer = record { Shape = ⊤ ; Position = λ _ → ⊤ }

  TrivFC : Functor Cn (ContCat lzero lzero)
  TrivFC = record
    { F₀           = λ _ → TrivContainer
    ; F₁           = λ _ → record { shape = λ _ → tt ; position = λ _ → tt }
    ; identity     = ≈sr-refl
    ; homomorphism = ≈sr-refl
    ; F-resp-≈     = λ _ → ≈sr-refl
    }

  ----------------------------------------------------------------------
  -- The two object maps uf, as functors ShapeCat Cn TrivFC → Cn.
  -- ShapeCat is the category of elements of the singleton shape functor:
  -- its objects are Σ (Fin n) (λ _ → ⊤) and every hom is unique, so the
  -- arrow part F₁ is the underlying (unique) Cn arrow and all functor
  -- laws hold by refl.  The only difference between the two is F₀.
  --
  -- 两个对象映射 uf，作为 ShapeCat Cn TrivFC → Cn 的函子。ShapeCat 是
  -- 单点形状函子的元素范畴：对象为 Σ (Fin n) (λ _ → ⊤)，每个 hom 唯一，
  -- 故箭头部分 F₁ 即底层（唯一的）Cn 箭头，所有函子律由 refl 成立。两
  -- 者唯一差别在 F₀。
  ----------------------------------------------------------------------
  -- Identity-like: F₀ (x , tt) = x.
  -- 类恒等：F₀ (x , tt) = x。
  ufId : Functor (ShapeCat Cn TrivFC) Cn
  ufId = record
    { F₀           = proj₁
    ; F₁           = proj₁
    ; identity     = ≡refl
    ; homomorphism = ≡refl
    ; F-resp-≈     = λ p → p
    }

  -- Constant on the first object: F₀ _ = fzero.
  -- 常值于首对象：F₀ _ = fzero。
  ufC0 : Functor (ShapeCat Cn TrivFC) Cn
  ufC0 = record
    { F₀           = λ _ → fzero
    ; F₁           = proj₁
    ; identity     = ≡refl
    ; homomorphism = ≡refl
    ; F-resp-≈     = λ p → p
    }

  ----------------------------------------------------------------------
  -- The two distinguished head labels.  Positions and shapes are
  -- singletons, so pts is the unique map; the labels differ only in uf.
  -- 两个被区分的头标签。位置与形状均为单点，故 pts 为唯一映射；标签仅
  -- 在 uf 上不同。
  ----------------------------------------------------------------------
  dId : MO.CosmosData Cn TrivFC
  dId = record { uf = ufId ; pts = λ _ _ → tt }

  dC0 : MO.CosmosData Cn TrivFC
  dC0 = record { uf = ufC0 ; pts = λ _ _ → tt }

  ----------------------------------------------------------------------
  -- Constant coalgebras over a singleton state family, and the constant
  -- trees they unfold to at every index.
  -- 单点状态族上的常余代数，及其在每个索引处展开的常树。
  ----------------------------------------------------------------------
  γId : MO.Coalgebra Cn TrivFC lzero (λ _ → ⊤)
  MO.Coalgebra.label γId _ tt = dId
  MO.Coalgebra.child γId _ tt _ = tt

  γC0 : MO.Coalgebra Cn TrivFC lzero (λ _ → ⊤)
  MO.Coalgebra.label γC0 _ tt = dC0
  MO.Coalgebra.child γC0 _ tt _ = tt

  treeId : (i : MO.I Cn TrivFC) → MO.CosmosM Cn TrivFC i
  treeId i = MO.ana Cn TrivFC γId i tt

  treeC0 : (i : MO.I Cn TrivFC) → MO.CosmosM Cn TrivFC i
  treeC0 i = MO.ana Cn TrivFC γC0 i tt

  ----------------------------------------------------------------------
  -- The distinguishing index: the second object fsuc fzero paired with
  -- the unique shape.  It exists only because n ≥ 2.
  -- 区分性索引：第二个对象 fsuc fzero 配上唯一形状。它仅因 n ≥ 2 而存在。
  ----------------------------------------------------------------------
  i₁ : MO.I Cn TrivFC
  i₁ = fsuc fzero , tt

  ----------------------------------------------------------------------
  -- Non-bisimilarity.  A bisimulation carries here-eq : dId ≡ dC0;
  -- projecting uf.F₀ at i₁ gives
  --
  --   F₀ ufId i₁ = fsuc fzero   versus   F₀ ufC0 i₁ = fzero,
  --
  -- i.e. fsuc fzero ≡ fzero, which is absurd (disjoint Fin constructors).
  -- The empty pattern is constructive no-confusion; no K/UIP, no subst.
  --
  -- 非互模拟。互模拟携带 here-eq : dId ≡ dC0；在 i₁ 处投影 uf.F₀ 得
  --
  --   F₀ ufId i₁ = fsuc fzero   对   F₀ ufC0 i₁ = fzero，
  --
  -- 即 fsuc fzero ≡ fzero，矛盾（Fin 构造子不相交）。空模式是构造性无
  -- 混淆；无 K/UIP、无 subst。
  ----------------------------------------------------------------------
  idN≉const0N
    : ¬ MO.≈CosmosM Cn TrivFC (λ _ → propEqOn _)
          (treeId i₁) (treeC0 i₁)
  idN≉const0N b
    with cong (λ d → F₀ (MO.CosmosData.uf d) i₁) (here-eq b)
  ... | ()
