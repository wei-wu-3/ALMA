------------------------------------------------------------------------
-- Standard colimit of an arbitrary forward ω-chain in SameIndexCatS.
--
-- A chain is a family of stage objects X m together with identity-index
-- forward arrows e m : X m ⇒ X (suc m).  Every arrow keeps the global id
-- and the deterministic dynamics d, so labels move between stages purely
-- by function passing.
--
-- The direct-limit fibre is a forward compatible family Fam: a choice at
-- every stage whose successive choices are related by the forward map in
-- the stage setoid.  Its equality is the pointwise stage setoid, so the
-- construction needs no Fin alignment, no transport, no K and no
-- function extensionality, and the stage fibres may carry arbitrary
-- setoids (not only propositional ones).  A family is determined by a
-- stage-0 seed along the deterministic forward orbit; embedding a later
-- stage element needs a root, the forward analogue of a total ray.
--
-- SameIndexCatS 中任意前向 ω-链的标准余极限。
--
-- 链由一族阶段对象 X m 与索引恒等的前向箭头 e m : X m ⇒ X (suc m)
-- 组成。每条箭头保持全局 id 与确定性动力 d，标签跨阶段纯由函数传递。
--
-- 直接极限纤维是前向相容族 Fam：在每个阶段取一个元素，相邻选择由前向
-- 映射在阶段 setoid 中相关。其相等为逐点阶段 setoid，故构造无需 Fin
-- 对齐、无传输、不用 K、不用函数外延性，且阶段纤维可带任意 setoid（不
-- 限于命题纤维）。一个族由阶段 0 的种子沿确定性前向轨道决定；嵌入更晚
-- 阶段的元素需要一个根，即全总射线的前向对偶。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.ChainColimitS where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc)

open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; propEqOn)
open import ALMA.Cosmos.Carried.SameIndexCatS
  using (LabelSys; dsys; Idx⇒; idxi; compi; _≈i_
        ; SameIndexCat; ≈i-refl; ≈i-sym; ≈i-trans; ∘-resp-≈i)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)
open import ALMA.Cosmos.Carried.SeqColimitCat
  using (Chain⇒; stop; step; ωCat)
import ALMA.Cosmos.Carried.SeqColimitCat as SQC

module _ (d : ℕ → ℕ) {ℓ : Level} where

  ----------------------------------------------------------------------
  -- A forward ω-chain: stage objects and identity-index forward arrows.
  -- 前向 ω-链：阶段对象与索引恒等的前向箭头。
  record ChainS : Set (lsuc ℓ) where
    field
      X₀ : ℕ → LabelSys ℓ
      e  : (m : ℕ) → Idx⇒ d (X₀ m) (X₀ (suc m))

  module Build (C : ChainS) where

    open ChainS C

    private
      s   = d
      sYS = dsys s

    -- Stage fibres and their setoids.
    -- 阶段纤维及其 setoid。
    fibre : (m v : ℕ) → Set ℓ
    fibre m v = LabelSys.A₀ (X₀ m) v

    ≈fibre : (m v : ℕ) → EqOn (fibre m v)
    ≈fibre m v = LabelSys.≈A₀ (X₀ m) v

    -- One-step forward label map and its setoid compatibility.
    -- 一步前向标签映射及其 setoid 同余。
    fwd : (m v : ℕ) → fibre m v → fibre (suc m) v
    fwd m v = Idx⇒.shape (e m) v

    fwd-cong : (m v : ℕ) {a a' : fibre m v}
             → EqOn._≈_ (≈fibre m v) a a'
             → EqOn._≈_ (≈fibre (suc m) v) (fwd m v a) (fwd m v a')
    fwd-cong m v = Idx⇒.shape-cong (e m) {v = v}

    -- Stage reached after n forward steps from m; the zero case is m
    -- definitionally, so iteration types need no arithmetic transport.
    -- 从 m 经 n 步前向到达的阶段；零步定义性为 m，故迭代类型无需算术传输。
    iter-stage : (n m : ℕ) → ℕ
    iter-stage zero    m = m
    iter-stage (suc n) m = iter-stage n (suc m)

    -- n-step forward iteration, from stage m to iter-stage n m.
    -- n 步前向迭代，从阶段 m 到 iter-stage n m。
    fwd^ : (n m v : ℕ) → fibre m v → fibre (iter-stage n m) v
    fwd^ zero    m v a = a
    fwd^ (suc n) m v a = fwd^ n (suc m) v (fwd m v a)

    -- Iteration respects the stage setoid at every step.
    -- 迭代在每一步保持阶段 setoid。
    fwd^-cong : (n m v : ℕ) {a a' : fibre m v}
              → EqOn._≈_ (≈fibre m v) a a'
              → EqOn._≈_ (≈fibre (iter-stage n m) v)
                          (fwd^ n m v a) (fwd^ n m v a')
    fwd^-cong zero    m v eq = eq
    fwd^-cong (suc n) m v eq =
      fwd^-cong n (suc m) v (fwd-cong m v eq)

    --------------------------------------------------------------------
    -- Direct-limit element as a forward compatible family: a choice at
    -- every stage with successive choices related by fwd.
    -- 直接极限元素作为前向相容族：每阶段一个选择，相邻选择由 fwd 相关。
    record Fam (v : ℕ) : Set ℓ where
      coinductive
      field
        at  : (m : ℕ) → fibre m v
        coh : (m : ℕ)
            → EqOn._≈_ (≈fibre (suc m) v) (fwd m v (at m)) (at (suc m))
    open Fam public

    -- Pointwise stage setoid on families; equality is data at every
    -- stage, so no function extensionality is required.
    -- 族上的逐点阶段 setoid；相等是每阶段的数据，无需函数外延性。
    _≈Fam_ : {v : ℕ} → Fam v → Fam v → Set ℓ
    _≈Fam_ {v} τ υ =
      (m : ℕ) → EqOn._≈_ (≈fibre m v) (at τ m) (at υ m)

    -- Pointwise lifting of the stage setoid; the element is named
    -- explicitly so the coinductive projection at τ m does not block
    -- inference.
    -- 阶段 setoid 的逐点提升；元素显式命名，以免共归纳投影 at τ m 阻塞推断。
    private
      refl-at : (v m : ℕ) (τ : Fam v)
              → EqOn._≈_ (≈fibre m v) (at τ m) (at τ m)
      refl-at v m τ = EqOn.refl (≈fibre m v)

      sym-at : (v m : ℕ) (τ υ : Fam v)
             → EqOn._≈_ (≈fibre m v) (at τ m) (at υ m)
             → EqOn._≈_ (≈fibre m v) (at υ m) (at τ m)
      sym-at v m τ υ h = EqOn.sym (≈fibre m v) h

      trans-at : (v m : ℕ) (τ υ ω : Fam v)
               → EqOn._≈_ (≈fibre m v) (at τ m) (at υ m)
               → EqOn._≈_ (≈fibre m v) (at υ m) (at ω m)
               → EqOn._≈_ (≈fibre m v) (at τ m) (at ω m)
      trans-at v m τ υ ω h₁ h₂ = EqOn.trans (≈fibre m v) h₁ h₂

    ≈Fam : (v : ℕ) → EqOn (Fam v)
    ≈Fam v = record
      { _≈_           = _≈Fam_
      ; isEquivalence = record
        { refl  = λ {x} m → refl-at v m x
        ; sym   = λ {x y} h m → sym-at v m x y (h m)
        ; trans = λ {x y z} h₁ h₂ m →
                    trans-at v m x y z (h₁ m) (h₂ m)
        }
      }

    -- Forward orbit of a stage-0 seed, indexed by the target stage; the
    -- recursion is on the target stage, so no stage arithmetic appears in
    -- the types.
    -- 阶段 0 种子的前向轨道，按目标阶段索引；递归作用于目标阶段，类型中
    -- 因而不出现阶段算术。
    orbit0 : (m v : ℕ) → fibre 0 v → fibre m v
    orbit0 zero    v a = a
    orbit0 (suc m) v a = fwd m v (orbit0 m v a)

    -- The forward orbit of a stage-0 seed is a compatible family; the
    -- coherence holds definitionally.
    -- 阶段 0 种子的前向轨道是相容族；相干定义性成立。
    fam-of : (v : ℕ) → fibre 0 v → Fam v
    fam-of v a .at m    = orbit0 m v a
    fam-of v a .coh m   = EqOn.refl (≈fibre (suc m) v)
