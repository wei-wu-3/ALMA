------------------------------------------------------------------------
-- Non-trivial fixed-label deterministic endomorphism on the M-Cosmos:
-- the uniform binary universe and the swap01 (n = 2) edge permutation
--
-- This is the M-base reconstruction of the old ListCosmos swap witness,
-- restricted to the regime the fixed-label congruence engine
-- (Cosmos.M.DetCongruence) actually covers.
--
-- The old swap-⇒ℱ lived on Shape = ℕ / Position = Fin n and used
-- onPos = swap01 together with a CHANGED position-to-shape map
-- (shapeTrans i = toℕ (swap01 n i)).  Changing pos-to-shape changes the
-- label CosmosData.pts, so that morphism is LABEL-CHANGING and is NOT in
-- the scope of the fixed-label engine (whose deterministic shape action
-- is the identity and whose coverage pullback is label-independent); it
-- belongs to the later general (non-fixed-label) correspondence slice
-- (M/MorphismCorrespondence).
--
-- The fixed-label ESSENCE of swap01 is the non-identity edge bijection
-- at n = 2 (swapFin2 = opposite, exchanging positions 0 and 1).  It is a
-- legitimate fixed-label deterministic endomorphism exactly on a
-- UNIFORMLY BRANCHING universe: take the single-shape container
-- (Shape = ⊤, Position = const (Fin 2)).  Here:
--
--   * the index I = Σ ⊤ ⊤ is a singleton, so the index endofunctor S is
--     the identity and its coverage pullback is (v , ≡refl);
--   * every label has pts : ⊤ → Fin 2 → ⊤, which is unique (the only
--     value of a ⊤-valued function), hence there is in effect ONE label
--     and every edge target is the unique index;
--   * the edge fibre E i d i is therefore Fin 2 (each position paired
--     with the constructive ≡refl), and opposite is a TOTAL, involutive
--     edge self-bijection for every label d — the required FiberAdjˢ.
--
-- opposite moves position 0 to position 1, so the carried deterministic
-- FMˢ is provably NON-IDENTITY on edges.  Everything is carried data
-- (the bijection and its round-trips); no K, UIP, subst or cast is used.
--
-- M-Cosmos 上的非平凡固定标签确定性自态射：
-- 一致二元宇宙与 swap01（n = 2）边置换
--
-- 这是旧 ListCosmos swap 见证在 M 底座上的重建，限定于固定标签同余引擎
-- （Cosmos.M.DetCongruence）真正覆盖的制度。
--
-- 旧 swap-⇒ℱ 生活在 Shape = ℕ / Position = Fin n 上，onPos = swap01 并
-- 附带被改变的位置到形状映射（shapeTrans i = toℕ (swap01 n i)）。改变
-- pos-to-shape 即改变标签 CosmosData.pts，故该态射是改标签的，不在固
-- 定标签引擎（其确定性形状作用为恒等、覆盖拉回与标签无关）的范围内，
-- 属于后续一般（非固定标签）对应切片（M/MorphismCorrespondence）。
--
-- swap01 在固定标签下的本质是 n = 2 处的非恒等边双射
-- （swapFin2 = opposite，交换位置 0 与 1）。它恰在一致分支宇宙上成为合
-- 法的固定标签确定性自态射：取单一形状容器（Shape = ⊤，
-- Position = const (Fin 2)）。此时：
--
--   * 索引 I = Σ ⊤ ⊤ 为单例，故索引自函子 S 为恒等，其覆盖拉回为
--     (v , ≡refl)；
--   * 每个标签的 pts : ⊤ → Fin 2 → ⊤ 唯一（⊤ 值函数的唯一值），故事实
--     上只有一个标签，每条边的目标都是唯一索引；
--   * 边纤维 E i d i 因而是 Fin 2（每个位置配上构造性 ≡refl），opposite
--     对每个标签 d 都是满定义、对合的边自双射——即所需 FiberAdjˢ。
--
-- opposite 把位置 0 移到位置 1，故所携带的确定性 FMˢ 在边上可证非恒
-- 等。一切皆为携带数据（双射及其往返）；不用 K、UIP、subst 或 cast。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ListCosmos where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Fin.Base using (Fin; opposite)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (opposite-involutive)
open import Data.Container.Core using (Container)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using (One)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

open import ALMA.Base.MCorrSetoid using (FiberAdjˢ; propEqOn)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.DetCongruence as DC

------------------------------------------------------------------------
-- The terminal base category and the uniform binary container.
--
-- 终基范畴与一致二元容器。
------------------------------------------------------------------------
C₀ : Category lzero lzero lzero
C₀ = One

-- Single shape ⊤, exactly two positions at every node.
-- 单一形状 ⊤，每个节点恰有两个位置。
BinContainer : Container lzero lzero
BinContainer = record { Shape = ⊤ ; Position = λ _ → Fin 2 }

-- The identity position map on Fin 2.
-- Fin 2 上的恒等位置映射。
idFin2 : Fin 2 → Fin 2
idFin2 p = p

-- The constant functor from the terminal category to ContCat.
-- 从终范畴到 ContCat 的常值函子。
BinFC : Functor C₀ (ContCat lzero lzero)
BinFC = record
  { F₀           = λ _ → BinContainer
  ; F₁           = λ _ → record { shape = λ _ → tt ; position = idFin2 }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

-- Bring the fixed-label congruence engine names (parameterised by the
-- base category and container functor, supplied at each use).
-- 引入固定标签同余引擎的名字（以基范畴与容器函子为参数，使用处供给）。
open DC using (UniDet; uniFMapˢ; uniFMˢ)

------------------------------------------------------------------------
-- Index, label and edge fibre for the binary universe.
--
-- 二元宇宙的索引、标签与边纤维。
------------------------------------------------------------------------
BinI : Set lzero
BinI = MO.I C₀ BinFC

BinData : Set lzero
BinData = MO.CosmosData C₀ BinFC

BinE : (i : BinI) (d : BinData) (j : BinI) → Set lzero
BinE = MO.E C₀ BinFC

-- The unique index (Obj One = ⊤ and Shape = ⊤).
-- 唯一索引（Obj One = ⊤ 且 Shape = ⊤）。
i0 : BinI
i0 = tt , tt

-- At the unique index the edge fibre is Fin 2: the target equation is
-- necessarily i0 ≡ i0 (pts is ⊤-valued, hence unique).  Edges are
-- introduced as (p , ≡refl) and never eliminated.
--
-- 在唯一索引处边纤维即 Fin 2：目标等式必为 i0 ≡ i0（pts 取 ⊤ 值，故唯
-- 一）。边以 (p , ≡refl) 引入，绝不消去。
Edge : (d : BinData) → Set lzero
Edge d = BinE i0 d i0

------------------------------------------------------------------------
-- The unique label.  uf is the unique functor ShapeCat → One (mirroring
-- UnitCosmos); pts is the unique ⊤-valued map.
--
-- 唯一标签。uf 是唯一的 ShapeCat → One 函子（与 UnitCosmos 同构）；pts
-- 是唯一的 ⊤ 值映射。
------------------------------------------------------------------------
uf0 : Functor (ShapeCat C₀ BinFC) C₀
uf0 = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl C₀
  ; homomorphism = Category.Equiv.refl C₀
  ; F-resp-≈     = λ p → p
  }

d0 : BinData
d0 = record { uf = uf0 ; pts = λ { _ _ → tt } }

------------------------------------------------------------------------
-- opposite on Fin 2 is an involution: it exchanges 0 and 1.
--
-- Fin 2 上的 opposite 是对合：交换 0 与 1。
------------------------------------------------------------------------
-- The edge permutation acts only on the position and KEEPS the
-- constructive target equation as an (un-matched) variable: at the
-- unique index the target is i0 regardless of the position, so the same
-- equation types the moved edge.  Matching the equation with ≡refl would
-- require pair injectivity (unsupported under --cubical-compatible), so
-- the equation is carried, never inspected.
--
-- 边置换只作用于位置，并把构造性目标等式作为（不匹配的）变量保留：在唯
-- 一索引处目标恒为 i0，与位置无关，故同一等式即可为移动后的边定型。
-- 用 ≡refl 匹配该等式会依赖配对单射（--cubical-compatible 不支持），故
-- 等式被携带、绝不检视。
swapE : ∀ (d : BinData) → Edge d → Edge d
swapE d (p , eq) = opposite p , eq

------------------------------------------------------------------------
-- The uniform deterministic data for the identity index functor:
--   pb v = (v , ≡refl)  (the singleton index covers itself);
--   adj is the opposite edge self-bijection with both round-trips from
--   the involution.  The adjunction is label-independent (it ignores d),
--   satisfying the fixed-label uniformity premise.
--
-- 恒等索引函子的一致确定性数据：
--   pb v = (v , ≡refl)（单例索引覆盖自身）；
--   adj 为 opposite 边自双射，两条往返由对合给出。伴随与标签无关（忽略
--   d），满足固定标签一致性前提。
------------------------------------------------------------------------
private
  swapAdj : (d : BinData)
          → FiberAdjˢ (propEqOn (Edge d)) (propEqOn (Edge d))
  swapAdj d = record
    { to        = swapE d
    ; fro       = swapE d
    ; to-cong   = λ eq → cong (swapE d) eq
    ; fro-cong  = λ eq → cong (swapE d) eq
    ; η         = λ { (p , eq) →
                    cong (λ q → (q , eq)) (opposite-involutive p) }
    ; ε         = λ { (p , eq) →
                    cong (λ q → (q , eq)) (opposite-involutive p) }
    }

swapUni : UniDet C₀ BinFC (idF {C = ShapeCat C₀ BinFC})
UniDet.pb  swapUni v = v , ≡refl
UniDet.adj swapUni (tt , tt) d (tt , tt) = swapAdj d

------------------------------------------------------------------------
-- The categorical deterministic endomorphism bundle: its map-cong is
-- SUPPLIED by the fixed-label gow-setoid engine (uniFMˢ), never derived
-- by eliminating equality.
--
-- 范畴确定性自态射束：其 map-cong 由固定标签 gow-setoid 引擎
-- （uniFMˢ）供给，绝不靠消去等式得到。
------------------------------------------------------------------------
swapFMˢ : FMˢ (MO.sys C₀ BinFC (λ _ → propEqOn _))
              (MO.sys C₀ BinFC (λ _ → propEqOn _))
swapFMˢ = uniFMˢ C₀ BinFC (idF {C = ShapeCat C₀ BinFC}) swapUni

------------------------------------------------------------------------
-- Non-identity witness: the carried edge action sends position 0 to
-- position 1.  This is the fixed-label analogue of swap01-fzero≠fzero.
--
-- 非恒等见证：所携带的边作用把位置 0 送到位置 1。这是
-- swap01-fzero≠fzero 的固定标签对应物。
------------------------------------------------------------------------
e0 : Edge d0
e0 = fzero , ≡refl

e1 : Edge d0
e1 = fsuc fzero , ≡refl

-- The carried forward edge action is definitionally opposite.
-- 所携带的正向边作用定义地即 opposite。
swap-sends-0→1 :
  FiberAdjˢ.to (FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) i0 d0 i0) e0 ≡ e1
swap-sends-0→1 = ≡refl

-- Hence it cannot fix position 0.
-- 故它不可能固定位置 0。
swap-nonidentity :
  ¬ FiberAdjˢ.to (FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) i0 d0 i0) e0 ≡ e0
swap-nonidentity ()
