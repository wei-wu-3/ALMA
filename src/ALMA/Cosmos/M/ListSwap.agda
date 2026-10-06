------------------------------------------------------------------------
-- Label-changing deterministic endomorphism on the M-Cosmos: the list
-- universe (Shape = ℕ, Position = Fin n) and the swap01 permutation
--
-- This is the M-base reconstruction of the old list swap-⇒ℱ, now using
-- the LABEL-CHANGING engine Cosmos.M.GenCongruence.
--
-- Shapes are natural numbers; a node of shape n has Fin n positions.
-- A label d routes position i to the child shape pts d n i.  The
-- deterministic endomorphism
--
--   * keeps the node index (S = id);
--   * CHANGES the label by conjugating the routing with swap01:
--       pts (σ d) n q = pts d n (swap01 n q),
--     so σ is total and uniform in d, and σ dList is the label that
--     routes i to toℕ (swap01 n i) (this is why DetCongruence, whose
--     shape action is the identity, cannot host it; GenCongruence can);
--   * covers each target child index by itself (pb v = (v , refl));
--   * carries the swap01 edge self-bijection, uniformly for every d.
--
-- swap01 is involutive only PROPOSITIONALLY on general Fin n (it uses
-- splitAt/join and opposite).  The edge fibre at a fixed child shape m
-- is the set of positions routing to m together with the constructive
-- index equation.  The edge bijection keeps that equation as a carried
-- variable; the only transport is a single J step (castTo) matching the
-- involution redex swap01 (swap01 p) ≡ p with the neutral term on the
-- left and the rigid p on the right.  That is the same legal,
-- computationally-refl J used by the kernel edge-reloc / ana: it
-- generalises a neutral index rather than assuming K, and carries no
-- transport debt.  The round-trips η/ε close with that J, so there is no
-- subst, cast, K, UIP axiom or Maybe.
--
-- M-Cosmos 上的改标签确定性自态射：列表宇宙（Shape = ℕ，
-- Position = Fin n）与 swap01 置换
--
-- 这是旧列表 swap-⇒ℱ 在 M 底座上的重建，现使用改标签引擎
-- Cosmos.M.GenCongruence。
--
-- 形状为自然数；形状 n 的节点有 Fin n 个位置。标签 d 把位置 i 路由到
-- 子形状 pts d n i。该确定性自态射：
--
--   * 保持节点索引（S = id）；
--   * 通过用 swap01 共轭路由来改变标签：
--       pts (σ d) n q = pts d n (swap01 n q)，
--     故 σ 对 d 是满的且一致，σ dList 即把 i 路由到
--     toℕ (swap01 n i) 的标签（这正是形状作用为恒等的 DetCongruence
--     无法容纳、而 GenCongruence 可以容纳的原因）；
--   * 每个目标子索引由自身覆盖（pb v = (v , refl)）；
--   * 对每个 d 一致地携带 swap01 边自双射。
--
-- swap01 在一般 Fin n 上仅命题地对合（用到 splitAt/join 与 opposite）。
-- 固定子形状 m 处的边纤维是路由到 m 的位置集合连同构造性索引等式。边
-- 双射把该等式作为携带变量保留；唯一传输是单个 J 步骤（castTo），它以
-- 左侧中性项、右侧刚性 p 匹配对合可约式 swap01 (swap01 p) ≡ p。这与内
-- 核 edge-reloc / ana 使用的合法、计算为 refl 的 J 相同：一般化中性索
-- 引而非假定 K，不携带传输债务。往返 η/ε 由该 J 闭合，故无 subst、
-- cast、K、UIP 公理或 Maybe。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ListSwap where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; toℕ; splitAt; join; opposite)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties
  using (opposite-involutive; join-splitAt; splitAt-join)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (proj₁)
open import Data.Product.Properties using (≡-dec)
open import Data.Nat using (_≟_)
open import Data.Unit.Polymorphic.Properties renaming (_≟_ to _⊤≟_)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Relation.Binary.Definitions using (Irrelevant)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Nullary.Negation using (¬_)
open import Categories.Functor.Core using (Functor)
open Functor using (F₀)

open import Data.Container.Core using (Container)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using (One)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

open import ALMA.Base.MCorrSetoid using (FiberAdjˢ; propEqOn)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.GenCongruence as GC

open ≡-Reasoning

------------------------------------------------------------------------
-- Terminal base category and the list container.
-- 终基范畴与列表容器。
------------------------------------------------------------------------
C₀ : Category lzero lzero lzero
C₀ = One

ListContainer : Container lzero lzero
ListContainer = record { Shape = ℕ ; Position = Fin }

-- The identity position map at an (implicit) shape n.
-- （隐式）形状 n 处的恒等位置映射。
idFin : ∀ {n : ℕ} → Fin n → Fin n
idFin p = p

ListFC : Functor C₀ (ContCat lzero lzero)
ListFC = record
  { F₀           = λ _ → ListContainer
  ; F₁           = λ _ → record { shape = λ n → n ; position = idFin }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

open GC using (GenDet; genFMapˢ; genFMˢ)

------------------------------------------------------------------------
-- Indices, labels and edge fibres.
-- 索引、标签与边纤维。
------------------------------------------------------------------------
L-I : Set lzero
L-I = MO.I C₀ ListFC

LData : Set lzero
LData = MO.CosmosData C₀ ListFC

LE : (i : L-I) (d : LData) (j : L-I) → Set lzero
LE = MO.E C₀ ListFC

-- The unique functor ShapeCat → One.
-- 唯一的 ShapeCat → One 函子。
uf0 : Functor (ShapeCat C₀ ListFC) C₀
uf0 = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl C₀
  ; homomorphism = Category.Equiv.refl C₀
  ; F-resp-≈     = λ p → p
  }

------------------------------------------------------------------------
-- swap01: swap the first two positions of Fin n, leave the rest.
-- swap01：交换 Fin n 的前两个位置，其余不变。
------------------------------------------------------------------------
private
  swapFin2 : Fin 2 → Fin 2
  swapFin2 = opposite

  swapSum : ∀ {n} → Fin 2 ⊎ Fin n → Fin 2 ⊎ Fin n
  swapSum (inj₁ i) = inj₁ (swapFin2 i)
  swapSum (inj₂ k) = inj₂ k

  swapSum-invol : ∀ {n} (z : Fin 2 ⊎ Fin n) → swapSum (swapSum z) ≡ z
  swapSum-invol (inj₁ i) = cong inj₁ (opposite-involutive i)
  swapSum-invol (inj₂ k) = ≡refl

-- The shape n is a plain natural number (not an indexed type), so
-- splitting it into 0 / 1 / 2 / ≥3 is ordinary Nat matching and raises
-- no indexed-match warning.  At n = 2 the permutation is opposite, which
-- computes definitionally; at n ≥ 3 it is the splitAt/join surgery.
--
-- 形状 n 是普通自然数（非索引类型），故将其分为 0 / 1 / 2 / ≥3 是普
-- 通 Nat 匹配，不产生索引匹配警告。n = 2 时置换为 opposite，可定义性
-- 计算；n ≥ 3 时为 splitAt/join 手术。
swap01 : (n : ℕ) → Fin n → Fin n
swap01 zero              ()
swap01 (suc zero)        i = i
swap01 (suc (suc zero))  i = opposite i
swap01 (suc (suc (suc n))) i = join 2 (suc n) (swapSum (splitAt 2 i))

-- Propositional involution of swap01.  At n = 2 this is opposite's
-- involutive law (definitionally refl on Fin 2); at n ≥ 3 it follows
-- from the splitAt/join round-trips.  No Fin-constructor indexed match
-- occurs here.
--
-- swap01 的命题对合。n = 2 时即 opposite 的对合律（Fin 2 上定义性
-- refl）；n ≥ 3 时由 splitAt/join 往返得到。此处无 Fin 构造子索引
-- 匹配。
swap01-invol : ∀ {n : ℕ} (p : Fin n) → swap01 n (swap01 n p) ≡ p
swap01-invol {zero}              ()
swap01-invol {suc zero}          i = ≡refl
swap01-invol {suc (suc zero)}    i = opposite-involutive i
swap01-invol {suc (suc (suc n))} i =
  begin
    join 2 (suc n)
      (swapSum (splitAt 2
        (join 2 (suc n) (swapSum (splitAt 2 i)))))
  ≡⟨ cong (join 2 (suc n) ∘ swapSum)
         (splitAt-join 2 (suc n) (swapSum (splitAt 2 i))) ⟩
    join 2 (suc n) (swapSum (swapSum (splitAt 2 i)))
  ≡⟨ cong (join 2 (suc n)) (swapSum-invol (splitAt 2 i)) ⟩
    join 2 (suc n) (splitAt 2 i)
  ≡⟨ join-splitAt 2 (suc n) i ⟩
    i
  ∎

------------------------------------------------------------------------
-- The standard list label (route i to toℕ i) and its swap-conjugate
-- (route i to toℕ (swap01 n i)).
-- 标准列表标签（i 路由到 toℕ i）与其交换共轭（i 路由到
-- toℕ (swap01 n i)）。
------------------------------------------------------------------------
dList : LData
dList = record { uf = uf0 ; pts = λ { {A} n i → toℕ i } }

dSwap : LData
dSwap = record { uf = uf0 ; pts = λ { {A} n i → toℕ (swap01 n i) } }

------------------------------------------------------------------------
-- The total label action: conjugate the routing by swap01.
--   pts (σ d) n q = pts d n (swap01 n q).
-- σ dList is definitionally the swap-conjugate routing dSwap.
--
-- 满标签作用：用 swap01 共轭路由。
--   pts (σ d) n q = pts d n (swap01 n q)。
-- σ dList 定义性地即交换共轭路由 dSwap。
------------------------------------------------------------------------
σlabel : LData → LData
σlabel d = record
  { uf  = MO.CosmosData.uf d
  ; pts = λ { {A} n q → MO.CosmosData.pts d n (swap01 n q) }
  }

------------------------------------------------------------------------
-- The uniform swap01 edge self-bijection at a fixed child shape m.
--
-- fro (σ d edge → d edge) keeps the equation: the swapped position
-- swap01 q routes under d exactly where the σ d edge (q , eq) witnesses,
-- so eq already has the required type.
--
-- to (d edge → σ d edge) changes the routing from pts d n p to
-- pts d n (swap01 (swap01 p)); castTo is a single legal J on the neutral
-- involution redex (generalises to rigid p), computing to the identity.
-- The round-trips close by that same J.
--
-- 固定子形状 m 处一致的 swap01 边自双射。
--
-- fro（σ d 边 → d 边）保留等式：交换位置 swap01 q 在 d 下恰路由到
-- σ d 边 (q , eq) 所见证处，故 eq 类型已符合要求。
--
-- to（d 边 → σ d 边）把路由从 pts d n p 改为
-- pts d n (swap01 (swap01 p))；castTo 是对中性对合可约式的单个合法 J
-- （一般化为刚性 p），计算为恒等。往返由同一 J 闭合。
------------------------------------------------------------------------
private
  -- Routing of a label at shape n: position i ↦ child shape pts ℓ n i.
  -- 标签在形状 n 处的路由：位置 i ↦ 子形状 pts ℓ n i。
  ρof : (ℓ : LData) (n : ℕ) → Fin n → ℕ
  ρof ℓ n i = MO.CosmosData.pts ℓ n i

  -- A single J transport of the routing equation along a position
  -- equation ip : p₁ ≡ p₂.  p₁ and p₂ are independent variables, so
  -- matching ip with ≡refl is the J rule (generalises a neutral index),
  -- not K; it computes to the identity.
  --
  -- 沿位置等式 ip : p₁ ≡ p₂ 对路由等式的单个 J 传输。p₁、p₂ 为独立变
  -- 量，故用 ≡refl 匹配 ip 是 J 规则（一般化中性索引），而非 K；计算为
  -- 恒等。
  castTo : ∀ {n m : ℕ} (ℓ : LData) (ρ : Fin n → ℕ) {p₁ p₂ : Fin n}
         → p₁ ≡ p₂
         → (tt , m) ≡ (F₀ (MO.CosmosData.uf ℓ) (tt , n) , ρ p₂)
         → (tt , m) ≡ (F₀ (MO.CosmosData.uf ℓ) (tt , n) , ρ p₁)
  castTo ℓ ρ ≡refl eq = eq

  -- J for a routing edge fibre: two edges whose positions are related by
  -- ip and whose routing equations are related by castTo are equal.
  --
  -- 路由边纤维上的 J：位置由 ip 相关、路由等式由 castTo 相关的两条边
  -- 相等。
  edgeJ : ∀ {n m : ℕ} (ℓ : LData) (ρ : Fin n → ℕ) {p₁ p₂ : Fin n}
        → (ip : p₁ ≡ p₂)
        → (eq : (tt , m) ≡ (F₀ (MO.CosmosData.uf ℓ) (tt , n) , ρ p₂))
        → (p₁ , castTo ℓ ρ ip eq) ≡ (p₂ , eq)
  edgeJ ℓ ρ ≡refl eq = ≡refl

  -- CONDITIONAL proof irrelevance for the index set ⊤ × ℕ, used only in
  -- this ℕ/Fin example.  ℕ has decidable equality, so UIP holds here as a
  -- THEOREM (DecUIP, via Data.Nat.Properties.≡-irrelevant), not as the K
  -- axiom; ⊤ is a singleton.  This identifies two J transports taken
  -- along propositionally-equal involution proofs.  The M core and the
  -- GenCongruence engine remain pure J and do not use this.
  --
  -- 索引集 ⊤ × ℕ 的条件证明无关性，仅用于本 ℕ/Fin 示例。ℕ 具有可判定
  -- 等式，故 UIP 在此作为定理（DecUIP，经由
  -- Data.Nat.Properties.≡-irrelevant）成立，而非 K 公理；⊤ 为单例。它
  -- 用于识别沿命题相等的对合证明所做的两个 J 传输。M 内核与
  -- GenCongruence 引擎仍为纯 J，不使用此定理。
  -- Decidable equality on the index type ⊤ × ℕ (⊤ and ℕ both have
  -- decidable equality), and the resulting UIP-as-a-theorem.
  --
  -- 索引类型 ⊤ × ℕ 上的可判定等式（⊤ 与 ℕ 均有可判定等式），以及由此
  -- 得到的"作为定理的 UIP"。
  index-eq? : Relation.Binary.Definitions.DecidableEquality (Σ ⊤ (λ _ → ℕ))
  index-eq? = ≡-dec (_⊤≟_ {lzero}) _≟_

  pair-eq-irr : Irrelevant {A = Σ ⊤ (λ _ → ℕ)} _≡_
  pair-eq-irr = Decidable⇒UIP.≡-irrelevant index-eq?

  toAdj : ∀ {n m} (d : LData)
        → LE (tt , n) d (tt , m) → LE (tt , n) (σlabel d) (tt , m)
  toAdj {n = n} d (p , eq) =
    swap01 n p , castTo d (ρof d n) (swap01-invol p) eq

  froAdj : ∀ {n m} (d : LData)
        → LE (tt , n) (σlabel d) (tt , m) → LE (tt , n) d (tt , m)
  froAdj {n = n} d (q , eq) = swap01 n q , eq

  -- η closes by a single pure J (edgeJ) on the source fibre.
  -- η 由源纤维上的单个纯 J（edgeJ）闭合。
  adjη : ∀ {n m} d (e : LE (tt , n) d (tt , m))
       → froAdj d (toAdj d e) ≡ e
  adjη {n = n} d (p , eq) =
    edgeJ d (ρof d n) (swap01-invol p) eq

  -- ε closes by the same J on the target fibre, after identifying the two
  -- J transports along the two involution proofs with the conditional
  -- DecUIP irrelevance of the ⊤ × ℕ index set.
  --
  -- ε 先以 ⊤ × ℕ 索引集的条件 DecUIP 证明无关性识别沿两个对合证明的两
  -- 个 J 传输，再由目标纤维上的同一 J 闭合。
  adjε : ∀ {n m} d (e : LE (tt , n) (σlabel d) (tt , m))
       → toAdj d (froAdj d e) ≡ e
  adjε {n = n} d (q , eq) =
    let castA = castTo d (ρof d n) (swap01-invol (swap01 n q)) eq
        castB = castTo (σlabel d) (ρof (σlabel d) n) (swap01-invol q) eq
    in trans (cong (λ e0 → swap01 n (swap01 n q) , e0)
                   (pair-eq-irr castA castB))
             (edgeJ (σlabel d) (ρof (σlabel d) n) (swap01-invol q) eq)

  swapAdj : ∀ {n m} (d : LData)
          → FiberAdjˢ (propEqOn (LE (tt , n) (σlabel d) (tt , m)))
                      (propEqOn (LE (tt , n) d (tt , m)))
  swapAdj {n = n} {m = m} d = record
    { to       = toAdj d
    ; fro      = froAdj d
    ; to-cong  = λ eq → cong (toAdj d) eq
    ; fro-cong = λ eq → cong (froAdj d) eq
    ; η        = adjη d
    ; ε        = adjε d
    }

------------------------------------------------------------------------
-- General deterministic data for the identity index functor.
-- 恒等索引函子的一般确定性数据。
------------------------------------------------------------------------
swapGen : GenDet C₀ ListFC (idF {C = ShapeCat C₀ ListFC})
GenDet.σ   swapGen _ d = σlabel d
GenDet.pb  swapGen v = v , ≡refl
GenDet.adj swapGen (tt , n) d (tt , m) = swapAdj {n = n} {m = m} d

------------------------------------------------------------------------
-- The categorical label-changing deterministic endomorphism bundle.
-- Its map-cong is supplied by the GenCongruence engine.
--
-- 范畴改标签确定性自态射束。其 map-cong 由 GenCongruence 引擎供给。
------------------------------------------------------------------------
swapFMˢ : FMˢ (MO.sys C₀ ListFC (λ _ → propEqOn _))
              (MO.sys C₀ ListFC (λ _ → propEqOn _))
swapFMˢ = genFMˢ C₀ ListFC (idF {C = ShapeCat C₀ ListFC}) swapGen

------------------------------------------------------------------------
-- Non-identity witness at shape 2: the carried forward edge action
-- sends position 0 (routing to child shape 0 under dList) to position 1
-- (the σ dList = dSwap routing).  It cannot fix position 0.
--
-- 形状 2 处的非恒等见证：所携带的正向边作用把位置 0（dList 下路由到
-- 子形状 0）送到位置 1（σ dList = dSwap 路由）。它不可能固定位置 0。
------------------------------------------------------------------------
private
  -- Source dList edge at node shape 2, position 0, child shape 0.
  -- 节点形状 2、位置 0、子形状 0 处的源 dList 边。
  e0 : LE (tt , 2) dList (tt , 0)
  e0 = fzero , ≡refl

  -- The image edge is position 1.
  -- 像边为位置 1。
  e1 : LE (tt , 2) (σlabel dList) (tt , 0)
  e1 = fsuc fzero , ≡refl

private
  adjAt : FiberAdjˢ (propEqOn (LE (tt , 2) (σlabel dList) (tt , 0)))
                    (propEqOn (LE (tt , 2) dList (tt , 0)))
  adjAt = FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) (tt , 2) dList (tt , 0)

  -- The forward edge map is the adjunction to (source dList fibre to
  -- target σ dList fibre).
  -- 前向边映射为伴随 to（源 dList 纤维到目标 σ dList 纤维）。
  fwd : LE (tt , 2) dList (tt , 0) → LE (tt , 2) (σlabel dList) (tt , 0)
  fwd = FiberAdjˢ.to adjAt

swap-sends-0→1 : fwd e0 ≡ e1
swap-sends-0→1 = ≡refl

-- The forward edge leaving child shape 0 carries position 1, never
-- position 0: the relabelling is not the identity on edges.
--
-- 离开子形状 0 的前向边携带位置 1，绝非位置 0：该重标在边上不是恒等。
swap-nonidentity : ¬ (proj₁ (fwd e0) ≡ fzero)
swap-nonidentity ()
