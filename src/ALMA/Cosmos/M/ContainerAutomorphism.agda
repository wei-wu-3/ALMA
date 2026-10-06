------------------------------------------------------------------------
-- Position automorphisms on the carried M base.
--
-- Legacy module Cosmos/ContainerAutomorphism defines PosAut, a per-shape
-- permutation τ of a container's positions with a two-sided inverse and a
-- NATURALITY field τ-nat
--
--   τ-nat : s ≡ t → τ t (subst (Position C) e p)
--                  ≡ subst (Position C) e (τ s p),
--
-- then builds a Group and a map aut→⇒ℱ sending each PosAut to a
-- structured simulation; τ-nat and onActP are discharged by repeated
-- subst along shape equalities.
--
-- On the carried M base the shape-equality transport, and hence τ-nat,
-- disappears altogether.  Two pieces remain, both subst-free:
--
--   Part A. The algebraic position-permutation group PosAutˢ over an
--           arbitrary indexed type family (S , P).  A position
--           automorphism is just a per-index permutation with a carried
--           two-sided inverse; there is no shape equality to be natural
--           along.  The group laws and the uniqueness of the inverse are
--           pure propositional-equality reasoning.
--
--   Part B. The induced fibre action.  In the M tower a position
--           permutation acts on EDGE FIBRES, and the bijection between
--           the routing fibres is a carried FiberAdjˢ (to/fro with η/ε),
--           not a map reconstructed by subst.  The self-fibre
--           adjunctions already form a group pointwise via idAdjˢ /
--           compAdjˢ / symAdjˢ, whose inverse laws are exactly the
--           carried η/ε.  This is the carried replacement for both
--           τ-nat and onActP: the "naturality" is the to-cong/fro-cong
--           data of FiberAdjˢ.
--
-- The realisation aut→FMˢ (turning a permutation into a structured
-- endomorphism of CosmosM trees) is the GenCongruence engine with the
-- edge adjunction SUPPLIED as data (GenDet.adj); it is not rebuilt here.
-- The boundary established in ListSwap / ListSwapDef is sharp:
--
--   * on a non-indexed position type with a DEFINITIONALLY involutive
--     permutation (Fin n ⊎ Fin n, flip), the fibre adjunction is pure
--     constructive J (ListSwapDef);
--   * on an indexed finite fibre (Fin n, splitAt/join/opposite), the
--     permutation is only propositionally involutive and ε needs the
--     index set's CONDITIONAL DecUIP (ListSwap) — a theorem, never a K
--     axiom.
--
-- There is therefore no generic pure-J aut→FMˢ; carrying the fibre
-- adjunction is the honest, debt-free formulation.
--
-- 携带 M 底座上的位置自同构。
--
-- 旧模块 Cosmos/ContainerAutomorphism 定义 PosAut：容器位置上的逐形
-- 状置换 τ，带双侧逆与自然性字段 τ-nat
--
--   τ-nat : s ≡ t → τ t (subst (Position C) e p)
--                  ≡ subst (Position C) e (τ s p)，
--
-- 再建一个 Group 与映射 aut→⇒ℱ（把每个 PosAut 送到结构化模拟）；
-- τ-nat 与 onActP 靠沿形状等式反复 subst 消去。
--
-- 在携带 M 底座上，形状等式传输（因而 τ-nat）整体消失。只剩两块，
-- 均零 subst：
--
--   A 部：任意索引类型族 (S , P) 上的代数位置置换群 PosAutˢ。位置自
--         同构就是带携带双侧逆的逐索引置换；不再有需要沿之自然的形
--         状等式。群律与逆的唯一性是纯命题等式推理。
--
--   B 部：诱导的纤维作用。M 塔中位置置换作用于边纤维，路由纤维间的
--         双射是携带的 FiberAdjˢ（to/fro 加 η/ε），而非靠 subst 重建
--         的映射。自纤维伴随经 idAdjˢ / compAdjˢ / symAdjˢ 已逐点构成
--         群，其逆律恰为携带的 η/ε。这是 τ-nat 与 onActp 的携带式替
--         代：“自然性”即 FiberAdjˢ 的 to-cong/fro-cong 数据。
--
-- aut→FMˢ 的实现（把置换变为 CosmosM 树的结构化自态射）是
-- GenCongruence 引擎，边伴随作为数据供给（GenDet.adj）；此处不重建。
-- ListSwap / ListSwapDef 划定的边界是锐利的：
--
--   * 在非索引位置类型上、置换定义性对合（Fin n ⊎ Fin n，flip），纤
--     维伴随是纯构造 J（ListSwapDef）；
--   * 在索引有限纤维（Fin n，splitAt/join/opposite）上，置换只命题
--     对合，ε 需索引集的条件 DecUIP（ListSwap）——是定理，绝非 K
--     公理。
--
-- 故不存在通用纯 J 的 aut→FMˢ；携带纤维伴随才是无债务的诚实表述。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.M.ContainerAutomorphism where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.Structures using (IsEquivalence)
open import Algebra.Bundles using (Group)
open import Function.Base using (_∘_)

open import ALMA.Base.MCorrSetoid
  using (EqOn; FiberAdjˢ; idAdjˢ; symAdjˢ; compAdjˢ)

------------------------------------------------------------------------
-- Part A. The algebraic position-permutation group
--
-- A 部：代数位置置换群
------------------------------------------------------------------------
module PositionPermutationGroup {s p : Level}
                                (S : Set s) (P : S → Set p) where

  -- A per-shape permutation of positions with a carried two-sided
  -- inverse.  There is NO naturality field: positions at distinct shapes
  -- are elements of distinct fibres, and in the carried architecture
  -- they are related by a carried FiberAdjˢ (Part B), never by subst
  -- along a shape equality.
  --
  -- 逐形状位置置换，携带双侧逆。无自然性字段：不同形状处的位置属于不
  -- 同纤维，在携带架构中它们由携带的 FiberAdjˢ（B 部）联系，绝不沿形
  -- 状等式 subst。
  record PosAutˢ : Set (s ⊔ p) where
    field
      τ       : (sh : S) → P sh → P sh
      τ⁻¹     : (sh : S) → P sh → P sh
      -- τ ∘ τ⁻¹ = id  (counit / right inverse of τ)
      -- τ ∘ τ⁻¹ = 恒等（余单位 / τ 的右逆）
      τ-τ⁻¹   : (sh : S) (q : P sh) → τ sh (τ⁻¹ sh q) ≡ q
      -- τ⁻¹ ∘ τ = id  (unit / left inverse of τ)
      -- τ⁻¹ ∘ τ = 恒等（单位 / τ 的左逆）
      τ⁻¹-τ   : (sh : S) (q : P sh) → τ⁻¹ sh (τ sh q) ≡ q
  open PosAutˢ public

  -- Identity position automorphism.
  -- 恒等位置自同构。
  idPosAutˢ : PosAutˢ
  idPosAutˢ = record
    { τ       = λ _ q → q
    ; τ⁻¹     = λ _ q → q
    ; τ-τ⁻¹   = λ _ _ → refl
    ; τ⁻¹-τ   = λ _ _ → refl
    }

  -- Composition: forward maps compose φ after ψ, inverses in reverse.
  -- 复合：正向映射按 φ 在 ψ 之后复合，逆向相反。
  infixl 20 _∘PosAutˢ_
  _∘PosAutˢ_ : PosAutˢ → PosAutˢ → PosAutˢ
  φ ∘PosAutˢ ψ = record
    { τ       = λ sh q → τ φ sh (τ ψ sh q)
    ; τ⁻¹     = λ sh q → τ⁻¹ ψ sh (τ⁻¹ φ sh q)
    ; τ-τ⁻¹   = λ sh q →
        begin
          τ φ sh (τ ψ sh (τ⁻¹ ψ sh (τ⁻¹ φ sh q)))
            ≡⟨ cong (τ φ sh) (τ-τ⁻¹ ψ sh (τ⁻¹ φ sh q)) ⟩
          τ φ sh (τ⁻¹ φ sh q)
            ≡⟨ τ-τ⁻¹ φ sh q ⟩
          q
        ∎
    ; τ⁻¹-τ = λ sh q →
        begin
          τ⁻¹ ψ sh (τ⁻¹ φ sh (τ φ sh (τ ψ sh q)))
            ≡⟨ cong (τ⁻¹ ψ sh) (τ⁻¹-τ φ sh (τ ψ sh q)) ⟩
          τ⁻¹ ψ sh (τ ψ sh q)
            ≡⟨ τ⁻¹-τ ψ sh q ⟩
          q
        ∎
    }
    where open ≡-Reasoning

  -- Inverse: swap the forward and backward maps and exchange the two
  -- round-trip laws.  No naturality proof is needed (there is no τ-nat).
  --
  -- 求逆：交换正反映射并对调两条往返律。无需自然性证明（无 τ-nat）。
  invPosAutˢ : PosAutˢ → PosAutˢ
  invPosAutˢ φ = record
    { τ       = τ⁻¹ φ
    ; τ⁻¹     = τ φ
    ; τ-τ⁻¹   = λ sh q → τ⁻¹-τ φ sh q
    ; τ⁻¹-τ   = λ sh q → τ-τ⁻¹ φ sh q
    }

  -- Pointwise equality of the forward permutations.
  -- 正向置换的逐点相等。
  infix 4 _≈PAˢ_
  _≈PAˢ_ : PosAutˢ → PosAutˢ → Set (s ⊔ p)
  φ ≈PAˢ ψ = ∀ (sh : S) (q : P sh) → τ φ sh q ≡ τ ψ sh q

  ≈PAˢ-isEquivalence : IsEquivalence _≈PAˢ_
  ≈PAˢ-isEquivalence = record
    { refl  = λ _ _ → refl
    ; sym   = λ eq sh q → sym (eq sh q)
    ; trans = λ eq₁ eq₂ sh q → trans (eq₁ sh q) (eq₂ sh q)
    }

  -- Composition respects pointwise equality.
  -- 复合保持逐点相等。
  ∘PosAutˢ-resp-≈ : ∀ {φ φ' ψ ψ'} → φ ≈PAˢ φ' → ψ ≈PAˢ ψ'
                  → (φ ∘PosAutˢ ψ) ≈PAˢ (φ' ∘PosAutˢ ψ')
  ∘PosAutˢ-resp-≈ {φ} {φ'} {ψ} {ψ'} φ≈φ' ψ≈ψ' sh q =
    begin
      τ φ sh (τ ψ sh q)
        ≡⟨ cong (τ φ sh) (ψ≈ψ' sh q) ⟩
      τ φ sh (τ ψ' sh q)
        ≡⟨ φ≈φ' sh (τ ψ' sh q) ⟩
      τ φ' sh (τ ψ' sh q)
    ∎
    where open ≡-Reasoning

  -- The inverse permutation is uniquely determined by the forward map
  -- (pure round-trip reasoning; no naturality is involved).
  --
  -- 逆置换由正向映射唯一确定（纯往返推理，不涉及自然性）。
  τ⁻¹-unique : {φ ψ : PosAutˢ} → φ ≈PAˢ ψ
             → (sh : S) (q : P sh) → τ⁻¹ φ sh q ≡ τ⁻¹ ψ sh q
  τ⁻¹-unique {φ} {ψ} φ≈ψ sh q =
    trans
      (sym (τ⁻¹-τ φ sh (τ⁻¹ φ sh q)))
      (trans
        (cong (τ⁻¹ φ sh) eq)
        (τ⁻¹-τ φ sh (τ⁻¹ ψ sh q)))
    where
      -- τ φ (τ⁻¹ φ q) ≡ q ≡ τ φ (τ⁻¹ ψ q), using the forward equality
      -- φ≈ψ at the point τ⁻¹ ψ q followed by ψ's own right-inverse law.
      --
      -- τ φ (τ⁻¹ φ q) ≡ q ≡ τ φ (τ⁻¹ ψ q)：在 τ⁻¹ ψ q 处用正向相等
      -- φ≈ψ，再接 ψ 自身的右逆律。
      eq : τ φ sh (τ⁻¹ φ sh q) ≡ τ φ sh (τ⁻¹ ψ sh q)
      eq = trans
             (τ-τ⁻¹ φ sh q)
             (sym (trans (φ≈ψ sh (τ⁻¹ ψ sh q)) (τ-τ⁻¹ ψ sh q)))

  -- The inverse operation respects pointwise equality.
  -- 求逆保持逐点相等。
  invPosAutˢ-cong : {φ ψ : PosAutˢ} → φ ≈PAˢ ψ
                  → invPosAutˢ φ ≈PAˢ invPosAutˢ ψ
  invPosAutˢ-cong {φ} {ψ} φ≈ψ sh q = τ⁻¹-unique {φ} {ψ} φ≈ψ sh q

  -- Group laws up to _≈PAˢ_.
  -- 模 _≈PAˢ_ 的群公理。
  ∘PosAutˢ-assoc : ∀ φ ψ χ
                 → (φ ∘PosAutˢ ψ) ∘PosAutˢ χ ≈PAˢ φ ∘PosAutˢ (ψ ∘PosAutˢ χ)
  ∘PosAutˢ-assoc _ _ _ _ _ = refl

  ∘PosAutˢ-identityˡ : ∀ φ → idPosAutˢ ∘PosAutˢ φ ≈PAˢ φ
  ∘PosAutˢ-identityˡ _ _ _ = refl

  ∘PosAutˢ-identityʳ : ∀ φ → φ ∘PosAutˢ idPosAutˢ ≈PAˢ φ
  ∘PosAutˢ-identityʳ _ _ _ = refl

  invPosAutˢ-left-inverse : ∀ φ → invPosAutˢ φ ∘PosAutˢ φ ≈PAˢ idPosAutˢ
  invPosAutˢ-left-inverse φ sh q = τ⁻¹-τ φ sh q

  invPosAutˢ-right-inverse : ∀ φ → φ ∘PosAutˢ invPosAutˢ φ ≈PAˢ idPosAutˢ
  invPosAutˢ-right-inverse φ sh q = τ-τ⁻¹ φ sh q

  -- The standard-library Group bundle of carried position automorphisms.
  -- 携带位置自同构的标准库 Group 打包。
  posAutˢGroup : Group (s ⊔ p) (s ⊔ p)
  posAutˢGroup = record
    { Carrier = PosAutˢ
    ; _≈_     = _≈PAˢ_
    ; _∙_     = _∘PosAutˢ_
    ; ε       = idPosAutˢ
    ; _⁻¹     = invPosAutˢ
    ; isGroup = record
        { isMonoid = record
            { isSemigroup = record
                { isMagma = record
                    { isEquivalence = ≈PAˢ-isEquivalence
                    ; ∙-cong = λ {x y u v} x≈y u≈v →
                        ∘PosAutˢ-resp-≈ {x} {y} {u} {v} x≈y u≈v
                    }
                ; assoc = ∘PosAutˢ-assoc
                }
            ; identity = ( ∘PosAutˢ-identityˡ , ∘PosAutˢ-identityʳ )
            }
        ; inverse = ( invPosAutˢ-left-inverse , invPosAutˢ-right-inverse )
        ; ⁻¹-cong = λ {x y} x≈y → invPosAutˢ-cong {x} {y} x≈y
        }
    }

------------------------------------------------------------------------
-- Part B. The group of carried self-fibre adjunctions.
--
-- A position permutation that relabels a Cosmos acts on the edge fibres;
-- its induced bijection is a FiberAdjˢ E E (to/fro with carried η/ε and
-- congruence).  These self-fibre adjunctions form a group POINTWISE: the
-- inverse laws are the carried η/ε themselves, so no equality is ever
-- eliminated and no naturality/subst appears.  This is the fibre-level
-- group in which the GenDet.adj of a carried automorphism lives.
--
-- B 部：携带自纤维伴随的群。
--
-- 重标 Cosmos 的位置置换作用于边纤维；其诱导双射是 FiberAdjˢ E E
-- （to/fro 带携带 η/ε 与同余）。这些自纤维伴随逐点成群：逆律即携带
-- η/ε 本身，故不消去任何等式，也不出现自然性/subst。这正是携带自同
-- 构的 GenDet.adj 所处的纤维级群。
------------------------------------------------------------------------
module FibreSelfAdjunctionGroup {c ℓ : Level} {P : Set c}
                               (E : EqOn {ℓ = ℓ} P) where
  open EqOn E using (_≈_) renaming (refl to ≈refl)

  -- A self-fibre adjunction: a carried bijection of P to itself.
  -- 自纤维伴随：P 到自身的携带双射。
  SelfAdj : Set (c ⊔ ℓ)
  SelfAdj = FiberAdjˢ E E

  idSelf : SelfAdj
  idSelf = idAdjˢ E

  -- Composition: a₁ then a₂ (to of the composite is to a₂ ∘ to a₁).
  -- 复合：先 a₁ 后 a₂（复合的 to 为 to a₂ ∘ to a₁）。
  compSelf : SelfAdj → SelfAdj → SelfAdj
  compSelf a₁ a₂ = compAdjˢ E E E a₁ a₂

  invSelf : SelfAdj → SelfAdj
  invSelf = symAdjˢ

  -- Pointwise group laws on the forward direction.  The inverse laws are
  -- exactly the carried ε/η; associativity and identity are definitional
  -- because composition of the to-maps is ordinary function composition.
  --
  -- 正向上的逐点群律。逆律恰为携带的 ε/η；结合律与单位律是定义性的，
  -- 因为 to 映射的复合即普通函数复合。
  comp-identityʳ-to : (a : SelfAdj) (p : P)
                    → FiberAdjˢ.to (compSelf a idSelf) p ≈ FiberAdjˢ.to a p
  comp-identityʳ-to a p = ≈refl

  comp-identityˡ-to : (a : SelfAdj) (p : P)
                    → FiberAdjˢ.to (compSelf idSelf a) p ≈ FiberAdjˢ.to a p
  comp-identityˡ-to a p = ≈refl

  -- inv after a (left inverse): to = fro a ∘ to a, and η a is the
  -- round-trip.  inv 在 a 之后（左逆）：to = fro a ∘ to a，η a 即往返。
  comp-inverseˡ-to : (a : SelfAdj) (r : P)
                   → FiberAdjˢ.to (compSelf a (invSelf a)) r ≈ r
  comp-inverseˡ-to a r = FiberAdjˢ.η a r

  -- a after inv (right inverse): to = to a ∘ fro a, and ε a is the
  -- round-trip.  a 在 inv 之后（右逆）：to = to a ∘ fro a，ε a 即往返。
  comp-inverseʳ-to : (a : SelfAdj) (p : P)
                   → FiberAdjˢ.to (compSelf (invSelf a) a) p ≈ p
  comp-inverseʳ-to a p = FiberAdjˢ.ε a p

  -- Associativity of the forward maps, pointwise definitional.
  -- 正向映射的结合律，逐点定义性。
  comp-assoc-to : (a b c : SelfAdj) (p : P)
                → FiberAdjˢ.to (compSelf (compSelf a b) c) p
                ≈ FiberAdjˢ.to (compSelf a (compSelf b c)) p
  comp-assoc-to a b c p = ≈refl
