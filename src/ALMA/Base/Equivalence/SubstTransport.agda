------------------------------------------------------------------------
-- subst-transport and the adjunction bridge
-- Three modules:
--   SubstTransport-Right    pointwise equality with target-side transport
--                           (uses posR, the projection side)
--   SubstTransport-Left     pointwise equality with source-side transport
--                           (uses posL, the embedding side)
--   SubstTransport-Adjoint  bridge: under posL ⊣ posR, the two layer
--                           relations interderive
-- These lift the fibre-wise adjunction skeleton _⊣_ from Core.agda to
-- concrete same-layer relations on F. The bridge closes the loop
-- between the adjunction skeleton and the two projections: each of
-- the two relations determines the other under the round-trip laws
--
-- subst 传输与伴随桥接
-- 三个模块：
--   SubstTransport-Right    逐点相等 + 目标侧传输（投影侧，用 posR）
--   SubstTransport-Left     逐点相等 + 源侧传输（嵌入侧，用 posL）
--   SubstTransport-Adjoint  桥接：在 posL ⊣ posR 下，两个同层关系互推
-- 这些模块把 Core.agda 中的纤维伴随骨架 _⊣_ 提升为 F 上的具体
-- 同层关系。桥接模块在伴随骨架与两个投影之间闭合回路：在往返
-- 律下，两个关系互相确定
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.SubstTransport where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core
  using (sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-subst; subst-subst-sym; subst-sym-subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import ALMA.Base.Equivalence.Core using (_⊣_)

------------------------------------------------------------------------
-- Given pos : (f : F) → ∀ {s : S} → P (shape f s) → R s, two F-elements are
-- _≈sr_-equal when they induce the same shape and, for every s and
-- every q : P (shape f s), the two pos-values agree after transporting
-- q along the shape equality to g's fibre
--
-- 给定 pos : (f : F) → ∀ {s : S} → P (shape f s) → R s，两个 F 元素
-- _≈sr_ 相等当且仅当它们诱导相同的 shape，且对每个 s 与
-- q : P (shape f s)，把 q 沿 shape 等式传输到 g 的纤维后，两个 pos 值一致
module _ {a b c d e : Level} {S : Set a} {T : Set c} (P : T → Set b)
         (R : S → Set d) {F : Set e} (shape : F → S → T) where
  module SubstTransport-Right
      (pos   : (f : F) → ∀ {s : S} → P (shape f s) → R s)
    where

    -- Pointwise equality with target-side transport
    --
    -- 逐点相等 + 目标侧传输
    record _≈sr_ (f g : F) : Set (a ⊔ b ⊔ c ⊔ d) where
      field

        -- The two shapes agree at every index
        --
        -- 两个 shape 在每个索引上相等
        shape-eq    : ∀ s → shape f s ≡ shape g s

        -- pos-values agree after transporting the input along shape-eq
        --
        -- 沿 shape-eq 传输输入后，两个 pos 值一致
        position-eq : ∀ s (q : P (shape f s))
                    → pos f q ≡ pos g (subst P (shape-eq s) q)

    open _≈sr_

    -- Reflexivity
    --
    -- 自反性
    ≈sr-refl : ∀ {f} → f ≈sr f
    ≈sr-refl = record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }

    -- Symmetry: invert the shape equality and absorb the two subst
    -- round-trips via subst-subst-sym
    --
    -- 对称性：反转 shape 等式，用 subst-subst-sym 吸收两个 subst 往返
    ≈sr-sym : ∀ {f g} → f ≈sr g → g ≈sr f
    ≈sr-sym {f} {g} p = record
      { shape-eq    = λ s → sym (p .shape-eq s)
      ; position-eq = λ s q →
          let e = p .shape-eq s
          in begin
            pos g q
              ≡⟨ cong (pos g) (sym (subst-subst-sym {P = P} e {p = q})) ⟩
            pos g (subst P e (subst P (sym e) q))
              ≡⟨ sym (p .position-eq s (subst P (sym e) q)) ⟩
            pos f (subst P (sym e) q)
            ∎
      }

    -- Transitivity: chain the two shape equalities, transport r through
    -- e₁ first, and merge the two subst steps via subst-subst
    --
    -- 传递性：串联两个 shape 等式，先沿 e₁ 传输 r，
    -- 再用 subst-subst 合并两个 subst 步骤
    ≈sr-trans : ∀ {f g h} → f ≈sr g → g ≈sr h → f ≈sr h
    ≈sr-trans {f} {g} {h} p q = record
      { shape-eq    = λ s → trans (p .shape-eq s) (q .shape-eq s)
      ; position-eq = λ s r →
          let e₁ = p .shape-eq s
              e₂ = q .shape-eq s
              r₁ = subst P e₁ r
          in begin
            pos f r
              ≡⟨ p .position-eq s r ⟩
            pos g r₁
              ≡⟨ q .position-eq s r₁ ⟩
            pos h (subst P e₂ r₁)
              ≡⟨ cong (pos h) (subst-subst {P = P} e₁ {y≡z = e₂} {p = r}) ⟩
            pos h (subst P (trans e₁ e₂) r)
            ∎
      }

    -- _≈sr_ is an equivalence relation
    --
    -- _≈sr_ 是等价关系
    ≈sr-isEquivalence : IsEquivalence _≈sr_
    ≈sr-isEquivalence = record
      { refl  = ≈sr-refl
      ; sym   = ≈sr-sym
      ; trans = ≈sr-trans
      }

    -- Equational reasoning combinators for _≈sr_
    -- Provides begin / _≈⟨_⟩_ / ∎ for chaining _≈sr_ steps
    --
    -- _≈sr_ 的等式推理组合子
    -- 提供 begin / _≈⟨_⟩_ / ∎ 用于串联 _≈sr_ 步骤
    module ≈sr-Reasoning where
      open import Relation.Binary.Reasoning.Setoid (record
        { Carrier       = F
        ; _≈_           = _≈sr_
        ; isEquivalence = ≈sr-isEquivalence
        }) public

  ------------------------------------------------------------------------
  -- Dual to SubstTransport-Right: pos : (f : F) → ∀ {s : S} → R s → P (shape f s),
  -- and the transport is applied to the output rather than the input
  --
  -- 与 SubstTransport-Right 对偶：pos : (f : F) → ∀ {s : S} → R s → P (shape f s)，
  -- 传输施加在输出而非输入上
  module SubstTransport-Left
      (pos   : (f : F) → ∀ {s : S} → R s → P (shape f s))
    where

    -- Pointwise equality with source-side transport
    --
    -- 逐点相等 + 源侧传输
    record _≈sl_ (f g : F) : Set (a ⊔ b ⊔ c ⊔ d) where
      field

        -- The two shapes agree at every index
        --
        -- 两个 shape 在每个索引上相等
        shape-eq    : ∀ s → shape f s ≡ shape g s

        -- pos-values agree after transporting the output along shape-eq
        --
        -- 沿 shape-eq 传输输出后，两个 pos 值一致
        position-eq : ∀ s (q : R s)
                    → subst P (shape-eq s) (pos f q) ≡ pos g q

    open _≈sl_

    -- Reflexivity
    --
    -- 自反性
    ≈sl-refl : ∀ {f} → f ≈sl f
    ≈sl-refl = record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }

    -- Symmetry: invert the shape equality and collapse the two subst
    -- round-trips via subst-sym-subst
    --
    -- 对称性：反转 shape 等式，用 subst-sym-subst 折叠两个 subst 往返
    ≈sl-sym : ∀ {f g} → f ≈sl g → g ≈sl f
    ≈sl-sym {f} {g} p = record
      { shape-eq    = λ s → sym (p .shape-eq s)
      ; position-eq = λ s q →
          let e = p .shape-eq s
          in begin
            subst P (sym e) (pos g q)
              ≡⟨ sym (cong (subst P (sym e)) (p .position-eq s q)) ⟩
            subst P (sym e) (subst P e (pos f q))
              ≡⟨ subst-sym-subst {P = P} e {p = pos f q} ⟩
            pos f q
            ∎
      }

    -- Transitivity: split the composed transport via subst-subst,
    -- then chain the two position equalities
    --
    -- 传递性：用 subst-subst 拆分复合传输，再串联两个 position 等式
    ≈sl-trans : ∀ {f g h} → f ≈sl g → g ≈sl h → f ≈sl h
    ≈sl-trans {f} {g} {h} p q = record
      { shape-eq    = λ s → trans (p .shape-eq s) (q .shape-eq s)
      ; position-eq = λ s r →
          let e₁ = p .shape-eq s
              e₂ = q .shape-eq s
          in begin
            subst P (trans e₁ e₂) (pos f r)
              ≡⟨ sym (subst-subst {P = P} e₁ {y≡z = e₂} {p = pos f r}) ⟩
            subst P e₂ (subst P e₁ (pos f r))
              ≡⟨ cong (subst P e₂) (p .position-eq s r) ⟩
            subst P e₂ (pos g r)
              ≡⟨ q .position-eq s r ⟩
            pos h r
            ∎
      }

    -- _≈sl_ is an equivalence relation
    --
    -- _≈sl_ 是等价关系
    ≈sl-isEquivalence : IsEquivalence _≈sl_
    ≈sl-isEquivalence = record
      { refl  = ≈sl-refl
      ; sym   = ≈sl-sym
      ; trans = ≈sl-trans
      }

    -- Equational reasoning combinators for _≈sl_
    -- Provides begin / _≈⟨_⟩_ / ∎ for chaining _≈sl_ steps
    --
    -- _≈sl_ 的等式推理组合子
    -- 提供 begin / _≈⟨_⟩_ / ∎ 用于串联 _≈sl_ 步骤
    module ≈sl-Reasoning where
      open import Relation.Binary.Reasoning.Setoid (record
        { Carrier       = F
        ; _≈_           = _≈sl_
        ; isEquivalence = ≈sl-isEquivalence
        }) public

  ------------------------------------------------------------------------
  -- Under posL ⊣ posR, the two same-layer relations _≈R_ (from posR)
  -- and _≈L_ (from posL) interderive at the same shape-equality:
  -- each determines the other. This closes the loop between the
  -- adjunction skeleton _⊣_ and the two projections
  --
  -- 在 posL ⊣ posR 下，两个同层关系 _≈R_（由 posR 给出）与 _≈L_
  -- （由 posL 给出）在同一 shape 等式下互推：彼此互相确定。这闭合
  -- 了伴随骨架 _⊣_ 与两个投影之间的回路
  module SubstTransport-Adjoint
      (posL : (f : F) → ∀ {s : S} → R s → P (shape f s))
      (posR : (f : F) → ∀ {s : S} → P (shape f s) → R s)
      (adj : _⊣_ P R shape posL posR)
    where

    unit   : ∀ f {s} (r : R s) → posR f (posL f r) ≡ r
    unit   = proj₁ adj

    counit : ∀ f {s} (p : P (shape f s)) → posL f (posR f p) ≡ p
    counit = proj₂ adj

    open SubstTransport-Right posR using (_≈sr_; ≈sr-isEquivalence)
    open SubstTransport-Left  posL using (_≈sl_; ≈sl-isEquivalence)

    -- _≈R_ implies _≈L_ by absorbing posL via unit and counit:
    -- first apply _≈R_'s position-eq at posL f r, then collapse the
    -- round-trip on g's side using counit
    --
    -- _≈R_ 经 unit 与 counit 吸收 posL 后得到 _≈L_：
    -- 先在 posL f r 处应用 _≈R_ 的 position-eq，再用 counit 折叠
    -- g 侧的往返
    ≈R→≈L : ∀ {f g} → f ≈sr g → f ≈sl g
    ≈R→≈L {f} {g} p = record
      { shape-eq    = _≈sr_.shape-eq p
      ; position-eq = λ s r →
          let e  = _≈sr_.shape-eq p s
              h₁ = _≈sr_.position-eq p s (posL f r)
              h₂ = unit f r
              h₃ = counit g (subst P e (posL f r))
          in begin
            subst P e (posL f r)
              ≡⟨ sym h₃ ⟩
            posL g (posR g (subst P e (posL f r)))
              ≡⟨ cong (posL g) (trans (sym h₁) h₂) ⟩
            posL g r
            ∎
      }

    -- _≈L_ implies _≈R_ by absorbing posR via counit and unit:
    -- dual to ≈R→≈L
    --
    -- _≈L_ 经 counit 与 unit 吸收 posR 后得到 _≈R_：与 ≈R→≈L 对偶
    ≈L→≈R : ∀ {f g} → f ≈sl g → f ≈sr g
    ≈L→≈R {f} {g} p = record
      { shape-eq    = _≈sl_.shape-eq p
      ; position-eq = λ s q →
          let e  = _≈sl_.shape-eq p s
              h₁ = _≈sl_.position-eq p s (posR f q)
              h₂ = counit f q
              h₃ = unit g (posR f q)
          in begin
            posR f q
              ≡⟨ sym h₃ ⟩
            posR g (posL g (posR f q))
              ≡⟨ cong (posR g) (trans (sym h₁) (cong (subst P e) h₂)) ⟩
            posR g (subst P e q)
            ∎
      }

    -- The two relations interderive on common shape-equalities
    --
    -- 两个关系在共同 shape 等式上互推
    ≈R↔≈L : ∀ {f g} → (f ≈sr g → f ≈sl g) × (f ≈sl g → f ≈sr g)
    ≈R↔≈L = ≈R→≈L , ≈L→≈R
