------------------------------------------------------------------------
-- Colimit of a diagram of setoids with an arbitrary small shape.
--
-- The shape is a quiver: vertices K and arrows Q x y between them; a
-- diagram assigns a setoid D x to each vertex and a setoid morphism to
-- each arrow. This subsumes coproducts (Q empty), coequalizers (two
-- parallel arrows), pushouts (a span), ω-chains (K = ℕ with Q = suc),
-- and hence the colimit of any diagram whose shape is a category (take
-- Q to be its hom-sets; the category laws are not used by the coequalizer
-- universal property).
--
-- The colimit setoid is the disjoint union Σ K (Carrier (D x)) with the
-- equivalence closure of two generators:
--   same x≈  identifies equal elements within one fibre;
--   edge f   identifies a with its image D₁ f a along an arrow.
-- This is a SETOID quotient: the carrier is never collapsed, so no HIT,
-- univalence, K or transport is needed, and the fibres may carry arbitrary
-- setoids. The mediating morphism is the equivalence-closure fold.
--
-- Scope. Collapsing the closure to propositional equality on a bare Set
-- is a different theorem: it needs a set quotient (a HIT, absent under
-- --cubical-compatible) to construct and a provably non-UIP fibre to
-- refute, so that layer is independent of the flags, exactly as for the
-- chain direct limit. The index dimension is settled separately in
-- ColimitPolarity.
--
-- 任意小形状的 setoid 图示余极限。
--
-- 形状是一个 quiver：顶点 K 与顶点间的箭头 Q x y；图示给每个顶点一个
-- setoid D x，给每条箭头一个 setoid 态射。它涵盖余积（Q 为空）、余等
-- 化子（两条平行箭头）、推出（span）、ω-链（K = ℕ、Q = suc），从而涵盖
-- 任意范畴形状图示的余极限（取 Q 为其 hom 集；余等化子泛性质不使用范畴
-- 律）。
--
-- 余极限 setoid 是不交并 Σ K (Carrier (D x))，配以两个生成子的等价闭
-- 包：same x≈ 识别同一纤维内相等的元素；edge f 沿箭头把 a 与其像
-- D₁ f a 识别。这是 SETOID 商：载体从不被压合，故无需 HIT、univalence、
-- K 或传输，纤维可带任意 setoid。mediate 态射即等价闭包的 fold。
--
-- 范围。把闭包压成裸 Set 上的命题相等是另一个定理：构造需集合商（HIT，
-- --cubical-compatible 下缺失），证伪需可证不满足 UIP 的纤维，故该层与
-- 开关独立，与链直接极限相同。索引维在 ColimitPolarity 中另行闭合。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.SetoidColimit where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Construct.Closure.Equivalence as EqClosure
  using (EqClosure; setoid; return; symmetric; gfold)

open Func using (cong)
open Setoid using (Carrier; isEquivalence)

module _ {k c ℓ q : Level}
         (K : Set k)
         (Q : K → K → Set q)
         (D : K → Setoid c ℓ)
         (D₁ : ∀ {x y} → Q x y → Func (D x) (D y)) where

  -- Disjoint union of the fibres; an element carries its birth vertex.
  -- 各纤维的不交并；元素携带其诞生顶点。
  ColimCarrier : Set (k ⊔ c)
  ColimCarrier = Σ K λ x → Carrier (D x)

  -- Generating identification: within-fibre equality, or one arrow step.
  -- 生成性识别：纤维内相等，或沿一条箭头前进一步。
  data _∼₀_ : Rel ColimCarrier (k ⊔ c ⊔ q ⊔ ℓ) where
    same : ∀ {x} {a a' : Carrier (D x)}
         → Setoid._≈_ (D x) a a'
         → (x , a) ∼₀ (x , a')
    edge : ∀ {x y} (f : Q x y) {a : Carrier (D x)}
         → (x , a) ∼₀ (y , D₁ f ⟨$⟩ a)

  -- The colimit setoid: equivalence closure of the generators.
  -- 余极限 setoid：生成子的等价闭包。
  Colim : Setoid (k ⊔ c) (k ⊔ c ⊔ q ⊔ ℓ)
  Colim = setoid _∼₀_

  -- Leg of the canonical cocone: tag an element with its vertex.
  -- 规范余锥的腿：给元素打上顶点标签。
  inj : (x : K) → Func (D x) Colim
  inj x = record
    { to   = λ a → x , a
    ; cong = λ a≈ → return (same a≈)
    }

  -- Canonical cocone commutation: the image along f is the same element
  -- reached by one edge step, read backwards.
  -- 规范余锥交换：沿 f 的像即走一条 edge 后到达的同一元素（反向读取）。
  canonical-comm : ∀ {x y} (f : Q x y) {a : Carrier (D x)}
    → Setoid._≈_ Colim (y , D₁ f ⟨$⟩ a) (x , a)
  canonical-comm f {a} = symmetric _∼₀_ (return (edge f {a}))

  module Cocone {cN ℓN : Level} (N : Setoid cN ℓN) where

    -- A cocone: a leg out of every fibre, agreeing along every arrow.
    -- 余锥：每条纤维一条腿，且沿任意箭头相容。
    record Cocone : Set (k ⊔ c ⊔ ℓ ⊔ q ⊔ cN ⊔ ℓN) where
      field
        ψ    : (x : K) → Func (D x) N
        comm : ∀ {x y} (f : Q x y) {a : Carrier (D x)}
             → Setoid._≈_ N (ψ y ⟨$⟩ (D₁ f ⟨$⟩ a))
                            (ψ x ⟨$⟩ a)

    open Cocone

    -- The mediating map on representatives, then closed under the
    -- generators: same uses the leg's congruence, edge uses commutation.
    -- mediate 在代表元上的映射，再对生成子封闭：same 用腿的同余，edge
    -- 用交换律。
    rep : (cn : Cocone) → ColimCarrier → Carrier N
    rep cn (x , a) = ψ cn x ⟨$⟩ a

    rep-step : (cn : Cocone) → ∀ {u v} → u ∼₀ v
             → Setoid._≈_ N (rep cn u) (rep cn v)
    rep-step cn (same a≈)            = cong (ψ cn _) a≈
    rep-step cn (edge f {a})         = Setoid.sym N (comm cn f {a})

    -- Unique mediating morphism: the fold extends rep over the closure.
    -- 唯一 mediate 态射：fold 把 rep 扩张到整个等价闭包。
    mediate : (cn : Cocone) → Func Colim N
    mediate cn = record
      { to   = rep cn
      ; cong = gfold (isEquivalence N) (rep cn) (rep-step cn)
      }

    -- Factorisation: mediating after the leg is the leg (definitionally).
    -- 因子分解：mediate 复合腿即该腿（定义性成立）。
    factor : (cn : Cocone) (x : K) {a : Carrier (D x)}
      → Setoid._≈_ N (mediate cn ⟨$⟩ (x , a)) (ψ cn x ⟨$⟩ a)
    factor cn x = Setoid.refl N

    -- Uniqueness: any morphism agreeing with the legs on every fibre
    -- agrees with mediate at every tagged representative.
    -- 唯一性：任何在每条纤维上与各腿一致的态射，在每个带标签代表元上都
    -- 与 mediate 一致。
    unique : (cn : Cocone) (h : Func Colim N)
      → (∀ (x : K) {a : Carrier (D x)}
           → Setoid._≈_ N (h ⟨$⟩ (x , a)) (ψ cn x ⟨$⟩ a))
      → ∀ (u : ColimCarrier)
      → Setoid._≈_ N (h ⟨$⟩ u) (mediate cn ⟨$⟩ u)
    unique cn h fac (x , a) = fac x
