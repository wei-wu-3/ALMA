------------------------------------------------------------------------
-- the category rooted in the indexed coinductive type Mᵢ
--   DependentTransport  generic two-level dependent transport along an
--                       index equality plus a shape equality; used here
--                       only for the naturality of a fixed outer morphism
--   Mᵢ-Obj / Mᵢ-⇒       indexed objects and morphisms
--   Fiber / fiber-of / fiber-tr
--                       the flat two-field fibre of a morphism over a
--                       source point and a FIXED target index, the
--                       inclusion of a morphism, and the canonical
--                       J-transport of a fibre across an index equality
--   FE                  the flat shape+position fibre equality (the
--                       Right/projection-side single-layer relation,
--                       defined locally; no hand-nested telescope)
--   Mᵢ-≈                outer index equality STACKED with the inner FE
--                       relation; refl/sym/trans delegate to FE
--   MᵢCat              the resulting Category
--   Container-*        the ordinary container category as the trivial
--                       specialisation at I = ⊤
--
-- 扎根于索引余归纳类型 Mᵢ 的范畴
--   DependentTransport  沿“索引等式 + 形状等式”的泛化两层依赖传输；此处
--                       仅用于固定外态射的自然性
--   Mᵢ-Obj / Mᵢ-⇒       索引对象与态射
--   Fiber / fiber-of / fiber-tr
--                       态射在一个源点、一个“固定目标索引”上的扁平两字段
--                       纤维；态射到纤维的落入；纤维沿索引等式的规范 J 传输
--   FE                  扁平的“形状 + 位置”纤维相等（Right/投影侧单层关系，
--                       就地定义；不手拼嵌套望远镜）
--   Mᵢ-≈                外层索引相等与内层 FE 关系相堆叠；refl/sym/trans
--                       委托给 FE
--   MᵢCat              最终得到的 Category
--   Container-*        普通容器范畴，即 I = ⊤ 处的平凡特化
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCategory where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; subst)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-subst; subst-subst-sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function.Base using (id; _∘_)

open import Categories.Category.Core using (Category)

open import ALMA.Base.IndexedMType using (Mᵢ; fst; snd)

-- The two standard transport lemmas powering the flat fibre equivalence:
--   subst-subst-sym : subst P e (subst P (sym e) p) ≡ p   (symmetry round-trip)
--   subst-subst     : subst P g (subst P f p)
--                     ≡ subst P (trans f g) p             (transitivity merge)
-- These are exactly the lemmas used by SubstTransport-Right; the round-trip
-- and merge are therefore never written by hand
--
-- 支撑扁平纤维等价的两个标准传输引理：
--   subst-subst-sym 对称往返；subst-subst 传递合并
-- 它们正是 SubstTransport-Right 所用的引理，故往返与合并不手写

------------------------------------------------------------------------
-- Generic two-level dependent transport
-- Every lemma is defined by refl on INDEPENDENT bound variables (the only
-- legal place for J-elimination); concrete call sites only instantiate.
-- Kept for the naturality lemmas shape-nat / pos-nat of a fixed outer
-- morphism in the congruence section
--
-- 泛化两层依赖传输
-- 所有引理都对“独立绑定变量”以 refl 定义（J 消去唯一合法的位置），具体
-- 调用点只做实例化。此处保留它，是为了同余段中固定外态射的自然性引理
-- shape-nat / pos-nat
module DependentTransport
  {ℓᵢ ℓₐ ℓₚ : Level}
  {Idx : Set ℓᵢ} {Sh : Idx → Set ℓₐ}
  (Ps : (i : Idx) → Sh i → Set ℓₚ) where

  transport₂ : ∀ {i₁ i₂ : Idx} {a₁ : Sh i₁} {a₂ : Sh i₂}
    → (eᵢ : i₁ ≡ i₂) (eₛ : subst Sh eᵢ a₁ ≡ a₂)
    → Ps i₁ a₁ → Ps i₂ a₂
  transport₂ refl refl q = q

  subst-sym' : ∀ {i₁ i₂ : Idx} {a₁ : Sh i₁} {a₂ : Sh i₂}
    → (eᵢ : i₁ ≡ i₂) (eₛ : subst Sh eᵢ a₁ ≡ a₂)
    → subst Sh (sym eᵢ) a₂ ≡ a₁
  subst-sym' refl refl = refl

  transport₂-round : ∀ {i₁ i₂ : Idx} {a₁ : Sh i₁} {a₂ : Sh i₂}
    → (eᵢ : i₁ ≡ i₂) (eₛ : subst Sh eᵢ a₁ ≡ a₂) (q' : Ps i₂ a₂)
    → transport₂ eᵢ eₛ
        (transport₂ (sym eᵢ) (subst-sym' eᵢ eₛ) q') ≡ q'
  transport₂-round refl refl q' = refl

  subst-trans' : ∀ {i₁ i₂ i₃ : Idx}
                   {a₁ : Sh i₁} {a₂ : Sh i₂} {a₃ : Sh i₃}
    → (e₁ : i₁ ≡ i₂) (e₂ : i₂ ≡ i₃)
      (s₁ : subst Sh e₁ a₁ ≡ a₂) (s₂ : subst Sh e₂ a₂ ≡ a₃)
    → subst Sh (trans e₁ e₂) a₁ ≡ a₃
  subst-trans' refl refl refl refl = refl

  transport₂-trans : ∀ {i₁ i₂ i₃ : Idx}
                       {a₁ : Sh i₁} {a₂ : Sh i₂} {a₃ : Sh i₃}
    → (e₁ : i₁ ≡ i₂) (e₂ : i₂ ≡ i₃)
      (s₁ : subst Sh e₁ a₁ ≡ a₂) (s₂ : subst Sh e₂ a₂ ≡ a₃)
      (q : Ps i₁ a₁)
    → transport₂ e₂ s₂ (transport₂ e₁ s₁ q)
      ≡ transport₂ (trans e₁ e₂) (subst-trans' e₁ e₂ s₁ s₂) q
  transport₂-trans refl refl refl refl q = refl

------------------------------------------------------------------------
-- Mᵢ category objects
--
-- Mᵢ 范畴对象
record Mᵢ-Obj (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    I    : Set i
    A    : I → Set a
    B    : (i : I) (a : A i) → Set b
    next : (i : I) (a : A i) (p : B i a) → I
    root : I
open Mᵢ-Obj public

------------------------------------------------------------------------
-- Mᵢ category morphisms
-- pos is contravariant on positions
--
-- Mᵢ 范畴态射；pos 在位置上反变
record Mᵢ-⇒ {i₁ a₁ b₁ i₂ a₂ b₂}
               (X : Mᵢ-Obj i₁ a₁ b₁)
               (Y : Mᵢ-Obj i₂ a₂ b₂)
  : Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂) where
  field
    idx   : I X → I Y
    shape : (x : I X) → A X x → A Y (idx x)
    pos   : (x : I X) (ax : A X x)
          → B Y (idx x) (shape x ax) → B X x ax
open Mᵢ-⇒ public

------------------------------------------------------------------------
-- Identity and composition (definitionally associative, idᵢ the unit)
--
-- 恒等与复合（定义性结合，idᵢ 为单位）
idᵢ : ∀ {i a b} {X : Mᵢ-Obj i a b} → Mᵢ-⇒ X X
idᵢ {X = X} = record
  { idx = id ; shape = λ _ → id ; pos = λ _ _ → id }

infixr 9 _∘ᵢ_
_∘ᵢ_ : ∀ {i₁ a₁ b₁ i₂ a₂ b₂ i₃ a₃ b₃}
      {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂} {Z : Mᵢ-Obj i₃ a₃ b₃}
      → Mᵢ-⇒ Y Z → Mᵢ-⇒ X Y → Mᵢ-⇒ X Z
_∘ᵢ_ g f = record
  { idx   = idx g ∘ idx f
  ; shape = λ x → shape g (idx f x) ∘ shape f x
  ; pos   = λ x ax → pos f x ax ∘ pos g (idx f x) (shape f x ax)
  }

------------------------------------------------------------------------
-- The flat morphism fibre over a source point and a FIXED target index
-- At fixed x and i this is exactly a non-indexed container arrow
-- (shape map + contravariant position map): the (shape , pos) shape that
-- SubstTransport-Right handles. Keeping it a flat named record (rather
-- than collapsing it into a nested Σ-telescope) is what lets us reuse the
-- already-proved single-layer equivalence
--
-- 态射在一个源点、一个“固定目标索引”上的扁平纤维
-- 固定 x 与 i 时，这正是一个非索引容器箭头（形状映射 + 反变位置映射），
-- 即 SubstTransport-Right 处理的 (shape , pos) 结构。把它保留为扁平具名
-- record（而不是塌缩成嵌套 Σ 望远镜），才能复用已证好的单层等价关系
record Fiber {i₁ a₁ b₁ i₂ a₂ b₂}
             {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
             (x : I X) (i : I Y)
  : Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂) where
  field
    shp : A X x → A Y i
    pso : (ax : A X x) → B Y i (shp ax) → B X x ax

-- The fibre of a morphism f at x, written against its own target index
--
-- 态射 f 在 x 处、写在其自身目标索引上的纤维
fiber-of : ∀ {i₁ a₁ b₁ i₂ a₂ b₂}
             {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
             (f : Mᵢ-⇒ X Y) (x : I X)
           → Fiber {X = X} {Y = Y} x (idx f x)
fiber-of f x = record { shp = shape f x ; pso = pos f x }

-- Canonical J-transport of a flat fibre along a target-index equality.
-- Defined by refl on independent indices, so the two fields are moved
-- automatically; this is the SINGLE boundary transport, never hand-nested
--
-- 扁平纤维沿目标索引等式的规范 J 传输。对独立索引以 refl 定义，两个字段
-- 自动搬运；这是唯一的边界传输，绝不手拼
fiber-tr : ∀ {i₁ a₁ b₁ i₂ a₂ b₂}
             {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
             {x : I X} {i j : I Y}
         → i ≡ j
         → Fiber {X = X} {Y = Y} x i
         → Fiber {X = X} {Y = Y} x j
fiber-tr refl φ = φ

------------------------------------------------------------------------
-- FE: the flat shape+position equality on fibres (Right/projection side)
-- Fixed source point x and target index i:
--   S = A X x        (the pointwise shape variable)
--   T = A Y i        (target shapes at the common index)
--   P = B Y i        (target positions, contravariant input)
--   R = B X x        (source positions, output)
--   F = Fiber x i    (shape = Fiber.shp, pos = Fiber.pso)
--
-- This is the SAME single-layer relation as SubstTransport-Right, defined
-- locally because that nested module lives inside a parameterised anonymous
-- module and is therefore not re-exported (Agda lifts data/record/functions
-- from anonymous modules, but not nested named modules). The proofs are
-- identical: symmetry absorbs the round-trip via subst-subst-sym and
-- transitivity merges transports via subst-subst — no hand-nested telescope
-- and no hand-written transport round-trip
--
-- FE：纤维上的扁平“形状 + 位置”相等（Right/投影侧）
-- 固定源点 x 与目标索引 i：
--   S = A X x、T = A Y i、P = B Y i、R = B X x、F = Fiber x i。
-- 这与 SubstTransport-Right 是同一个单层关系；之所以就地定义，是因为那个
-- 嵌套 module 位于带参数的匿名模块内部、不会被 re-export（Agda 会提升匿名
-- 模块中的 data/record/函数，但不提升嵌套具名 module）。证明完全一致：对称
-- 用 subst-subst-sym 吸收往返，传递用 subst-subst 合并传输——不手拼望远镜，
-- 也不手写传输往返
module FE {i₁ a₁ b₁ i₂ a₂ b₂}
          {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
          (x : I X) (i : I Y) where

  -- Fib pins the implicit object parameters to THIS module's X Y; writing
  -- bare `Fiber x i` would leave Agda to infer the objects through the
  -- non-injective record projection I, which produces duplicate object
  -- metavariables and blocked universe levels
  --
  -- Fib 把隐式对象参数钉死为本模块的 X Y；若直接写 `Fiber x i`，Agda 需经
  -- 非单射的记录投影 I 反推对象，会产生重复对象元变量与阻塞的层级
  private
    Fib : Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂)
    Fib = Fiber {X = X} {Y = Y} x i

    shpᵢ : Fib → A X x → A Y i
    shpᵢ φ = Fiber.shp φ

    psoᵢ : (φ : Fib) (ax : A X x)
         → B Y i (Fiber.shp φ ax) → B X x ax
    psoᵢ φ = Fiber.pso φ

  record _≈sr_ (α β : Fib)
    : Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂) where
    field
      -- Shapes agree at every source element
      --
      -- 两个形状在每个源元素上相等
      shape-eq : ∀ (ax : A X x)
               → shpᵢ α ax ≡ shpᵢ β ax
      -- After transporting the target position along shape-eq, the two
      -- (contravariant) source positions agree
      --
      -- 把目标位置沿 shape-eq 传输后，两个（反变）源位置相等
      position-eq : ∀ (ax : A X x)
                      (q : B Y i (shpᵢ α ax))
                  → psoᵢ α ax q
                  ≡ psoᵢ β ax
                      (subst (B Y i) (shape-eq ax) q)
  open _≈sr_ public

  -- Reflexivity.
  --
  -- 自反性。
  ≈sr-refl : ∀ {α : Fib} → α ≈sr α
  ≈sr-refl = record
    { shape-eq    = λ _ → refl
    ; position-eq = λ _ _ → refl
    }

  -- Symmetry: reverse the shape equality and absorb the two-transport
  -- round-trip with subst-subst-sym
  --
  -- 对称性：反转形状等式，用 subst-subst-sym 吸收两次传输的往返
  ≈sr-sym : ∀ {α β : Fib} → α ≈sr β → β ≈sr α
  ≈sr-sym {α = α} {β = β} p = record
    { shape-eq    = λ ax → sym (shape-eq p ax)
    ; position-eq = λ ax q →
        let e = shape-eq p ax in
        begin
          psoᵢ β ax q
            ≡⟨ cong (psoᵢ β ax)
                   (sym (subst-subst-sym {P = B Y i} e {p = q})) ⟩
          psoᵢ β ax
            (subst (B Y i) e (subst (B Y i) (sym e) q))
            ≡⟨ sym (position-eq p ax (subst (B Y i) (sym e) q)) ⟩
          psoᵢ α ax (subst (B Y i) (sym e) q)
        ∎
    }

  -- Transitivity: chain the shape equalities and merge the two transports
  -- with subst-subst
  --
  -- 传递性：串联形状等式，用 subst-subst 合并两次传输
  ≈sr-trans : ∀ {α β γ : Fib} → α ≈sr β → β ≈sr γ → α ≈sr γ
  ≈sr-trans {α = α} {β = β} {γ = γ} p q = record
    { shape-eq    = λ ax → trans (shape-eq p ax) (shape-eq q ax)
    ; position-eq = λ ax r →
        let e₁ = shape-eq p ax
            e₂ = shape-eq q ax
            r₁ = subst (B Y i) e₁ r
        in begin
          psoᵢ α ax r
            ≡⟨ position-eq p ax r ⟩
          psoᵢ β ax r₁
            ≡⟨ position-eq q ax r₁ ⟩
          psoᵢ γ ax (subst (B Y i) e₂ r₁)
            ≡⟨ cong (psoᵢ γ ax)
                   (subst-subst {P = B Y i} e₁ {y≡z = e₂} {p = r}) ⟩
          psoᵢ γ ax (subst (B Y i) (trans e₁ e₂) r)
        ∎
    }

------------------------------------------------------------------------
-- Mᵢ morphism equality: outer index equality STACKED with inner FE
-- At each x we record an index equality eᵢ, then compare the fibres over
-- the common index idx f x, after pulling g's fibre back once along
-- sym eᵢ via fiber-tr. The inner relation is the flat _≈sr_; there is no
-- hand-nested Σ-telescope and no naked subst in this definition
--
-- Mᵢ 态射相等：外层索引相等与内层 FE 相堆叠
-- 每个 x 记录一个索引等式 eᵢ，然后在公共索引 idx f x 上比较纤维：先用
-- fiber-tr 沿 sym eᵢ 把 g 的纤维回拉一次。内层关系即扁平的 _≈sr_；本
-- 定义中没有手拼的 Σ 望远镜，也没有裸 subst
module _ {i₁ a₁ b₁ i₂ a₂ b₂}
        {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂} where

  -- FE instance with object parameters anchored to this module's X Y,
  -- avoiding object metavariables through the non-injective projection I
  --
  -- 对象参数钉死为本模块 X Y 的 FE 实例，避免经非单射投影 I 产生对象元变量
  private
    module FE' (x : I X) (i : I Y) =
      FE {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
         {i₂ = i₂} {a₂ = a₂} {b₂ = b₂} {X = X} {Y = Y} x i

  Mᵢ-≈ : (f g : Mᵢ-⇒ X Y) → Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂)
  Mᵢ-≈ f g = ∀ (x : I X) →
    Σ (idx f x ≡ idx g x)
      λ eᵢ → FE'._≈sr_ x (idx f x)
               (fiber-of f x)
               (fiber-tr (sym eᵢ) (fiber-of g x))

  -- Heterogeneous symmetry of the stacked relation. e' is the REVERSED
  -- index equality (the first component of the reversed pair); J on the
  -- independent index reduces the whole boundary to ≈sr-sym — the
  -- transport round-trip is handled by J and never written by hand
  --
  -- 堆叠关系的异构对称。e' 是“反向后的索引等式”（反向对的第一分量）；
  -- 对独立索引做 J，整个边界归约为 ≈sr-sym——传输往返由 J 处理，不手写
  ≈fib-sym : ∀ (x : I X) {i j : I Y} (e' : j ≡ i)
               {α : Fiber {X = X} {Y = Y} x i}
               {β : Fiber {X = X} {Y = Y} x j}
           → FE'._≈sr_ x i α (fiber-tr e' β)
           → FE'._≈sr_ x j β (fiber-tr (sym e') α)
  ≈fib-sym x refl h = FE'.≈sr-sym x _ h

  -- Heterogeneous transitivity; J on the two independent index equalities
  -- reduces the boundary to ≈sr-trans (transport merge handled by J)
  --
  -- 异构传递；对两条独立索引等式做 J，边界归约为 ≈sr-trans（传输合并由
  -- J 处理）
  ≈fib-trans : ∀ (x : I X) {i j k : I Y}
                 (e₁ : i ≡ j) (e₂ : j ≡ k)
                 {α : Fiber {X = X} {Y = Y} x i}
                 {β : Fiber {X = X} {Y = Y} x j}
                 {γ : Fiber {X = X} {Y = Y} x k}
             → FE'._≈sr_ x i α (fiber-tr (sym e₁) β)
             → FE'._≈sr_ x j β (fiber-tr (sym e₂) γ)
             → FE'._≈sr_ x i α (fiber-tr (sym (trans e₁ e₂)) γ)
  ≈fib-trans x refl refl h₁ h₂ = FE'.≈sr-trans x _ h₁ h₂

  Mᵢ-≈-refl : (f : Mᵢ-⇒ X Y) → Mᵢ-≈ f f
  Mᵢ-≈-refl f x = refl , FE'.≈sr-refl x (idx f x)

  Mᵢ-≈-sym : {f g : Mᵢ-⇒ X Y} → Mᵢ-≈ f g → Mᵢ-≈ g f
  Mᵢ-≈-sym p x
    with p x
  ... | eᵢ , h = sym eᵢ , ≈fib-sym x (sym eᵢ) h

  Mᵢ-≈-trans : {f g h : Mᵢ-⇒ X Y} → Mᵢ-≈ f g → Mᵢ-≈ g h → Mᵢ-≈ f h
  Mᵢ-≈-trans p q x
    with p x | q x
  ... | e₁ , h₁ | e₂ , h₂ =
      trans e₁ e₂ , ≈fib-trans x e₁ e₂ h₁ h₂

  Mᵢ-≈-isEquivalence : IsEquivalence Mᵢ-≈
  Mᵢ-≈-isEquivalence = record
    { refl  = λ {f} → Mᵢ-≈-refl f
    ; sym   = λ {f g} → Mᵢ-≈-sym {f = f} {g = g}
    ; trans = λ {f g h} → Mᵢ-≈-trans {f = f} {g = g} {h = h}
    }

------------------------------------------------------------------------
-- Congruence of composition
-- shape-nat / pos-nat express that a FIXED outer morphism G commutes
-- with dependent transport of shapes/positions; they are refl on
-- independent index/shape variables. Right and left congruence then only
-- repack the already-flat FE record (J on the outer index equality); the
-- inner shape/position equivalence is inherited, never re-derived
--
-- 复合的同余
-- shape-nat / pos-nat 表达“固定外态射 G”与形状/位置的依赖传输相交换，
-- 在独立索引/形状变量上为 refl。右、左同余随后只重新打包已是扁平的 FE
-- record（对外层索引等式做 J）；内层形状/位置相等直接继承，不再重导
module _ {i₁ a₁ b₁ i₂ a₂ b₂ i₃ a₃ b₃ : Level}
        {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂} {Z : Mᵢ-Obj i₃ a₃ b₃}
  where

  private
    module FE-XY (x : I X) (i : I Y) =
      FE {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
         {i₂ = i₂} {a₂ = a₂} {b₂ = b₂} {X = X} {Y = Y} x i
    module FE-YZ (y : I Y) (i : I Z) =
      FE {i₁ = i₂} {a₁ = a₂} {b₁ = b₂}
         {i₂ = i₃} {a₂ = a₃} {b₂ = b₃} {X = Y} {Y = Z} y i
    module FE-XZ (x : I X) (i : I Z) =
      FE {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
         {i₂ = i₃} {a₂ = a₃} {b₂ = b₃} {X = X} {Y = Z} x i

    -- Canonical J-naturality of a morphism's contravariant position with
    -- respect to a shape equality at a FIXED target index y. Transport the
    -- outer position along cong (shape G y) s and the source position along
    -- s; J on the INDEPENDENT shape variables reduces the whole diagram to
    -- refl. No coherence hypothesis on G is required (every dependent
    -- function is natural w.r.t. this path-over transport)
    --
    -- 态射反变位置在“固定目标索引 y”处对形状等式的规范 J 自然性：外层位置
    -- 沿 cong (shape G y) s 传输、源位置沿 s 传输；对独立形状变量做 J，整
    -- 个图归约为 refl。无需对 G 加相干条件（任何依赖函数对此路径传输都是
    -- 自然的）
    pos-nat-shape : (G : Mᵢ-⇒ Y Z) (y : I Y)
      → ∀ {b₁ b₂ : A Y y} (s : b₁ ≡ b₂)
          (qZ : B Z (idx G y) (shape G y b₁))
      → subst (B Y y) s (pos G y b₁ qZ)
        ≡ pos G y b₂
            (subst (B Z (idx G y)) (cong (shape G y) s) qZ)
    pos-nat-shape G y refl qZ = refl

  -- Composite fibres from an arbitrary outer/inner fibre. Defining the
  -- congruence lemmas against these (rather than against idx G (idx F x))
  -- lets J act on INDEPENDENT index variables; when applied to fiber-of
  -- they reduce definitionally to fiber-of (G ∘ᵢ F)
  --
  -- 由任意外/内层纤维构造复合纤维。同余引理针对它们（而非复合项
  -- idx G (idx F x)）陈述，使 J 作用于独立索引变量；应用到 fiber-of 时
  -- 它们定义性归约为 fiber-of (G ∘ᵢ F)
  private
    comp-fibʳ : (F : Mᵢ-⇒ X Y) (x : I X) {i : I Z}
              → Fiber {X = Y} {Y = Z} (idx F x) i
              → Fiber {X = X} {Y = Z} x i
    comp-fibʳ F x γ = record
      { shp = λ ax → Fiber.shp γ (shape F x ax)
      ; pso = λ ax qZ → pos F x ax (Fiber.pso γ (shape F x ax) qZ)
      }

    comp-fibˡ : (G : Mᵢ-⇒ Y Z) (x : I X) {y : I Y}
              → Fiber {X = X} {Y = Y} x y
              → Fiber {X = X} {Y = Z} x (idx G y)
    comp-fibˡ G x {y = y} δ = record
      { shp = λ ax → shape G y (Fiber.shp δ ax)
      ; pso = λ ax qZ → Fiber.pso δ ax (pos G y (Fiber.shp δ ax) qZ)
      }

  -- Right congruence, fixed inner F, vary G₁ ≈ G₂. The outer index equality
  -- is abstracted over INDEPENDENT i j (J by refl); the FE record is then
  -- repacked by precomposing shapes with shape F and postcomposing
  -- positions with pos F
  --
  -- 右同余：内态射 F 固定，变动 G₁ ≈ G₂。外层索引等式抽象为独立的 i j
  -- （以 refl 做 J）；随后把形状用 shape F 预复合、位置用 pos F 后复合，
  -- 重新打包 FE record
  respʳ-fib : {F : Mᵢ-⇒ X Y}
              (x : I X)
              {i j : I Z} (e : i ≡ j)
              (α : Fiber {X = Y} {Y = Z} (idx F x) i)
              (β : Fiber {X = Y} {Y = Z} (idx F x) j)
            → FE-YZ._≈sr_ (idx F x) i α (fiber-tr (sym e) β)
            → FE-XZ._≈sr_ x i
                (comp-fibʳ F x α)
                (fiber-tr (sym e) (comp-fibʳ F x β))
  respʳ-fib {F = F} x refl α β
            record { shape-eq = se ; position-eq = pe } =
    record
      { shape-eq    = λ ax → se (shape F x ax)
      ; position-eq = λ ax qZ →
          cong (pos F x ax) (pe (shape F x ax) qZ)
      }

  -- Left congruence, fixed outer G, vary F₁ ≈ F₂. The intermediate index
  -- equality is abstracted over INDEPENDENT y₁ y₂ (J by refl); the shape
  -- field uses shape-nat and the position field threads pos-nat
  --
  -- 左同余：外态射 G 固定，变动 F₁ ≈ F₂。中间索引等式抽象为独立的
  -- y₁ y₂（以 refl 做 J）；形状字段用 shape-nat，位置字段串接 pos-nat
  respˡ-fib : {G : Mᵢ-⇒ Y Z}
              (x : I X)
              {y₁ y₂ : I Y} (e : y₁ ≡ y₂)
              (α : Fiber {X = X} {Y = Y} x y₁)
              (β : Fiber {X = X} {Y = Y} x y₂)
            → FE-XY._≈sr_ x y₁ α (fiber-tr (sym e) β)
            → FE-XZ._≈sr_ x (idx G y₁)
                (comp-fibˡ G x α)
                (fiber-tr (sym (cong (idx G) e)) (comp-fibˡ G x β))
  respˡ-fib {G = G} x {y} refl α β
            record { shape-eq = se ; position-eq = pe } =
    record
      { shape-eq    = λ ax → cong (shape G y) (se ax)
      ; position-eq = λ ax qZ →
          trans (pe ax (pos G y (Fiber.shp α ax) qZ))
                (cong (Fiber.pso β ax)
                      (pos-nat-shape G y (se ax) qZ))
      }

  ∘ᵢ-resp-≈ʳ : {G₁ G₂ : Mᵢ-⇒ Y Z} {F : Mᵢ-⇒ X Y}
             → Mᵢ-≈ G₁ G₂ → Mᵢ-≈ (G₁ ∘ᵢ F) (G₂ ∘ᵢ F)
  ∘ᵢ-resp-≈ʳ {G₁ = G₁} {G₂ = G₂} {F = F} eqG x
    with eqG (idx F x)
  ... | e , hG =
      e , respʳ-fib {F = F} x e
            (fiber-of G₁ (idx F x)) (fiber-of G₂ (idx F x)) hG

  ∘ᵢ-resp-≈ˡ : {F₁ F₂ : Mᵢ-⇒ X Y} {G : Mᵢ-⇒ Y Z}
             → Mᵢ-≈ F₁ F₂ → Mᵢ-≈ (G ∘ᵢ F₁) (G ∘ᵢ F₂)
  ∘ᵢ-resp-≈ˡ {F₁ = F₁} {F₂ = F₂} {G = G} eqF x
    with eqF x
  ... | e , hF =
      cong (idx G) e ,
        respˡ-fib {G = G} x e (fiber-of F₁ x) (fiber-of F₂ x) hF

  -- Binary congruence in stdlib order: outer equality first. All implicit
  -- objects/levels/morphisms of the cross-module Mᵢ-≈-trans are supplied
  -- explicitly (source X, target Z; target-level slot filled with Z's
  -- i₃/a₃/b₃)
  --
  -- 二元同余，按标准库顺序：先外层相等。跨模块 Mᵢ-≈-trans 的全部隐式
  -- 对象/层级/态射均显式提供（源 X、目标 Z；目标层级位用 Z 的 i₃/a₃/b₃）
  ∘ᵢ-resp-≈ : {F₁ F₂ : Mᵢ-⇒ X Y} {G₁ G₂ : Mᵢ-⇒ Y Z}
            → Mᵢ-≈ G₁ G₂ → Mᵢ-≈ F₁ F₂
            → Mᵢ-≈ (G₁ ∘ᵢ F₁) (G₂ ∘ᵢ F₂)
  ∘ᵢ-resp-≈ {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} eqG eqF =
    Mᵢ-≈-trans
      {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
      {i₂ = i₃} {a₂ = a₃} {b₂ = b₃}
      {X = X} {Y = Z}
      {f = G₁ ∘ᵢ F₁}
      {g = G₁ ∘ᵢ F₂}
      {h = G₂ ∘ᵢ F₂}
      (∘ᵢ-resp-≈ˡ {F₁ = F₁} {F₂ = F₂} {G = G₁} eqF)
      (∘ᵢ-resp-≈ʳ {G₁ = G₁} {G₂ = G₂} {F = F₂} eqG)

------------------------------------------------------------------------
-- Category laws (definitional refl in both directions)
--
-- 范畴定律（两个方向均为定义性 refl）
module _ {i a b} {W X Y Z : Mᵢ-Obj i a b}
         {f : Mᵢ-⇒ W X} {g : Mᵢ-⇒ X Y} {h : Mᵢ-⇒ Y Z} where

  private
    module FE-WZ (x : I W) (k : I Z) =
      FE {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = W} {Y = Z} x k

  ∘ᵢ-assoc : Mᵢ-≈ ((h ∘ᵢ g) ∘ᵢ f) (h ∘ᵢ (g ∘ᵢ f))
  ∘ᵢ-assoc x = refl , FE-WZ.≈sr-refl x _

  ∘ᵢ-sym-assoc : Mᵢ-≈ (h ∘ᵢ (g ∘ᵢ f)) ((h ∘ᵢ g) ∘ᵢ f)
  ∘ᵢ-sym-assoc x = refl , FE-WZ.≈sr-refl x _

module _ {i a b} {X Y : Mᵢ-Obj i a b} {f : Mᵢ-⇒ X Y} where

  private
    module FE-XY (x : I X) (k : I Y) =
      FE {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = Y} x k

  ∘ᵢ-identityˡ : Mᵢ-≈ (idᵢ ∘ᵢ f) f
  ∘ᵢ-identityˡ x = refl , FE-XY.≈sr-refl x _

  ∘ᵢ-identityʳ : Mᵢ-≈ (f ∘ᵢ idᵢ) f
  ∘ᵢ-identityʳ x = refl , FE-XY.≈sr-refl x _

module _ {i a b} {X : Mᵢ-Obj i a b} where

  -- idX has a rigid monomorphic type Mᵢ-⇒ X X, anchoring Mᵢ-≈'s
  -- implicit object/levels that bare polymorphic idᵢ cannot provide
  --
  -- idX 具有刚性单态类型 Mᵢ-⇒ X X，为 Mᵢ-≈ 的隐式对象/层级提供裸多态
  -- idᵢ 所不能提供的锚点
  private
    idX : Mᵢ-⇒ X X
    idX = idᵢ

    module FE-XX (x : I X) (k : I X) =
      FE {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = X} x k

  ∘ᵢ-identity² : Mᵢ-≈ (idX ∘ᵢ idX) idX
  ∘ᵢ-identity² x = refl , FE-XX.≈sr-refl x _

------------------------------------------------------------------------
-- Same-universe monomorphic aliases (pin every level up front)
--
-- 同宇宙单态别名（预先钉死每个层级）
private
  Hom : (i a b : Level)
      → Mᵢ-Obj i a b → Mᵢ-Obj i a b → Set (i ⊔ a ⊔ b)
  Hom i a b X Y =
    Mᵢ-⇒ {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} X Y

  Eq : (i a b : Level) {X Y : Mᵢ-Obj i a b}
     → Hom i a b X Y → Hom i a b X Y → Set (i ⊔ a ⊔ b)
  Eq i a b {X = X} {Y = Y} f g =
    Mᵢ-≈ {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = Y} f g

  id₀ : (i a b : Level) {X : Mᵢ-Obj i a b} → Hom i a b X X
  id₀ i a b {X = X} = idᵢ {i = i} {a = a} {b = b} {X = X}

  comp₀ : (i a b : Level) {X Y Z : Mᵢ-Obj i a b}
        → Hom i a b Y Z → Hom i a b X Y → Hom i a b X Z
  comp₀ i a b {X = X} {Y = Y} {Z = Z} g f =
    _∘ᵢ_ {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b}
         {i₃ = i} {a₃ = a} {b₃ = b}
         {X = X} {Y = Y} {Z = Z} g f

------------------------------------------------------------------------
-- The Mᵢ category instance
--
-- Mᵢ 范畴实例
MᵢCat : (i a b : Level) → Category (lsuc (i ⊔ a ⊔ b)) (i ⊔ a ⊔ b) (i ⊔ a ⊔ b)
MᵢCat i a b = record
  { Obj       = Mᵢ-Obj i a b
  ; _⇒_       = Hom i a b
  ; _≈_       = Eq i a b
  ; id        = id₀ i a b
  ; _∘_       = comp₀ i a b
  ; equiv     = λ {X} {Y} →
                  Mᵢ-≈-isEquivalence
                    {i₁ = i} {a₁ = a} {b₁ = b}
                    {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = Y}
  ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} eqG eqF →
                  ∘ᵢ-resp-≈
                    {i₁ = i} {a₁ = a} {b₁ = b}
                    {i₂ = i} {a₂ = a} {b₂ = b}
                    {i₃ = i} {a₃ = a} {b₃ = b}
                    {X = X} {Y = Y} {Z = Z}
                    {F₁ = g} {F₂ = k} {G₁ = f} {G₂ = h} eqG eqF
  ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  ∘ᵢ-assoc {i = i} {a = a} {b = b}
                            {W = W} {X = X} {Y = Y} {Z = Z}
                            {f = f} {g = g} {h = h}
  ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  ∘ᵢ-sym-assoc {i = i} {a = a} {b = b}
                                {W = W} {X = X} {Y = Y} {Z = Z}
                                {f = f} {g = g} {h = h}
  ; identityˡ = λ {X} {Y} {f} →
                  ∘ᵢ-identityˡ {i = i} {a = a} {b = b}
                                {X = X} {Y = Y} {f = f}
  ; identityʳ = λ {X} {Y} {f} →
                  ∘ᵢ-identityʳ {i = i} {a = a} {b = b}
                                {X = X} {Y = Y} {f = f}
  ; identity² = λ {X} →
                  ∘ᵢ-identity² {i = i} {a = a} {b = b} {X = X}
  }

------------------------------------------------------------------------
-- The ordinary container category as the trivial specialisation I = ⊤
-- Parameters named S / P avoid clashing with the projections A / B
--
-- 普通容器范畴，即 I = ⊤ 的平凡特化。参数命名 S / P，避免与投影 A / B
-- 撞名
module Container-Specialization (i a b : Level) where

  trivial-Mᵢ : (S : Set a) → (S → Set b) → Mᵢ-Obj i a b
  trivial-Mᵢ S P = record
    { I    = ⊤ {i}
    ; A    = λ _ → S
    ; B    = λ _ s → P s
    ; next = λ _ _ _ → tt {i}
    ; root = tt {i}
    }

  ContObj : Set (lsuc (a ⊔ b))
  ContObj = Σ (Set a) (λ S → S → Set b)

  Cont⇒ : (X Y : ContObj) → Set (i ⊔ a ⊔ b)
  Cont⇒ X Y =
    let SX = proj₁ X ; PX = proj₂ X
        SY = proj₁ Y ; PY = proj₂ Y
    in Mᵢ-⇒ (trivial-Mᵢ SX PX) (trivial-Mᵢ SY PY)

  Cont-≈ : {X Y : ContObj} → Cont⇒ X Y → Cont⇒ X Y → Set (i ⊔ a ⊔ b)
  Cont-≈ {X = X} {Y = Y} f g = Mᵢ-≈ f g

  ContCat : Category (lsuc (i ⊔ a ⊔ b)) (i ⊔ a ⊔ b) (i ⊔ a ⊔ b)
  ContCat = MᵢCat i a b

------------------------------------------------------------------------
-- The container final coalgebra at I = ⊤ (polymorphic index level)
--
-- I = ⊤ 处的容器终余代数（索引层级多态）
module _ {i a b : Level} (S : Set a) (P : S → Set b) where
  open Container-Specialization i a b

  ContainerCoalg : Set (a ⊔ b)
  ContainerCoalg =
    Mᵢ {I = ⊤ {i}} (λ _ → S) (λ _ s → P s)
                    (λ _ _ _ → tt {i}) (tt {i})

  out : ContainerCoalg → Σ S (λ s → P s → ContainerCoalg)
  out c = fst c , λ q → snd c q

  ana : ∀ {c} {X : Set c}
      → (X → Σ S (λ s → P s → X)) → X → ContainerCoalg
  ana γ x .fst = proj₁ (γ x)
  ana γ x .snd q = ana γ (proj₂ (γ x) q)
