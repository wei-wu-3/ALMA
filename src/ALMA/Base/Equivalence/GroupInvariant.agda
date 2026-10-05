------------------------------------------------------------------------
-- transformation invariance under a group action
-- Mathematics: a group G acts on X via act, and act is compatible
-- with the evolution step (act-id, act-comp). The five group axioms
-- then yield two-sided transformation invariance of ScaleInvariant
-- under the action. GI-inverse consumes invʳ and idˡ; GI-inverseˡ consumes
-- invˡ and idˡ. The forward and dual invariance directions (GI-invariant,
-- GI-invariantˡ) use only act-comp. The round trips close the loop via
-- the two inverse-action lemmas
-- Form: this is ScaleInvariant at Obs = G, step = act. The relation
-- is an equivalence relation, inherited from the coinductive shape of
-- ScaleInvariant at the trivial layer
--
-- 群作用下的变换不变性
-- 数学内容：群 G 经 act 作用于 X，且 act 与演化 step 相容
-- （act-id、act-comp）。五条群公理于是给出 ScaleInvariant 在作用下的
-- 双向变换不变性。GI-inverse 消费 invʳ 和 idˡ，GI-inverseˡ 消费 invˡ 和 idˡ；
-- 往返经两条逆作用引理闭合回路
-- 形式：这是 Obs = G、step = act 处的 ScaleInvariant。该关系是
-- 等价关系，继承自 ScaleInvariant 在平凡层处的余归纳形状
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.GroupInvariant where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality.Core using (subst₂; cong; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (_×_; _,_)

open import ALMA.Base.IndexedMType using (fst; snd)
open import ALMA.Base.Equivalence.ScaleInvariant using (ScaleInvariant)

------------------------------------------------------------------------
-- A minimal group record carrying the five axioms used below
--
-- 最小群记录，携带下面使用的五条公理
record GroupStructure {g} (G : Set g) : Set g where
  infixl 6 _·_
  field
    _·_   : G → G → G
    e     : G
    _⁻¹   : G → G
    assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
    idˡ   : ∀ a → e · a ≡ a
    idʳ   : ∀ a → a · e ≡ a
    invˡ  : ∀ a → (a ⁻¹) · a ≡ e
    invʳ  : ∀ a → a · (a ⁻¹) ≡ e

module GroupAction
    {a g} {X : Set a} {G : Set g}
    (𝔾 : GroupStructure G)
    (act : X → G → X)
    (act-id   : ∀ x → act x (GroupStructure.e 𝔾) ≡ x)
    (act-comp : ∀ x (g h : G) →
                  act (act x g) h ≡ act x (GroupStructure._·_ 𝔾 g h))
  where

  open GroupStructure 𝔾

  -- GroupInvariant is ScaleInvariant at Obs = G, step = act
  -- The universe is Set g (not Set (a ⊔ g)): ScaleInvariant's
  -- universe does not depend on the universe of the state type X
  --
  -- GroupInvariant 是 Obs = G、step = act 处的 ScaleInvariant
  -- universe 是 Set g（而非 Set (a ⊔ g)）：ScaleInvariant 的 universe
  -- 不依赖状态类型 X 的 universe
  GroupInvariant : X → X → Set g
  GroupInvariant = ScaleInvariant act

  -- The four group lemmas below split into two dual pairs: the first
  -- pair consumes invʳ and idˡ, the second invˡ and idʳ
  --
  -- 下面四条群论引理分为两对对偶：第一对消费 invʳ 与 idˡ，
  -- 第二对消费 invˡ 与 idʳ
  g·g⁻¹·h≡h : ∀ (g h : G) → g · ((g ⁻¹) · h) ≡ h
  g·g⁻¹·h≡h g h = begin
    g · ((g ⁻¹) · h)
      ≡˘⟨ assoc g (g ⁻¹) h ⟩
    (g · (g ⁻¹)) · h
      ≡⟨ cong (_· h) (invʳ g) ⟩
    e · h
      ≡⟨ idˡ h ⟩
    h
    ∎

  g⁻¹·g·h≡h : ∀ (g h : G) → (g ⁻¹) · (g · h) ≡ h
  g⁻¹·g·h≡h g h = begin
    (g ⁻¹) · (g · h)
      ≡˘⟨ assoc (g ⁻¹) g h ⟩
    ((g ⁻¹) · g) · h
      ≡⟨ cong (_· h) (invˡ g) ⟩
    e · h
      ≡⟨ idˡ h ⟩
    h
    ∎

  g·h·h⁻¹≡g : ∀ (g h : G) → (g · h) · (h ⁻¹) ≡ g
  g·h·h⁻¹≡g g h = begin
    (g · h) · (h ⁻¹)
      ≡⟨ assoc g h (h ⁻¹) ⟩
    g · (h · (h ⁻¹))
      ≡⟨ cong (g ·_) (invʳ h) ⟩
    g · e
      ≡⟨ idʳ g ⟩
    g
    ∎

  g·h⁻¹·h≡g : ∀ (g h : G) → (g · (h ⁻¹)) · h ≡ g
  g·h⁻¹·h≡g g h = begin
    (g · (h ⁻¹)) · h
      ≡⟨ assoc g (h ⁻¹) h ⟩
    g · ((h ⁻¹) · h)
      ≡⟨ cong (g ·_) (invˡ h) ⟩
    g · e
      ≡⟨ idʳ g ⟩
    g
    ∎

  -- The two inverse-action lemmas are the dual pair act-inverseʳ /
  -- act-inverseˡ, consuming invʳ / invˡ respectively
  --
  -- 两条逆作用引理是对偶对 act-inverseʳ / act-inverseˡ，
  -- 分别消费 invʳ / invˡ
  act-inverseʳ : ∀ x (g : G) → act (act x g) (g ⁻¹) ≡ x
  act-inverseʳ x g = begin
    act (act x g) (g ⁻¹)
      ≡⟨ act-comp x g (g ⁻¹) ⟩
    act x (g · (g ⁻¹))
      ≡⟨ cong (act x) (invʳ g) ⟩
    act x e
      ≡⟨ act-id x ⟩
    x
    ∎

  act-inverseˡ : ∀ x (g : G) → act (act x (g ⁻¹)) g ≡ x
  act-inverseˡ x g = begin
    act (act x (g ⁻¹)) g
      ≡⟨ act-comp x (g ⁻¹) g ⟩
    act x ((g ⁻¹) · g)
      ≡⟨ cong (act x) (invˡ g) ⟩
    act x e
      ≡⟨ act-id x ⟩
    x
    ∎

  -- Invariance, forward and dual. The forward direction rewrites the
  -- composite action via act-comp and recurses; the dual direction is
  -- its mirror at g⁻¹
  --
  -- 不变性，正向与对偶。正向经 act-comp 重写复合作用并递归；
  -- 对偶方向是它在 g⁻¹ 处的镜像
  GI-invariant : ∀ {x y} (g : G)
               → GroupInvariant x y → GroupInvariant (act x g) (act y g)
  GI-invariant {x} {y} g p .fst = tt
  GI-invariant {x} {y} g p .snd h
    rewrite act-comp x g h | act-comp y g h =
    p .snd (g · h)

  GI-invariantˡ : ∀ {x y} (g : G)
                → GroupInvariant x y
                → GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹))
  GI-invariantˡ {x} {y} g p .fst = tt
  GI-invariantˡ {x} {y} g p .snd h
    rewrite act-comp x (g ⁻¹) h | act-comp y (g ⁻¹) h =
    p .snd ((g ⁻¹) · h)

  -- Inverses, forward and dual. Each picks a mid observation and
  -- transports the recursive call along the corresponding group lemma
  --
  -- 逆，正向与对偶。各取一个中间观察，并沿对应的群论引理传输递归调用
  GI-inverse : ∀ {x y} (g : G)
             → GroupInvariant (act x g) (act y g) → GroupInvariant x y
  GI-inverse {x} {y} g p .fst = tt
  GI-inverse {x} {y} g p .snd h =
    subst₂ GroupInvariant left-eq right-eq (p .snd k)
    where
      k : G
      k = (g ⁻¹) · h

      left-eq : act (act x g) k ≡ act x h
      left-eq = trans (act-comp x g k) (cong (act x) (g·g⁻¹·h≡h g h))

      right-eq : act (act y g) k ≡ act y h
      right-eq = trans (act-comp y g k) (cong (act y) (g·g⁻¹·h≡h g h))

  GI-inverseˡ : ∀ {x y} (g : G)
              → GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹))
              → GroupInvariant x y
  GI-inverseˡ {x} {y} g p .fst = tt
  GI-inverseˡ {x} {y} g p .snd h =
    subst₂ GroupInvariant left-eq right-eq (p .snd k)
    where
      k : G
      k = g · h

      left-eq : act (act x (g ⁻¹)) k ≡ act x h
      left-eq = trans (act-comp x (g ⁻¹) k) (cong (act x) (g⁻¹·g·h≡h g h))

      right-eq : act (act y (g ⁻¹)) k ≡ act y h
      right-eq = trans (act-comp y (g ⁻¹) k) (cong (act y) (g⁻¹·g·h≡h g h))

  -- Round trips: compose the two invariance directions and rewrite
  -- the endpoints back via the corresponding inverse-action lemma
  --
  -- 往返：复合两个不变性方向，并经对应的逆作用引理把端点重写回原处
  GI-roundtrip : ∀ {x y} (g : G)
               → GroupInvariant x y → GroupInvariant x y
  GI-roundtrip {x} {y} g p =
    subst₂ GroupInvariant
      (act-inverseʳ x g)
      (act-inverseʳ y g)
      (GI-invariantˡ g (GI-invariant g p))

  GI-roundtripˡ : ∀ {x y} (g : G)
                → GroupInvariant x y → GroupInvariant x y
  GI-roundtripˡ {x} {y} g p =
    subst₂ GroupInvariant
      (act-inverseˡ x g)
      (act-inverseˡ y g)
      (GI-invariant g (GI-invariantˡ g p))

  -- Bundled two-sided invariance
  --
  -- 打包的双向不变性
  GI-iff : ∀ {x y} (g : G)
         → ( GroupInvariant x y
             → GroupInvariant (act x g) (act y g) )
         × ( GroupInvariant (act x g) (act y g)
             → GroupInvariant x y )
         × ( GroupInvariant x y
             → GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹)) )
         × ( GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹))
             → GroupInvariant x y )
         × ( GroupInvariant x y → GroupInvariant x y )
         × ( GroupInvariant x y → GroupInvariant x y )
  GI-iff g = GI-invariant g , GI-inverse g
           , GI-invariantˡ g , GI-inverseˡ g
           , GI-roundtrip g , GI-roundtripˡ g

open GroupAction public
