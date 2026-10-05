------------------------------------------------------------------------
-- Subst-free indexed M-type and carried functional correspondences.
--
-- This module replaces the (B , next) presentation of indexed M-types
-- by an EDGE-FAMILY presentation in which every edge is indexed
-- directly by its child node:
--
--   E : (x : I) (a : A x) (y : I) → Set
--
-- reads as "edges E x a y lead from a node of shape a at x to a child
-- node at y". There is no `next` function and therefore no transition
-- commutation equation (the old next-comm): the child index is part of
-- the edge's type, not a value that two morphisms have to prove equal.
--
-- A morphism is a CARRIED one-step functional correspondence:
--   * R x y            an index-layer correspondence (NOT an equality;
--                      in a bare Set-enriched world it can be the graph
--                      of a function u, in general it is any relator)
--   * shapeᴿ : A x → C y           the observation map
--   * pull             for every target edge out of the image node,
--                      return (source child index, source edge, child
--                      index correspondence) as DATA.
--
-- The induced tree action mapR is defined by guarded copatterns. At
-- every child the target index y is already carried by the returned
-- correspondence r', so the recursive call has exactly the required
-- type: no equality is stated and nothing is transported by J/subst.
--
-- 零 subst 的索引 M 型与携带式功能对应。
--
-- 本模块用“边族”表示取代索引 M 型的 (B , next) 表示：每条边直接按其
-- 子节点索引化：
--
--   E : (x : I) (a : A x) (y : I) → Set
--
-- 读作“边 E x a y 从 x 处形状为 a 的节点引向 y 处的子节点”。这里没有
-- `next` 函数，因此也就没有转移交换等式（旧的 next-comm）：子索引是边
-- 类型的一部分，而不是两个态射需要去证明相等的值。
--
-- 态射是“携带的一步功能对应”：
--   * R x y            索引层对应（不是等式；在裸 Set 富集世界里可取函数
--                      u 的图，一般情形可为任意 relator）
--   * shapeᴿ : A x → C y           观测映射
--   * pull             对像节点的每条目标边，以数据形式返回（源子索引、
--                      源边、子索引对应）。
--
-- 诱导的树作用 mapR 用 guarded copattern 定义。每个子节点处，目标索引
-- y 已由返回的对应 r' 携带，因此递归调用恰好具有所需类型：不陈述任何
-- 等式，也没有任何 J/subst 传输。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Base.MCorr where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Base using (id; _∘_)
open import Categories.Category.Core using (Category)

------------------------------------------------------------------------
-- Edge-family indexed M-type (no next, no equality)
--
-- 边族索引 M 型（无 next、无等式）
------------------------------------------------------------------------
record M {i a b : Level} {I : Set i}
         (A : I → Set a)
         (E : (x : I) (a : A x) (y : I) → Set b)
         (x : I) : Set (i ⊔ a ⊔ b) where
  coinductive
  field
    -- Observation at the node.
    --
    -- 节点处的观测。
    here  : A x
    -- Children, indexed directly by the child index y and the edge e
    -- leading to y.
    --
    -- 子节点，直接按子索引 y 与引向 y 的边 e 索引化。
    below : (y : I) (e : E x here y) → M A E y
open M public

------------------------------------------------------------------------
-- Fibre-wise adjunction: the symmetry primitive.
--
-- Between two HOMOGENEOUS edge sets P (target) and R (source), an
-- adjunction carries both directions together with the two round-trip
-- laws. The round-trips live inside one fixed fibre, so they are
-- homogeneous propositional equalities with NO transport.
--   to   : source → target  (posL, the embedding / push)
--   fro  : target → source  (posR, the projection / pull)
--   η    : fro (to r) ≡ r   (unit)
--   ε    : to (fro p) ≡ p   (counit)
-- Symmetry just swaps the two sides (η ↔ ε): no path inversion, no J.
--
-- 纤维伴随：对称原语。
-- 在两个同质边集 P（目标）与 R（源）之间，伴随同时携带两个方向与两条
-- 往返律。往返律位于同一固定纤维内，故为同质命题等式，不含任何传输。
--   to   : 源 → 目标（posL，嵌入 / push）
--   fro  : 目标 → 源（posR，投影 / pull）
--   η    : fro (to r) ≡ r  （unit）
--   ε    : to (fro p) ≡ p  （counit）
-- 对称只需交换两侧（η ↔ ε）：无路径反转、无 J。
------------------------------------------------------------------------
record FiberAdj {ℓp ℓr : Level} (P : Set ℓp) (R : Set ℓr)
       : Set (ℓp ⊔ ℓr) where
  field
    to : R → P
    fro : P → R
    η   : (r : R) → fro (to r) ≡ r
    ε   : (p : P) → to (fro p) ≡ p

  -- The inverse adjunction (the symmetry of the fibre correspondence).
  --
  -- 逆伴随（纤维对应的对称）。
  symAdj : FiberAdj R P
  symAdj = record { to = fro ; fro = to ; η = ε ; ε = η }
open FiberAdj public

------------------------------------------------------------------------
-- Fibre adjunction combinators: identity and composition.
-- idAdj: to = fro = id, η = ε = refl on an independent edge variable
-- (J without K). compAdj stacks two adjunctions; the round-trips use
-- the components' homogeneous η / ε, with no dependent transport.
--
-- 纤维伴随组合子：恒等与复合。idAdj 的 to = fro = id、η = ε = refl，
-- refl 作用于独立边变量（J，无需 K）。compAdj 叠加两个伴随，往返律
-- 用各分量的同质 η / ε，无依赖传输。
------------------------------------------------------------------------
idAdj : ∀ {ℓ : Level} (P : Set ℓ) → FiberAdj P P
idAdj P = record { to = id ; fro = id ; η = λ _ → refl ; ε = λ _ → refl }

------------------------------------------------------------------------
-- Coinductive bisimulation at the SAME index, carried style.
--
-- The label correspondence here-eq is CARRIED, never eliminated. At
-- each child y the witness carries BOTH directions as data:
--   a FiberAdj between the two edge fibres, together with
--   fwd : t-edge → bisimulation of the t-child and the s-child,
--   bwd : s-edge → bisimulation of the s-child and the t-child.
-- Because both directions are carried, symmetry is a purely structural
-- swap (no recursive call, no edge cast) and transitivity composes the
-- adjunctions. There is NO cast / subst anywhere; the only refl is in
-- idAdj, on independently bound edge variables (J without K).
--
-- 同一索引处的余归纳互模拟（携带式）。
-- 标签对应 here-eq 只携带、不消去。每个子节点 y 上，见证把两个方向
-- 都作为数据携带：两边纤维间的 FiberAdj，以及
--   fwd：t 边 → t 子树与 s 子树的互模拟，
--   bwd：s 边 → s 子树与 t 子树的互模拟。
-- 因两个方向都被携带，对称只是纯结构交换（无递归调用、无边转换），
-- 传递复合伴随即可。全程无 cast / subst；唯一的 refl 在 idAdj 中，
-- 作用于独立绑定的边变量（J，无需 K）。
------------------------------------------------------------------------
record _≈M_ {i a b : Level} {I : Set i} {A : I → Set a}
            {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
            (t s : M A E x) : Set (i ⊔ a ⊔ b) where
  coinductive
  field
    here-eq : here t ≡ here s
    below-eq : ∀ (y : I)
      → Σ (FiberAdj (E x (here s) y) (E x (here t) y)) λ adj
      →   (∀ (e₁ : E x (here t) y)
           → (below t y e₁) ≈M (below s y (FiberAdj.to adj e₁)))
        × (∀ (e₂ : E x (here s) y)
           → (below s y e₂) ≈M (below t y (FiberAdj.fro adj e₂)))
open _≈M_

≈M-refl : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
            {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
            (t : M A E x) → t ≈M t
≈M-refl t .here-eq = refl
≈M-refl {E = E} {x = x} t .below-eq y =
    idAdj (E x (here t) y)
  , ( (λ e₁ → ≈M-refl (below t y e₁))
    , (λ e₂ → ≈M-refl (below t y e₂)) )

-- Children along two HOMOGENEOUSLY equal edges (same fibre) are
-- bisimilar: J on the independently bound edge equation, reflexivity at
-- refl. The equation lives inside one fixed edge fibre (no dependent
-- transport, no K).
--
-- 沿两条同质相等的边（同一纤维）所得子树互模拟：对独立绑定的边等式做
-- J，refl 处即自反。等式位于同一固定边纤维内（无依赖传输、无需 K）。
edge-≈ : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
           {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
           (u : M A E x) {e e' : E x (here u) y}
       → e ≡ e' → below u y e ≈M below u y e'
edge-≈ u {e = z} {e' = .z} refl = ≈M-refl (below u _ z)

-- Composition of fibre adjunctions; the round-trips use the two
-- components' η / ε (homogeneous equations, no transport).
--
-- 纤维伴随的复合；往返律由两个分量的 η / ε 拼成（同质等式，无传输）。
compAdj : ∀ {ℓr ℓg ℓh : Level}
          (R : Set ℓr) (G : Set ℓg) (H : Set ℓh)
        → FiberAdj G R → FiberAdj H G → FiberAdj H R
compAdj R G H a₁ a₂ = record
  { to  = FiberAdj.to a₂ ∘ FiberAdj.to a₁
  ; fro = FiberAdj.fro a₁ ∘ FiberAdj.fro a₂
  ; η = λ r → trans (cong (FiberAdj.fro a₁)
                         (FiberAdj.η a₂ (FiberAdj.to a₁ r)))
                   (FiberAdj.η a₁ r)
  ; ε = λ p → trans (cong (FiberAdj.to a₂)
                         (FiberAdj.ε a₁ (FiberAdj.fro a₂ p)))
                   (FiberAdj.ε a₂ p)
  }


-- Transitivity: compose the carried adjunctions; each component is a
-- bare corecursive call directly under the coinductive field.
--
-- 传递性：复合携带的伴随；每个分量都是余归纳字段下直接的裸递归调用。
≈M-trans : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
             {t g h : M A E x}
         → t ≈M g → g ≈M h → t ≈M h
≈M-trans {E = E} {x = x} {t = t} {g = g} {h = h} p q .here-eq =
  trans (here-eq p) (here-eq q)
≈M-trans {E = E} {x = x} {t = t} {g = g} {h = h} p q .below-eq y
  with p .below-eq y | q .below-eq y
... | adj₁ , (fwd₁ , bwd₁) | adj₂ , (fwd₂ , bwd₂) =
    compAdj (E x (here t) y) (E x (here g) y) (E x (here h) y) adj₁ adj₂
  , ( (λ e₁ → ≈M-trans (fwd₁ e₁) (fwd₂ (FiberAdj.to adj₁ e₁)))
    , (λ e₃ → ≈M-trans (bwd₂ e₃) (bwd₁ (FiberAdj.fro adj₂ e₃))) )

-- Symmetry: swap the adjunction (symAdj) and exchange fwd / bwd.
-- No recursive call and no edge cast.
--
-- 对称性：交换伴随（symAdj）并互换 fwd / bwd。无递归调用、无边转换。
≈M-sym : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
           {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
           {t s : M A E x}
       → t ≈M s → s ≈M t
≈M-sym {E = E} {x = x} {t = t} {s = s} p .here-eq = sym (here-eq p)
≈M-sym {E = E} {x = x} {t = t} {s = s} p .below-eq y
  with p .below-eq y
... | adj , (fwd , bwd) = symAdj adj , (bwd , fwd)

------------------------------------------------------------------------
-- One-step functional correspondence over an index layer R.
--
-- A value of Step at r : R x y explains how a single source node at x
-- maps to a single target node at y WITHOUT any equation:
--   shapeᴿ maps the source observation to the target observation;
--   pull maps a target edge (v , q) back to a source edge, and carries
--   the child correspondence r' : R x' v that locates the source child
--   inside the target child index.
--
-- 索引层 R 上的一步功能对应。
-- r : R x y 处的 Step 值以“无等式”的方式说明 x 处单个源节点如何映到
-- y 处单个目标节点：shapeᴿ 把源观测映为目标观测；pull 把一条目标边
-- (v , q) 拉回为一条源边，并携带子对应 r' : R x' v，用它把源子节点
-- 定位到目标子索引内。
------------------------------------------------------------------------
record Step {i j a b c d ℓr : Level}
            {I : Set i} {J : Set j}
            (R : I → J → Set ℓr)
            (A : I → Set a)
            (E : (x : I) (a : A x) (y : I) → Set b)
            (C : J → Set c)
            (D : (y : J) (q : C y) (v : J) → Set d)
            {x : I} {y : J} (r : R x y)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr) where
  field
    -- Observation map (the coinductive `here`).
    --
    -- 观测映射（余归纳的 here）。
    shapeᴿ : A x → C y
    -- Canonical source child of a target child v. It is EDGE-INDEPENDENT
    -- (depends only on a and v, not on the edge label q) and carries the
    -- correspondence r' : R x' v that locates the source child. This is
    -- carried function data, not an equation to prove, and it is what
    -- lets a whole-fibre adjunction below be stated at fixed v.
    --
    -- 目标子节点 v 的规范源子节点。它与边无关（只依赖 a 与 v，不依赖边
    -- 标签 q），并携带定位源子节点的对应 r' : R x' v。这是携带的函数
    -- 数据而非待证等式，也使下面的整纤维伴随能在固定 v 上陈述。
    child : (a : A x) (v : J) → Σ I λ x' → R x' v
    -- Whole-fibre adjunction at the canonical child, between the target
    -- edge fibre D y (shapeᴿ a) v and the source edge fibre E x a x'.
    -- Carried as data (to / fro + homogeneous η / ε); fro is the edge
    -- pullback and to its inverse. This is the structure that lets two
    -- bisimilar source trees map to bisimilar target trees with no J
    -- along the label equation.
    --
    -- 规范子节点上的整纤维伴随，位于目标边纤维 D y (shapeᴿ a) v 与源
    -- 边纤维 E x a x' 之间。作为数据携带（to / fro 加同质 η / ε）：fro
    -- 是边拉回、to 是其逆。有了它，两棵互模拟源树映为互模拟目标树，
    -- 无需沿标签等式做 J。
    edge-adj : (a : A x) (v : J)
             → FiberAdj (D y (shapeᴿ a) v)
                        (E x a (proj₁ (child a v)))

  -- Edge pullback DERIVED from the canonical child and the adjunction:
  -- x' and r' come from child (edge-independent), the source edge is the
  -- adjunction's fro. Everything needed to continue is carried.
  --
  -- 边拉回由规范子节点与伴随派生：x' 与 r' 来自 child（与边无关），源
  -- 边是伴随的 fro。继续所需的一切都是携带的。
  pull : (a : A x) (v : J) (q : D y (shapeᴿ a) v)
       → Σ I λ x' → Σ (E x a x') λ e → R x' v
  pull a v q =
    let x' , r' = child a v
    in x' , FiberAdj.fro (edge-adj a v) q , r'
open Step public

------------------------------------------------------------------------
-- A morphism is an index layer R together with a one-step Step at
-- every related pair. The tree action mapR is then total and subst-free.
--
-- 态射 = 索引层 R + 每个相关对上的一步 Step。树作用 mapR 因此是全的且
-- 零 subst。
------------------------------------------------------------------------
record Morph {i j a b c d ℓr : Level}
             {I : Set i} {J : Set j}
             (R : I → J → Set ℓr)
             (A : I → Set a)
             (E : (x : I) (a : A x) (y : I) → Set b)
             (C : J → Set c)
             (D : (y : J) (q : C y) (v : J) → Set d)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr) where
  field
    step : ∀ {x : I} {y : J} (r : R x y)
         → Step R A E C D r

  -- Subst-free tree action. At a target child (v , q), pull hands back
  -- the exact source child x', edge e and correspondence r' : R x' v;
  -- the recursive call mapR r' (...) therefore already lives at v.
  --
  -- 零 subst 树作用。在目标子节点 (v , q) 处，pull 直接交回确切的源子
  -- 节点 x'、边 e 与对应 r' : R x' v；故递归调用 mapR r' (...) 本就位
  -- 于 v，无需任何传输。
  mapR : ∀ {x : I} {y : J} → R x y → M A E x → M C D y
  -- Defined with `let` (not `with`) so the continuation unfolds
  -- DEFINITIONALLY: below (mapR r t) v q reduces to mapR r' (below t x' e)
  -- without with-abstraction, which keeps the coinductive setoid laws
  -- guarded without manual casts.
  --
  -- 用 `let`（非 `with`）定义，使连续化定义性展开：
  -- below (mapR r t) v q 直接归约为 mapR r' (below t x' e)，没有
  -- with 抽象，余归纳 setoid 定律因此可保持受保护而无需手工转换。
  mapR r t .here   = shapeᴿ (step r) (here t)
  mapR r t .below v q =
    let x' , e , r' = pull (step r) (here t) v q
    in mapR r' (below t x' e)
open Morph public

------------------------------------------------------------------------
-- Relational composition of index layers (no equality): a related
-- pair x ─R─ y ─S─ z is witnessed by an carried middle index y.
--
-- 索引层的关系复合（无等式）：相关对 x ─R─ y ─S─ z 由携带的中间索引 y
-- 见证。
------------------------------------------------------------------------
infixr 9 _⍮_
_⍮_ : ∀ {i j k ℓ₁ ℓ₂ : Level}
        {I : Set i} {J : Set j} {K : Set k}
      (R : I → J → Set ℓ₁) (S : J → K → Set ℓ₂)
    → I → K → Set (j ⊔ ℓ₁ ⊔ ℓ₂)
(R ⍮ S) x z = Σ _ λ y → Σ (R x y) λ _ → S y z

------------------------------------------------------------------------
-- Composition of carried correspondences. The target edge is first
-- pulled back through ψ to a middle edge, then through φ to a source
-- edge; the middle index and both correspondences are carried in the
-- composed witness. No equation is stated at any point.
--
-- 携带式对应的复合。目标边先经 ψ 拉回为中间边，再经 φ 拉回为源边；中
-- 间索引与两份对应都作为复合见证携带。全程不陈述任何等式。
------------------------------------------------------------------------
compM :
  ∀ {i j k a b c d e f ℓ₁ ℓ₂ : Level}
    {I : Set i} {J : Set j} {K : Set k}
    {A : I → Set a} {E : (x : I) (a : A x) (y : I) → Set b}
    {C : J → Set c} {D : (y : J) (q : C y) (v : J) → Set d}
    {G : K → Set e} {F : (z : K) (q : G z) (w : K) → Set f}
    {R : I → J → Set ℓ₁} {S : J → K → Set ℓ₂}
  → Morph R A E C D → Morph S C D G F
  → Morph (R ⍮ S) A E G F
compM {E = E} {D = D} {F = F} φ ψ .step {x = x} {y = z} (ym , r , s) =
  let φr = Morph.step φ r
      ψs = Morph.step ψ s
  in record
  { shapeᴿ = λ a → Step.shapeᴿ ψs (Step.shapeᴿ φr a)
  ; child = λ a w →
      let ym' , s' = Step.child ψs (Step.shapeᴿ φr a) w
          x' , r'  = Step.child φr a ym'
      in x' , (ym' , r' , s')
  ; edge-adj = λ a w →
      let ym' , s' = Step.child ψs (Step.shapeᴿ φr a) w
          x' , r'  = Step.child φr a ym'
      in compAdj (E x a x')
                 (D ym (Step.shapeᴿ φr a) ym')
                 (F z (Step.shapeᴿ ψs (Step.shapeᴿ φr a)) w)
                 (Step.edge-adj φr a ym')
                 (Step.edge-adj ψs (Step.shapeᴿ φr a) w)
  }

------------------------------------------------------------------------
-- FREE PATH-GROUPOID INSTANCE (the one place where equality appears).
--
-- When the index layer is chosen to be propositional equality
-- R x y = x ≡ y (the free path groupoid of a bare Set), the identity
-- correspondence is the identity morphism. Equality occurs ONLY here,
-- as the refl constructors of the index graph; the coinductive tree
-- action is still the subst-free mapR, which threads r opaquely and
-- never eliminates it by J. A fully equality-free identity is obtained
-- instead by equipping the indices with their own carried correspondence
-- category (id as data).
--
-- 自由路径广群实例（等式唯一出现之处）。
-- 当索引层取为命题等式 R x y = x ≡ y（裸 Set 的自由路径广群）时，恒等
-- 对应即恒等态射。等式仅在此处作为索引图的 refl 构造子出现；余归纳树作
-- 用仍是零 subst 的 mapR，它把 r 作为不透明数据传递、从不用 J 消去。若
-- 要完全无等式的恒等，应给索引配备自带的携带对应范畴（id 作为数据）。
------------------------------------------------------------------------
idM : ∀ {i a b : Level} {I : Set i}
        (A : I → Set a) (E : (x : I) (a : A x) (y : I) → Set b)
      → Morph (λ (x y : I) → x ≡ y) A E A E
idM A E .step {x = x} {y = .x} refl = record
  { shapeᴿ  = λ a → a
  ; child    = λ a v → v , refl
  ; edge-adj = λ a v → idAdj (E x a v)
  }

-- The identity correspondence's fibre adjunction along a node path
-- d : x₁ ≡ x₀, between the edge fibres over x₀ and x₁. This is the ONE
-- action of the index free path groupoid on edges: J on the independently
-- bound node path, and at refl the two fibres coincide (idAdj). It carries
-- both directions with homogeneous η / ε, so congruence never needs a
-- dependent subst across the shape / position layers.
--
-- 恒等对应沿节点路径 d : x₁ ≡ x₀ 的纤维伴随，位于 x₀ 与 x₁ 上的边纤维
-- 之间。这是索引自由路径广群在边上的唯一作用：对独立绑定的节点路径做
-- J，refl 处两纤维重合（idAdj）。它携带两个方向与同质 η / ε，故同余
-- 永不需要跨形状 / 位置层的依赖 subst。
idM-edge-adj : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 {x x₁ x₀ : I} (a : A x) (d : x₁ ≡ x₀)
             → FiberAdj (E x a x₀) (E x a x₁)
idM-edge-adj {E = E} {x₁ = z} {x₀ = .z} a refl = idAdj (E _ a z)

------------------------------------------------------------------------
-- Bundled edge-family system (an object of the eventual category).
--
-- 束装的边族系统（未来范畴的对象）。
------------------------------------------------------------------------
record Sys (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    I : Set i
    A : I → Set a
    E : (x : I) (a : A x) (y : I) → Set b
open Sys public

------------------------------------------------------------------------
-- DETERMINISTIC carried morphism at the free path-groupoid instance.
--
-- The index layer is the graph of a function u: R x v = u x ≡ v. The
-- ONLY propositional equality in the whole construction is the graph
-- witness u x' ≡ v inside pull (the old next-comm), a homogeneous
-- equation in J. Everything else is carried function data, and the tree
-- action is the subst-free generic mapR specialised at refl.
--
-- 自由路径广群实例上的确定性携带态射。
-- 索引层是函数 u 的图：R x v = u x ≡ v。整个构造中唯一的命题等式是
-- pull 内的图见证 u x' ≡ v（即旧的 next-comm），它是 J 中一条同质等
-- 式。其余全是携带的函数数据，树作用则是泛型零 subst 的 mapR 在 refl
-- 处的特化。
------------------------------------------------------------------------
record FMap {i j a b c d : Level}
            (X : Sys i a b) (Y : Sys j c d)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d) where
  field
    u     : I X → I Y
    shape : (x : I X) → A X x → A Y (u x)
    -- Canonical source child of a target child v: edge-INDEPENDENT (it
    -- depends only on x, a, v, not on the edge label q), together with
    -- the graph witness u x' ≡ v (the old next-comm, a homogeneous
    -- equation in I Y). This is what lets a whole-fibre FiberAdj be
    -- formed at fixed v without choosing x' per edge.
    --
    -- 目标子节点 v 的规范源子节点：与边无关（只依赖 x、a、v，不依赖边标
    -- 签 q），并携带图见证 u x' ≡ v（即旧的 next-comm，I Y 中的同质等
    -- 式）。正因如此，才能在固定 v 上形成整纤维 FiberAdj，而不必逐条边
    -- 选 x'。
    childF : (x : I X) (a : A X x) (v : I Y)
           → Σ (I X) λ x' → u x' ≡ v
    -- Whole-fibre adjunction at the canonical child of v, between the
    -- target edge fibre and the source edge fibre at proj₁ (childF x a v).
    -- This is the carried posL ⊣ posR: fro is the edge pullback, to its
    -- inverse, η / ε the homogeneous round-trips. It makes the tree
    -- action a bisimulation congruence with no J along the label equation.
    --
    -- v 的规范子节点上的整纤维伴随，位于目标边纤维与源边纤维
    -- proj₁ (childF x a v) 之间。它是携带的 posL ⊣ posR：fro 为边拉
    -- 回、to 为其逆、η / ε 为同质往返律。它使树作用成为互模拟同余，
    -- 无需沿标签等式做 J。
    adjF  : (x : I X) (a : A X x) (v : I Y)
          → FiberAdj (E Y (u x) (shape x a) v)
                     (E X x a (proj₁ (childF x a v)))
    -- Index-layer coherence: the canonical child INDEX is invariant under
    -- a label equation e : a ≡ a'. This is a HOMOGENEOUS equation in I X,
    -- of the same nature as the graph witness u x' ≡ v (the old next-comm):
    -- it lives at the index layer only. The dependent shape / edge fibres
    -- are never transported along it — they are always aligned by the
    -- carried FiberAdj. This is the single extra equation congruence
    -- needs, and it is carried as data rather than proved by dependent J.
    --
    -- 索引层相干性：规范子节点索引在标签等式 e : a ≡ a' 下不变。这是
    -- I X 中的同质等式，与图见证 u x' ≡ v（旧 next-comm）同类：只存在
    -- 于索引层。依赖的形状 / 边纤维绝不沿它传输，始终由携带的 FiberAdj
    -- 对齐。这是同余所需的唯一额外等式，作为数据携带，而非用依赖 J 证明。
    -- Index-layer coherence under a label equation e : a ≡ a'. It carries
    -- BOTH (d) the equation between the two canonical child indices and
    -- (w) the compatibility of the two graph witnesses along d:
    --   r₁ ≡ trans (cong u d) r₀,  where (x₀,r₀)=childF x a v and
    --                              (x₁,r₁)=childF x a' v.
    -- Both are homogeneous equations on the index graph (the free path
    -- groupoid); the dependent edge fibres are never transported by them.
    -- Carrying w is essential: without K one cannot identify two arbitrary
    -- same-endpoint paths, so the witness compatibility must be data.
    --
    -- 标签等式 e : a ≡ a' 下的索引层相干性。它同时携带 (d) 两个规范子
    -- 节点索引间的等式，与 (w) 两个图见证沿 d 的相容等式：
    --   r₁ ≡ trans (cong u d) r₀，其中 (x₀,r₀)=childF x a v、
    --                            (x₁,r₁)=childF x a' v。
    -- 两者都是索引图（自由路径广群）上的同质等式，依赖的边纤维绝不沿其
    -- 传输。必须携带 w：禁用 K 时不能判定任意两条同端点路径相等（那将
    -- 是 UIP），故见证相容性必须作为数据。
    childF-coh : (x : I X) {a a' : A X x} (e : a ≡ a') (v : I Y)
               → Σ (proj₁ (childF x a' v) ≡ proj₁ (childF x a v)) λ d
               → proj₂ (childF x a' v)
                 ≡ trans (cong u d) (proj₂ (childF x a v))

  -- Edge pullback DERIVED from the canonical child and the adjunction:
  -- x' and r' come from childF (edge-independent), the source edge is
  -- the adjunction's fro.
  --
  -- 边拉回由规范子节点与伴随派生：x' 与 r' 来自 childF（与边无关），源
  -- 边是伴随的 fro。
  pullF : (x : I X) (a : A X x) (v : I Y)
          (q : E Y (u x) (shape x a) v)
        → Σ (I X) λ x' → Σ (E X x a x') λ e → u x' ≡ v
  pullF x a v q =
    let x' , r' = childF x a v
    in x' , FiberAdj.fro (adjF x a v) q , r'

  -- The generic carried morphism at the graph of u (one J, at refl).
  --
  -- u 的图上的泛型携带态射（仅 refl 处一次 J）。
  asMorph : Morph (λ (x : I X) (v : I Y) → u x ≡ v)
                  (A X) (E X) (A Y) (E Y)
  asMorph .step {x = x} {y = .(u x)} refl = record
    { shapeᴿ  = shape x
    ; child    = childF x
    ; edge-adj = adjF x
    }

  -- Subst-free deterministic tree action.
  --
  -- 零 subst 确定性树作用。
  mapF : (x : I X) → M (A X) (E X) x → M (A Y) (E Y) (u x)
  mapF x t = mapR asMorph refl t
open FMap public

------------------------------------------------------------------------
-- Identity and composition of deterministic carried morphisms.
--
-- The graph witnesses are composed with homogeneous cong/trans only
-- (all equations live in the single index type I Z); there is no
-- dependent transport.
--
-- 确定性携带态射的恒等与复合。
-- 图见证仅用同质 cong/trans 复合（所有等式都在单一索引类型 I Z 中），
-- 无依赖传输。
------------------------------------------------------------------------
idF : ∀ {i a b : Level} (X : Sys i a b) → FMap X X
idF X = record
  { u          = id
  ; shape      = λ _ a → a
  ; childF     = λ x a v → v , refl
  ; adjF       = λ x a v → idAdj (E X x a v)
  ; childF-coh = λ x e v → refl , refl
  }

compF : ∀ {i j k a b c d e f : Level}
          {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e f}
      → FMap Y Z → FMap X Y → FMap X Z
compF {X = X} {Y = Y} {Z = Z} g f = record
  { u          = ug ∘ uf
  ; shape      = λ x a → shapeg (uf x) (shapef x a)
  ; childF     = childcomp
  ; adjF       = adjcomp
  ; childF-coh = cohcomp
  }
  where
    uf     = FMap.u f
    ug     = FMap.u g
    shapef = FMap.shape f
    shapeg = FMap.shape g

    -- Canonical composite child: g's child first (edge-independent),
    -- then f's child; only homogeneous graph witnesses are composed.
    --
    -- 规范复算子节点：先取 g 的（与边无关的）子节点，再取 f 的子节点；
    -- 只复合同质图见证。
    childcomp : (x : I X) (a : A X x) (w : I Z)
             → Σ (I X) λ x'' → ug (uf x'') ≡ w
    childcomp x a w =
      let y' , eg = FMap.childF g (uf x) (shapef x a) w
          x'' , ef = FMap.childF f x a y'
      in x'' , trans (cong ug ef) eg

    -- The composite fibre adjunction uses the SAME edge-independent
    -- canonical decomposition as childcomp: g's child y', then f's child
    -- x''. compAdj stacks f's then g's adjunction, so its fro is
    -- DEFINITIONALLY the two-stage edge pullback used by nested mapR;
    -- this is what makes fusion hold with idAdj. Round-trips are
    -- discharged by the components' homogeneous η / ε; no cast.
    --
    -- 复合纤维伴随采用与 childcomp 完全相同的、与边无关的规范分解：先 g
    -- 的子节点 y'，再 f 的子节点 x''。compAdj 叠 f 与 g 的伴随，其 fro
    -- 定义性等于嵌套 mapR 的两段边拉回，fusion 因而能用 idAdj 成立。
    -- 往返律由各分量同质 η / ε 自动解除，无转换。
    adjcomp : (x : I X) (a : A X x) (w : I Z)
            → FiberAdj (E Z (ug (uf x))
                           (shapeg (uf x) (shapef x a)) w)
                       (E X x a (proj₁ (childcomp x a w)))
    adjcomp x a w =
      let y' , _  = FMap.childF g (uf x) (shapef x a) w
          x'' , _ = FMap.childF f x a y'
      in compAdj (E X x a x'')
                 (E Y (uf x) (shapef x a) y')
                 (E Z (ug (uf x)) (shapeg (uf x) (shapef x a)) w)
                 (FMap.adjF f x a y')
                 (FMap.adjF g (uf x) (shapef x a) w)

    -- Composite child coherence. g's child moves only with the label
    -- equation (childF-coh g); f's child then moves with the target-child
    -- equation via plain homogeneous cong, and with the label equation via
    -- childF-coh f. Everything stays on the plain index types I Y / I X;
    -- no dependent fibre is ever transported.
    --
    -- 复算子节点相干性。g 的子节点只随标签等式移动（childF-coh g）；f 的
    -- 子节点再随目标子节点等式（纯同质 cong）与标签等式（childF-coh f）
    -- 移动。全程只在纯索引类型 I Y / I X 上，绝不传输依赖纤维。
    -- Composite child coherence. childcomp is itself a function of the
    -- label a, so J on the independently bound label equation e closes
    -- both the index equation and the witness compatibility at once: at
    -- refl the two childcomp outputs are the SAME term and both equations
    -- are refl. No path algebra on the components is needed, and no
    -- dependent fibre is transported.
    --
    -- 复算子节点相干性。childcomp 本身是标签 a 的函数，故对独立绑定的标
    -- 签等式 e 做 J，索引等式与见证相容性同时成立：refl 处两次 childcomp
    -- 输出是同一项，两条等式皆为 refl。无需在分量上做路径代数，也不传输
    -- 依赖纤维。
    cohcomp : (x : I X) {a a' : A X x} (e : a ≡ a') (w : I Z)
            → Σ (proj₁ (childcomp x a' w) ≡ proj₁ (childcomp x a w)) λ d
            → proj₂ (childcomp x a' w)
              ≡ trans (cong (ug ∘ uf) d) (proj₂ (childcomp x a w))
    cohcomp x {a = z} {a' = .z} refl w = refl , refl
------------------------------------------------------------------------
-- Subst-free relocation across an index equation.
--
-- Moving a tree from index x to y along r : x ≡ y is just the identity
-- correspondence idM applied by mapR: r is carried opaquely (the only J
-- is the refl clause inside idM). No term is transported by subst.
--
-- 沿索引等式的零 subst 重定位。
-- 沿 r : x ≡ y 把树从索引 x 移到 y，就是恒等对应 idM 经 mapR 作用：
-- r 作为不透明数据贯穿（唯一 J 是 idM 内的 refl 子句）。没有任何项被
-- subst 传输。
------------------------------------------------------------------------
relocate : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
         → x ≡ y → M A E x → M A E y
-- The refl case is the identity DEFINITIONALLY (not merely up to
-- bisimulation): this lets congruence engines unify
-- here (relocate refl s) with here s under arbitrary canonical-child
-- functions without inserting a transport. Non-refl paths are carried
-- opaquely through mapR idM.
--
-- refl 情形定义性地是恒等（而非仅互模拟意义下）：这使同余引擎能在任意
-- 规范子节点函数下把 here (relocate refl s) 与 here s 直接合一，无需插入
-- 传输。_≡_ 只有 refl 一个构造子，任意中性路径经 J 归约到该子句，故无需
-- 其它子句；非 refl 行为由调用处对独立路径做 J 得到。
relocate {A = A} {E = E} refl t = t

------------------------------------------------------------------------
-- Behavioural equivalence of deterministic carried morphisms.
--
-- At each source index x the witness carries the pointwise index graph
-- r : u f x ≡ u g x, and, after relocating f's image tree along r
-- (subst-free), a same-index bisimulation with g's image tree. For the
-- category laws the two u are definitionally equal, so r is refl and
-- relocation is the identity.
--
-- 确定性携带态射的行为等价。
-- 在每个源索引 x 上，见证携带逐点索引图 r : u f x ≡ u g x，并把 f 的
-- 输出树沿 r 零 subst 重定位后，与 g 的输出树给出同索引互模拟。范畴
-- 定律中两侧 u 定义性相等，故 r 为 refl、重定位恒等。
------------------------------------------------------------------------
_≈F_ : ∀ {i j a b c d : Level}
         {X : Sys i a b} {Y : Sys j c d}
       → FMap X Y → FMap X Y → Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d)
_≈F_ {X = X} {Y = Y} f g =
  ∀ (x : I X)
  → Σ (FMap.u f x ≡ FMap.u g x)
      (λ r → ∀ (t : M (A X) (E X) x)
            → relocate r (FMap.mapF f x t) ≈M FMap.mapF g x t)

------------------------------------------------------------------------
-- Relocation along refl is the identity, bisimulation-wise (both
-- directions). Mutual corecursion on the immediate subtrees; every
-- recursive call is bare under a coinductive field.
--
-- 沿 refl 重定位在互模拟意义下是恒等（双向）。在直接子树上互逆余归
-- 纳；每个递归调用都是余归纳字段下的裸调用。
------------------------------------------------------------------------
mutual
  ≈rel-refl : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
                (t : M A E x) → relocate refl t ≈M t
  ≈rel-refl {E = E} {x = x} t .here-eq = refl
  ≈rel-refl {E = E} {x = x} t .below-eq y =
      idAdj (E x (here t) y)
    , ( (λ e₁ → ≈rel-refl (below t y e₁))
      , (λ e₂ → ≈rel-refl˘ (below t y e₂)) )

  ≈rel-refl˘ : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
                 (t : M A E x) → t ≈M relocate refl t
  ≈rel-refl˘ {E = E} {x = x} t .here-eq = refl
  ≈rel-refl˘ {E = E} {x = x} t .below-eq y =
      idAdj (E x (here t) y)
    , ( (λ e₁ → ≈rel-refl˘ (below t y e₁))
      , (λ e₂ → ≈rel-refl (below t y e₂)) )

-- Reflexivity of behavioural equivalence of deterministic morphisms.
--
-- 确定性态射行为等价的自反性。
≈F-refl : ∀ {i j a b c d : Level}
            {X : Sys i a b} {Y : Sys j c d}
            (f : FMap X Y) → f ≈F f
≈F-refl f x = refl , λ t → ≈rel-refl (FMap.mapF f x t)

------------------------------------------------------------------------
-- Relocation is a groupoid action on trees up to bisimulation.
--
-- All three are J on independent index variables (refl patterns are
-- legal without K); at refl they reduce to the ≈rel-refl pair and the
-- already-proved ≈M-trans. No term is transported by subst.
--
-- 重定位在互模拟意义下是树上的广群作用。
-- 三者均对独立索引变量做 J（refl 模式无需 K）；refl 处退化为
-- ≈rel-refl 对与已证的 ≈M-trans。没有任何项被 subst 传输。
------------------------------------------------------------------------
-- Relocation preserves bisimulation.
--
-- 重定位保持互模拟。
≈rel-resp : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
              {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
              (r : x ≡ y) (t s : M A E x)
          → t ≈M s → relocate r t ≈M relocate r s
≈rel-resp refl t s p =
  ≈M-trans (≈rel-refl t) (≈M-trans p (≈rel-refl˘ s))

-- Round trip: relocate (sym r) after relocate r is the identity.
--
-- 往返：relocate (sym r) 接 relocate r 是恒等。
≈rel-round : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
               {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
               (r : x ≡ y) (t : M A E x)
           → relocate (sym r) (relocate r t) ≈M t
≈rel-round {x = x} {y = .x} refl t =
  ≈M-trans (≈rel-refl (relocate refl t)) (≈rel-refl t)

-- Composition: relocate (trans r s) is relocate s after relocate r.
--
-- 复合：relocate (trans r s) 等于 relocate r 后再 relocate s。
≈rel-comp : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
              {E : (x : I) (a : A x) (y : I) → Set b} {x y z : I}
              (r : x ≡ y) (s : y ≡ z) (t : M A E x)
          → relocate (trans r s) t ≈M relocate s (relocate r t)
≈rel-comp {x = x} {y = .x} {z = .x} refl refl t =
  ≈rel-refl˘ (relocate refl t)

-- Naturality of relocation with the immediate children: relocating a
-- child along d : x₁ ≡ x₀ yields, up to bisimulation, the parent's child
-- at the idM-edge-transported edge. J on the independently bound node
-- path d; at refl it is relocate-refl. Homogeneous index-groupoid action
-- only; no dependent fibre transport.
--
-- 重定位与直接子节点的自然性：沿 d : x₁ ≡ x₀ 重定位一个子节点，在互模拟
-- 意义下等于父节点在经 idM 边传输后的边上的子节点。对独立绑定的节点路
-- 径 d 做 J，refl 处即 relocate-refl。仅是同质索引广群作用，无依赖纤维
-- 传输。
rel-child-nat : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                  {E : (x : I) (a : A x) (y : I) → Set b}
                  {x x₁ x₀ : I}
                  (u : M A E x) (d : x₁ ≡ x₀)
                  (e0 : E x (here u) x₀)
              → relocate {E = E} d
                  (below u x₁ (FiberAdj.fro
                     (idM-edge-adj {E = E} {x = x} (here u) d) e0))
                ≈M below u x₀ e0
rel-child-nat {E = E} {x = x} {x₁ = z} {x₀ = .z} u refl e0 =
  ≈rel-refl (below u z e0)

-- Symmetry and transitivity of behavioural equivalence, obtained by
-- combining the groupoid-action lemmas with ≈M-sym / ≈M-trans.
--
-- 行为等价的对称与传递：广群作用引理结合 ≈M-sym / ≈M-trans 得到。
≈F-sym : ∀ {i j a b c d : Level}
           {X : Sys i a b} {Y : Sys j c d}
           {f g : FMap X Y}
       → f ≈F g → g ≈F f
≈F-sym {f = f} {g = g} p x
  with p x
... | r , h =
    sym r
  , λ t → let a = FMap.mapF f x t
              b = FMap.mapF g x t
          in ≈M-trans (≈rel-resp (sym r) b (relocate r a) (≈M-sym (h t)))
                      (≈rel-round r a)

≈F-trans : ∀ {i j a b c d : Level}
             {X : Sys i a b} {Y : Sys j c d}
             {f g h : FMap X Y}
         → f ≈F g → g ≈F h → f ≈F h
≈F-trans {f = f} {g = g} {h = h} p q x
  with p x | q x
... | r₁ , h₁ | r₂ , h₂ =
    trans r₁ r₂
  , λ t → let a = FMap.mapF f x t
              b = FMap.mapF g x t
          in ≈M-trans (≈rel-comp r₁ r₂ a)
                      (≈M-trans (≈rel-resp r₂ (relocate r₁ a) b (h₁ t))
                                (h₂ t))

------------------------------------------------------------------------
-- Behavioural equivalence is an equivalence relation on FMap.
--
-- 行为等价在 FMap 上构成等价关系。
------------------------------------------------------------------------
≈F-isEquivalence : ∀ {i j a b c d : Level}
                     {X : Sys i a b} {Y : Sys j c d}
                 → IsEquivalence (_≈F_ {X = X} {Y = Y})
≈F-isEquivalence = record
  { refl  = λ {f} → ≈F-refl f
  ; sym   = ≈F-sym
  ; trans = ≈F-trans
  }

------------------------------------------------------------------------
-- Coinductive fusion for mapR.
--
-- Mapping along the composed graph witness equals the nested mapping,
-- up to bisimulation:
--   mapR asC (trans (cong ug rf) rg) t  ≈M  mapR asG rg (mapR asF rf t)
-- J is on the two independent graph witnesses; at refl the two labels
-- agree and each child reduces, by nested-let pullback, to the fusion
-- lemma on the immediate subtree. Both directions are carried (mutual
-- fusion / fusion˘); no edge cast or dependent transport is introduced.
--
-- mapR 的余归纳融合。
-- 沿复合图见证作用与嵌套作用在互模拟意义下相等：
--   mapR asC (trans (cong ug rf) rg) t  ≈M  mapR asG rg (mapR asF rf t)
-- 对两个独立图见证做 J；refl 处两个标签一致，每个子节点经嵌套 let 拉
-- 回后归约为直接子树上的融合引理。两个方向都携带（互逆 fusion /
-- fusion˘），不引入边转换或依赖传输。
------------------------------------------------------------------------
module Fusion {i j k a b c d e fℓ : Level}
             {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e fℓ}
             (gm : FMap Y Z) (fm : FMap X Y) where

  uf  = FMap.u fm
  ug  = FMap.u gm
  asF = FMap.asMorph fm
  asG = FMap.asMorph gm
  asC = FMap.asMorph (compF gm fm)

  mutual
    fusion : ∀ {x : I X} {y : I Y} {z : I Z}
               (rf : uf x ≡ y) (rg : ug y ≡ z)
               (t : M (A X) (E X) x)
           → mapR asC (trans (cong ug rf) rg) t
             ≈M mapR asG rg (mapR asF rf t)
    fusion {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .here-eq =
      refl
    fusion {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .below-eq w =
        idAdj (E Z (ug (uf x))
                   (FMap.shape gm (uf x) (FMap.shape fm x (here t))) w)
      , ( (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion ef eg (below t x'' eX))
        , (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion˘ ef eg (below t x'' eX)) )

    fusion˘ : ∀ {x : I X} {y : I Y} {z : I Z}
                (rf : uf x ≡ y) (rg : ug y ≡ z)
                (t : M (A X) (E X) x)
            → mapR asG rg (mapR asF rf t)
              ≈M mapR asC (trans (cong ug rf) rg) t
    fusion˘ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .here-eq =
      refl
    fusion˘ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .below-eq w =
        idAdj (E Z (ug (uf x))
                   (FMap.shape gm (uf x) (FMap.shape fm x (here t))) w)
      , ( (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion˘ ef eg (below t x'' eX))
        , (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion ef eg (below t x'' eX)) )

------------------------------------------------------------------------
-- Consequences of fusion: the tree action sends composition to nested
-- application and identity to relocation-along-refl, up to bisimulation.
--
-- 融合的推论：树作用把复合映为嵌套作用、把恒等映为沿 refl 重定位，
-- 均在互模拟意义下。
------------------------------------------------------------------------
mapF-comp : ∀ {i j k a b c d e fℓ : Level}
              {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e fℓ}
              (gm : FMap Y Z) (fm : FMap X Y)
              (x : I X) (t : M (A X) (E X) x)
          → FMap.mapF (compF gm fm) x t
            ≈M FMap.mapF gm (FMap.u fm x) (FMap.mapF fm x t)
mapF-comp gm fm x t = Fusion.fusion gm fm refl refl t

mutual
  mapF-id : ∀ {i a b : Level} {X : Sys i a b}
              (x : I X) (t : M (A X) (E X) x)
          → FMap.mapF (idF X) x t ≈M relocate refl t
  mapF-id {X = X} x t .here-eq = refl
  mapF-id {X = X} x t .below-eq w =
      idAdj (E X x (here t) w)
    , ( (λ q → mapF-id w (below t w q))
      , (λ q → mapF-id˘ w (below t w q)) )

  mapF-id˘ : ∀ {i a b : Level} {X : Sys i a b}
               (x : I X) (t : M (A X) (E X) x)
           → relocate refl t ≈M FMap.mapF (idF X) x t
  mapF-id˘ {X = X} x t .here-eq = refl
  mapF-id˘ {X = X} x t .below-eq w =
      idAdj (E X x (here t) w)
    , ( (λ q → mapF-id˘ w (below t w q))
      , (λ q → mapF-id w (below t w q)) )

------------------------------------------------------------------------
-- Congruence of the deterministic tree action under bisimulation.
--
-- Workhorse: acting along an arbitrary graph witness r is, up to
-- bisimulation, relocating the refl-witness action. J is on the
-- independently bound target index v; at refl it is the existing
-- relocate-refl bisimulation. Both directions are carried.
--
-- 确定性树作用在互模拟下的同余。
-- 工作马：沿任意图见证 r 作用，在互模拟意义下等于对 refl 见证作用做
-- 重定位。对独立绑定的目标索引 v 做 J；refl 处即已有的沿 refl 重定位
-- 互模拟。两个方向都携带。
------------------------------------------------------------------------
module Cong {i j a b c d : Level}
           {X : Sys i a b} {Y : Sys j c d}
           (f : FMap X Y) where
  private
    asF  = FMap.asMorph f
    uf   = FMap.u f
    mapf = FMap.mapF f

  mutual
    mapR-rel : ∀ {x : I X} {v : I Y} (r : uf x ≡ v)
                 (t : M (A X) (E X) x)
             → mapR asF r t ≈M relocate r (mapf x t)
    mapR-rel {x = x} {v = .(uf x)} refl t = ≈rel-refl˘ (mapf x t)

    mapR-rel˘ : ∀ {x : I X} {v : I Y} (r : uf x ≡ v)
                  (t : M (A X) (E X) x)
              → relocate r (mapf x t) ≈M mapR asF r t
    mapR-rel˘ {x = x} {v = .(uf x)} refl t = ≈rel-refl (mapf x t)

    -- Acting along two homogeneously equal graph witnesses (same
    -- endpoints) gives bisimilar trees: J on the independently bound
    -- witness equation, reflexivity at refl. No K (the two witnesses are
    -- independent variables; their equality is carried data, not UIP).
    --
    -- 沿两条同质相等的图见证（同端点）作用得到互模拟树：对独立绑定的
    -- 见证等式做 J，refl 处即自反。无需 K（两个见证是独立变量，其相等
    -- 是携带数据而非 UIP）。
    mapR-r-eq : ∀ {x : I X} {v : I Y} {r r' : uf x ≡ v}
                  (eq : r ≡ r') (t : M (A X) (E X) x)
              → mapR asF r t ≈M mapR asF r' t
    mapR-r-eq {x = x} {r = z} {r' = .z} refl t =
      ≈M-refl (mapR asF z t)

    -- Naturality: acting by f after relocating along d equals acting with
    -- the flattened graph witness trans (cong uf d) r₀. J on the
    -- independently bound node path d and witness r₀; at refl the two
    -- sides differ only by relocate-refl wrappers, removed by the guarded
    -- recursive call (fusion style). fwd / bwd are carried as a pair; no
    -- recursive call is wrapped by an outer combinator.
    --
    -- 自然性：先沿 d 重定位再经 f 作用，等于用展平的图见证
    -- trans (cong uf d) r₀ 作用。对独立绑定的节点路径 d 与见证 r₀ 做 J；
    -- refl 处两侧仅差 relocate-refl 包装，由受保护递归调用消除（fusion
    -- 式）。fwd / bwd 成对携带，递归调用不被外层组合子包裹。
    -- The two directions are a mutual pair (fusion style): each child
    -- calls the matching direction bare, never wrapped by ≈M-sym (which
    -- would strip the coinductive guard).
    --
    -- 两个方向构成互逆对（fusion 式）：每个子节点裸调用匹配方向，绝不用
    -- ≈M-sym 包裹（那会剥离余归纳守护）。
    mapR-cross : ∀ {x₁ x₀ : I X} {v : I Y}
                   (d : x₁ ≡ x₀) (r₀ : uf x₀ ≡ v)
                   (s₁ : M (A X) (E X) x₁)
               → mapR asF r₀ (relocate d s₁)
                 ≈M mapR asF (trans (cong uf d) r₀) s₁
    mapR-cross {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .here-eq =
      refl
    mapR-cross {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .below-eq w =
      idAdj (E Y (uf z) (FMap.shape f z (here s₁)) w)
      , ( (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross refl r' (below s₁ x' e))
        , (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross˘ refl r' (below s₁ x' e)) )

    mapR-cross˘ : ∀ {x₁ x₀ : I X} {v : I Y}
                    (d : x₁ ≡ x₀) (r₀ : uf x₀ ≡ v)
                    (s₁ : M (A X) (E X) x₁)
                → mapR asF (trans (cong uf d) r₀) s₁
                  ≈M mapR asF r₀ (relocate d s₁)
    mapR-cross˘ {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .here-eq =
      refl
    mapR-cross˘ {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .below-eq w =
      idAdj (E Y (uf z) (FMap.shape f z (here s₁)) w)
      , ( (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross˘ refl r' (below s₁ x' e))
        , (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross refl r' (below s₁ x' e)) )

    -- Fused congruence engine. Relates mapR asF rT T (source xT) and
    -- mapR asF rS S (source xS), where d : xS ≡ xT links the source nodes
    -- and h : T ≈M relocate d S is the carried heterogeneous bisimulation.
    -- All index equations (d, rT, rS, witness compatibility ww) are
    -- independently bound and J-eliminated up front; at refl the relocated
    -- s-tree collapses DEFINITIONALLY (relocate refl S = S), and an
    -- ascribed copy h' : T ≈M S forces that conversion once at tree level so
    -- every canonical-child function sees clean labels. Each output child is
    -- then ONE bare recursive gow / gow˘ call; the adjunction round-trips (η)
    -- and relocation naturality only build the recursive INPUT h-rec / hrb
    -- from h's own fields. No recursive call is wrapped by ≈M-trans, so
    -- coinduction stays guarded (fusion style).
    --
    -- 融合同余引擎。关联 mapR asF rT T（源 xT）与 mapR asF rS S（源 xS），
    -- d : xS ≡ xT 连接源节点，h : T ≈M relocate d S 为携带的异质互模拟。
    -- 所有索引等式（d、rT、rS、见证相容 ww）均独立绑定并在前端 J 消去；
    -- refl 处重定位树定义性塌缩（relocate refl S = S），并用带类型标注的
    -- 副本 h' : T ≈M S 在树层级强制完成该转换一次，使每个规范子节点函数
    -- 看到干净标签。此后每个输出子节点恰是一次裸 gow / gow˘ 递归；伴随
    -- 往返（η）与重定位自然性只用 h 自带字段构造递归的输入 h-rec / hrb。
    -- 递归调用绝不被 ≈M-trans 包裹，余归纳保持受保护（fusion 式）。
    gow : ∀ {xS xT : I X} {v : I Y}
            (d : xS ≡ xT) (rT : uf xT ≡ v) {rS : uf xS ≡ v}
            (ww : rS ≡ trans (cong uf d) rT)
            {T : M (A X) (E X) xT} {S : M (A X) (E X) xS}
            (h : T ≈M relocate d S)
        → mapR asF rT T ≈M mapR asF rS S
    gow˘ : ∀ {xS xT : I X} {v : I Y}
             (d : xS ≡ xT) (rT : uf xT ≡ v) {rS : uf xS ≡ v}
             (ww : rS ≡ trans (cong uf d) rT)
             {T : M (A X) (E X) xT} {S : M (A X) (E X) xS}
             (h : T ≈M relocate d S)
         → mapR asF rS S ≈M mapR asF rT T

    gow {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl h
      .here-eq = cong (FMap.shape f z) (h .here-eq)
    gow {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl
        {T = T} {S = S} h
      .below-eq w = adjout , (fwd , bwd)
      where
      h' : T ≈M S
      h' = h
      e   = h' .here-eq
      At  = FMap.adjF f z (here T) w
      As  = FMap.adjF f z (here S) w
      Pt = E Y (uf z) (FMap.shape f z (here T)) w
      Ps = E Y (uf z) (FMap.shape f z (here S)) w
      dd~ = FMap.childF-coh f z e w
      dd  = proj₁ dd~
      ww' = proj₂ dd~
      Dadj = idM-edge-adj {E = E X} {x = z} (here S) dd
      xT' = proj₁ (FMap.childF f z (here T) w)
      xS' = proj₁ (FMap.childF f z (here S) w)
      Rt  = E X z (here T) xT'
      Rs₀ = E X z (here S) xT'
      Rs₁ = E X z (here S) xS'
      bp  = h' .below-eq xT'
      padj = proj₁ bp
      pfwd = proj₁ (proj₂ bp)
      pbwd = proj₂ (proj₂ bp)
      c02 = compAdj Rs₀ Rs₁ Ps (FiberAdj.symAdj Dadj) As
      c03 = compAdj Rt Rs₀ Ps padj c02
      adjout : FiberAdj Ps Pt
      adjout = compAdj Pt Rt Ps (FiberAdj.symAdj At) c03

      fwd : ∀ (qT : Pt)
          → below (mapR asF refl T) w qT
            ≈M below (mapR asF refl S) w (FiberAdj.to adjout qT)
      fwd qT =
        let xT₁ , eT , rT' = FMap.pullF f z (here T) w qT
            qS = FiberAdj.to adjout qT
            xS₁ , _ , rS' = FMap.pullF f z (here S) w qS
            e0  = FiberAdj.to padj eT
            e1  = FiberAdj.fro Dadj e0
            ηs  = FiberAdj.η As e1
            Tsub    = below T xT₁ eT
            B0      = below S xT₁ e0
            SsubCan = below S xS₁ e1
            Sraw    = below S xS₁ (FiberAdj.fro As (FiberAdj.to As e1))
            hrec : Tsub ≈M relocate dd Sraw
            hrec =
              ≈M-trans (pfwd eT)
              (≈M-trans (≈rel-refl B0)
              (≈M-trans (≈M-sym (rel-child-nat S dd e0))
                        (≈M-sym (≈rel-resp dd Sraw SsubCan
                                          (edge-≈ S ηs)))))
        in gow dd rT' ww' hrec

      bwd : ∀ (qS : Ps)
          → below (mapR asF refl S) w qS
            ≈M below (mapR asF refl T) w (FiberAdj.fro adjout qS)
      bwd qS =
        let xS₁ , es , rS' = FMap.pullF f z (here S) w qS
            qT = FiberAdj.fro adjout qS
            xT₁ , _ , rT' = FMap.pullF f z (here T) w qT
            e0' = FiberAdj.to Dadj es
            et' = FiberAdj.fro padj e0'
            ηd  = FiberAdj.η Dadj es
            ηt  = FiberAdj.η At et'
            Sraw    = below S xS₁ es
            SCan'   = below S xS₁ (FiberAdj.fro Dadj e0')
            B0'     = below S xT₁ e0'
            TrawCan = below T xT₁ et'
            Traw    = below T xT₁ (FiberAdj.fro At (FiberAdj.to At et'))
            hrb : Traw ≈M relocate dd Sraw
            hrb =
              ≈M-trans (edge-≈ T ηt)
              (≈M-trans (≈M-sym (pbwd e0'))
              (≈M-trans (≈M-sym (rel-child-nat S dd e0'))
                        (≈rel-resp dd SCan' Sraw
                                   (edge-≈ S ηd))))
        in gow˘ dd rT' ww' hrb

    gow˘ {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl h
      .here-eq = cong (FMap.shape f z) (sym (h .here-eq))
    gow˘ {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl
          {T = T} {S = S} h
      .below-eq w = FiberAdj.symAdj adjout , (fwd˘ , bwd˘)
      where
      h' : T ≈M S
      h' = h
      e   = h' .here-eq
      At  = FMap.adjF f z (here T) w
      As  = FMap.adjF f z (here S) w
      Pt = E Y (uf z) (FMap.shape f z (here T)) w
      Ps = E Y (uf z) (FMap.shape f z (here S)) w
      dd~ = FMap.childF-coh f z e w
      dd  = proj₁ dd~
      ww' = proj₂ dd~
      Dadj = idM-edge-adj {E = E X} {x = z} (here S) dd
      xT' = proj₁ (FMap.childF f z (here T) w)
      xS' = proj₁ (FMap.childF f z (here S) w)
      Rt  = E X z (here T) xT'
      Rs₀ = E X z (here S) xT'
      Rs₁ = E X z (here S) xS'
      bp  = h' .below-eq xT'
      padj = proj₁ bp
      pfwd = proj₁ (proj₂ bp)
      pbwd = proj₂ (proj₂ bp)
      c02 = compAdj Rs₀ Rs₁ Ps (FiberAdj.symAdj Dadj) As
      c03 = compAdj Rt Rs₀ Ps padj c02
      adjout : FiberAdj Ps Pt
      adjout = compAdj Pt Rt Ps (FiberAdj.symAdj At) c03

      fwd˘ : ∀ (qS : Ps)
           → below (mapR asF refl S) w qS
             ≈M below (mapR asF refl T) w (FiberAdj.fro adjout qS)
      fwd˘ qS =
        let xS₁ , es , rS' = FMap.pullF f z (here S) w qS
            qT = FiberAdj.fro adjout qS
            xT₁ , _ , rT' = FMap.pullF f z (here T) w qT
            e0' = FiberAdj.to Dadj es
            et' = FiberAdj.fro padj e0'
            ηd  = FiberAdj.η Dadj es
            ηt  = FiberAdj.η At et'
            Sraw    = below S xS₁ es
            SCan'   = below S xS₁ (FiberAdj.fro Dadj e0')
            B0'     = below S xT₁ e0'
            TrawCan = below T xT₁ et'
            Traw    = below T xT₁ (FiberAdj.fro At (FiberAdj.to At et'))
            hrb : Traw ≈M relocate dd Sraw
            hrb =
              ≈M-trans (edge-≈ T ηt)
              (≈M-trans (≈M-sym (pbwd e0'))
              (≈M-trans (≈M-sym (rel-child-nat S dd e0'))
                        (≈rel-resp dd SCan' Sraw
                                   (edge-≈ S ηd))))
        in gow˘ dd rT' ww' hrb

      bwd˘ : ∀ (qT : Pt)
           → below (mapR asF refl T) w qT
             ≈M below (mapR asF refl S) w (FiberAdj.to adjout qT)
      bwd˘ qT =
        let xT₁ , eT , rT' = FMap.pullF f z (here T) w qT
            qS = FiberAdj.to adjout qT
            xS₁ , _ , rS' = FMap.pullF f z (here S) w qS
            e0  = FiberAdj.to padj eT
            e1  = FiberAdj.fro Dadj e0
            ηs  = FiberAdj.η As e1
            Tsub    = below T xT₁ eT
            B0      = below S xT₁ e0
            SsubCan = below S xS₁ e1
            Sraw    = below S xS₁ (FiberAdj.fro As (FiberAdj.to As e1))
            hrec : Tsub ≈M relocate dd Sraw
            hrec =
              ≈M-trans (pfwd eT)
              (≈M-trans (≈rel-refl B0)
              (≈M-trans (≈M-sym (rel-child-nat S dd e0))
                        (≈M-sym (≈rel-resp dd Sraw SsubCan
                                          (edge-≈ S ηs)))))
        in gow dd rT' ww' hrec

    -- Congruence of the deterministic action: a thin, non-recursive
    -- wrapper; the fused engine gow carries all coinduction.
    --
    -- 确定性作用的同余：薄的非递归封装；全部余归纳由融合引擎 gow 承担。
    mapF-cong : ∀ {x : I X} {t s : M (A X) (E X) x}
              → t ≈M s → mapf x t ≈M mapf x s
    mapF-cong {x = x} {t = t} {s = s} p =
      gow refl refl refl
          (≈M-trans p (≈rel-refl˘ s))

------------------------------------------------------------------------
-- Composition respects behavioural equivalence.
--
-- Finite (non-coinductive) argument. fusion (mapF-comp) identifies each
-- composite action with the nested action; mapR-rel˘ / mapR-cross˘ move the
-- inner index relocation rF across G₁'s action (cong uG₁ rF); mapF-cong
-- applies the inner equivalence F₁≈F₂ under G₁; the outer equivalence
-- G₁≈G₂ then closes the diagram; the second fusion removes G₂∘F₂'s
-- nesting. Only homogeneous index-groupoid paths and carried adjunctions
-- are used; no dependent transport.
--
-- 复合同余于行为等价。
-- 有限（非余归纳）论证。fusion（mapF-comp）把每个复合作用等同为嵌套作
-- 用；mapR-rel˘ / mapR-cross˘ 把内层索引重定位 rF 跨过 G₁ 的作用
-- （cong uG₁ rF）；mapF-cong 在 G₁ 下应用内层等价 F₁≈F₂；外层等价
-- G₁≈G₂ 闭合图表；第二个 fusion 去掉 G₂∘F₂ 的嵌套。仅用同质索引广群
-- 路径与携带伴随，无依赖传输。
------------------------------------------------------------------------
-- trans p refl is propositionally p (J on the independent path p).
--
-- trans p refl 在命题意义下等于 p（对独立路径 p 做 J）。
trans-refl-≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y)
             → trans p refl ≡ p
trans-refl-≡ refl = refl

∘-resp-≈ : ∀ {i j k a b c d e fℓ : Level}
             {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e fℓ}
             {G₁ G₂ : FMap Y Z} {F₁ F₂ : FMap X Y}
         → G₁ ≈F G₂ → F₁ ≈F F₂
         → compF G₁ F₁ ≈F compF G₂ F₂
∘-resp-≈ {X = X} {Y = Y} {Z = Z} {G₁ = G₁} {G₂ = G₂}
          {F₁ = F₁} {F₂ = F₂} eqG eqF x
  with eqF x | eqG (FMap.u F₂ x)
... | rF , hF | rG , hG =
    trans (cong (FMap.u G₁) rF) rG
  , λ t →
      let s1 = FMap.mapF F₁ x t
          s2 = FMap.mapF F₂ x t
          a1 = FMap.mapF G₁ (FMap.u F₁ x) s1
          r  = trans (cong (FMap.u G₁) rF) rG
      in
      ≈M-trans
        (≈rel-resp r (FMap.mapF (compF G₁ F₁) x t) a1
                    (mapF-comp G₁ F₁ x t))
        (≈M-trans
          (≈rel-comp (cong (FMap.u G₁) rF) rG a1)
          (≈M-trans
            (≈rel-resp rG
              (relocate (cong (FMap.u G₁) rF) a1)
              (FMap.mapF G₁ (FMap.u F₂ x) (relocate rF s1))
              (≈M-trans (Cong.mapR-rel˘ G₁ (cong (FMap.u G₁) rF) s1)
              (≈M-trans (Cong.mapR-r-eq G₁
                          (sym (trans-refl-≡ (cong (FMap.u G₁) rF))) s1)
                        (Cong.mapR-cross˘ G₁ rF refl s1))))
            (≈M-trans
              (≈rel-resp rG
                (FMap.mapF G₁ (FMap.u F₂ x) (relocate rF s1))
                (FMap.mapF G₁ (FMap.u F₂ x) s2)
                (Cong.mapF-cong G₁ (hF t)))
              (≈M-trans
                (hG s2)
                (≈M-sym (mapF-comp G₂ F₂ x t))))))

------------------------------------------------------------------------
-- Category laws.
--
-- The node maps of both sides of each law are definitionally equal
-- (composition of u is function composition; u idF = id), so the index
-- groupoid witness is refl throughout. The tree-level clauses are finite
-- bisimulation chains built only from mapF-comp (fusion), mapF-id and
-- mapF-cong; no new coinduction and no transport.
--
-- 范畴定律。
-- 每条定律两侧的节点映射都定义性相等（u 的复合即函数复合，
-- u idF = id），故索引广群见证处处为 refl。树层面子句是仅由
-- mapF-comp（融合）、mapF-id 与 mapF-cong 拼成的有限互模拟链；无新
-- 余归纳、无传输。
------------------------------------------------------------------------
assoc-f : ∀ {i a b : Level} {W X Y Z : Sys i a b}
            (f : FMap W X) (g : FMap X Y) (h : FMap Y Z)
        → compF (compF h g) f ≈F compF h (compF g f)
assoc-f {i = i} {a = a} {b = b} {W} {X} {Y} {Z} f g h x =
    refl
  , λ t →
      let t1 = FMap.mapF f x t
      in ≈M-trans (mapF-comp (compF h g) f x t)
         (≈M-trans (mapF-comp h g (FMap.u f x) t1)
         (≈M-sym
           (≈M-trans (mapF-comp h (compF g f) x t)
                     (Cong.mapF-cong h (mapF-comp g f x t)))))

sym-assoc-f : ∀ {i a b : Level} {W X Y Z : Sys i a b}
                (f : FMap W X) (g : FMap X Y) (h : FMap Y Z)
            → compF h (compF g f) ≈F compF (compF h g) f
sym-assoc-f f g h = ≈F-sym (assoc-f f g h)

identityˡ-f : ∀ {i a b : Level} {X Y : Sys i a b} (f : FMap X Y)
            → compF (idF Y) f ≈F f
identityˡ-f {X = X} {Y = Y} f x =
    refl
  , λ t → ≈M-trans (mapF-comp (idF Y) f x t)
                   (mapF-id (FMap.u f x) (FMap.mapF f x t))

identityʳ-f : ∀ {i a b : Level} {X Y : Sys i a b} (f : FMap X Y)
            → compF f (idF X) ≈F f
identityʳ-f {X = X} {Y = Y} f x =
    refl
  , λ t → ≈M-trans (mapF-comp f (idF X) x t)
                   (Cong.mapF-cong f (mapF-id x t))

identity²-f : ∀ {i a b : Level} {X : Sys i a b}
            → compF (idF X) (idF X) ≈F idF X
identity²-f {X = X} = identityˡ-f (idF X)

------------------------------------------------------------------------
-- The category of edge-indexed M-types and deterministic correspondences.
--
-- Objects are systems Sys; morphisms are deterministic functional
-- correspondences FMap; equality is the transport-free behavioural
-- bisimulation _≈F_. All level arguments are supplied explicitly.
--
-- 边索引化 M 型与确定性对应的范畴。
-- 对象为系统 Sys；态射为确定性函数对应 FMap；相等为无传输的行为互模
-- 拟 _≈F_。所有层级参数显式提供。
------------------------------------------------------------------------
MCorrCat : (i a b : Level)
         → Category (lsuc (i ⊔ a ⊔ b)) (i ⊔ a ⊔ b) (i ⊔ a ⊔ b)
MCorrCat i a b = record
  { Obj       = Sys i a b
  ; _⇒_       = λ X Y → FMap {i = i} {j = i} {a = a} {b = b}
                             {c = a} {d = b} X Y
  ; _≈_       = λ {X} {Y} f g → _≈F_ {i = i} {j = i} {a = a} {b = b}
                                 {c = a} {d = b}
                                 {X = X} {Y = Y} f g
  ; id        = λ {X} → idF X
  ; _∘_       = λ {X} {Y} {Z} g f → compF g f
  ; equiv     = λ {X} {Y} → ≈F-isEquivalence {i = i} {j = i} {a = a}
                                            {b = b} {c = a} {d = b}
                                            {X = X} {Y = Y}
  ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} eqG eqF →
                  ∘-resp-≈ {c = a} {d = b} {e = a} {fℓ = b}
                           {X = X} {Y = Y} {Z = Z}
                           {G₁ = f} {G₂ = h} {F₁ = g} {F₂ = k}
                           eqG eqF
  ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  assoc-f {i = i} {a = a} {b = b}
                          {W = W} {X = X} {Y = Y} {Z = Z} f g h
  ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  sym-assoc-f {i = i} {a = a} {b = b}
                              {W = W} {X = X} {Y = Y} {Z = Z} f g h
  ; identityˡ = λ {X} {Y} {f} →
                  identityˡ-f {i = i} {a = a} {b = b} {X = X} {Y = Y} f
  ; identityʳ = λ {X} {Y} {f} →
                  identityʳ-f {i = i} {a = a} {b = b} {X = X} {Y = Y} f
  ; identity² = λ {X} →
                  identity²-f {i = i} {a = a} {b = b} {X = X}
  }
