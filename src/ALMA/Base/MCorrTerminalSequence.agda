------------------------------------------------------------------------
-- Terminal sequence of the indexed edge-family functor, finite-depth
-- side. The one-step functor is
--   F X i = Σ (A i) λ a → (j : I) (e : E i a j) → X j;
-- its iterates on the unit carrier are the finite-depth trees
--   Tr 0 i = ⊤,  Tr (suc n) i = F (Tr n) i,
-- with bonding maps drop : Tr (suc n) → Tr n (erase the deepest layer)
-- and truncations take n : M i → Tr n i. The take n form a cone over
-- the ω^op terminal sequence (compatibility at the carried finite-depth
-- setoid _≈Tr_), and a carried bisimulation forces agreement at every
-- finite depth.
--
-- Tr is defined by recursion on n rather than as an indexed datatype,
-- so deconstructing a depth never infers a Nat index (no constructor
-- injectivity, no Cubical indexed-match warning).
--
-- Every F-layer exposes its children as data (a bounded/polynomial
-- shape): a tree is determined by its finite-depth prefixes, so the
-- limit is reached at ω with no transfinite (κ) iteration. Equality is
-- the carried setoid/bisimulation rather than _≡_: a propositional iso
-- would compare child functions pointwise and hence need funExt, which
-- is not assumed. The mediating map and the iso up to _≈Mˢ_ follow in a
-- separate slice; this module fixes the approximants, the cone and the
-- finite-depth necessity.
--
-- 索引边族函子的终序列，有限深度侧。一步函子为
--   F X i = Σ (A i) λ a → (j : I) (e : E i a j) → X j；
-- 其在单位载体上的迭代即有限深度树
--   Tr 0 i = ⊤，Tr (suc n) i = F (Tr n) i，
-- 带有结合映射 drop : Tr (suc n) → Tr n（抹去最深层）与截断
-- take n : M i → Tr n i。take n 构成 ω^op 终序列上的锥（在携带式
-- 有限深度 setoid _≈Tr_ 处相容），且携带式互模拟迫使每个有限深度一致。
--
-- Tr 按 n 递归定义而非索引归纳数据类型，故消解深度时从不反推 Nat 索引
-- （无构造子注入，无 Cubical 索引匹配 warning）。
--
-- 每个 F 层都把子节点作为数据暴露（有界/多项式形状）：树由其有限深度
-- 前缀决定，故极限在 ω 处达到，无需超限（κ）迭代。相等取携带 setoid/
-- 互模拟而非 _≡_：命题式同构需逐点比较子函数、因而需要 funExt，此处不
-- 假设。mediate 映射与到 _≈Mˢ_ 的同构在另一切片给出；本模块固定近似物、
-- 锥与有限深度必要性。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrTerminalSequence where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; proj₁; proj₂)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid
  using (SysEq; EqOn; FiberAdjˢ; idAdjˢ; symAdjˢ; _≈Mˢ_)

open FiberAdjˢ

module _ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe) where

  open SysEq X

  private
    ℓtr  = i ⊔ a ⊔ b
    ℓeq = i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe

  ----------------------------------------------------------------------
  -- Finite-depth trees: F^n of the unit carrier. Depth 0 is the single
  -- unit leaf; a successor depth is a label and depth-n children along
  -- every edge.
  -- 有限深度树：单位载体的 F^n。深度 0 为单一单位叶；后继深度为一个
  -- 标签与沿每条边的深度 n 子树。

  Tr : ℕ → I → Set ℓtr
  Tr zero    x = ⊤ {ℓtr}
  Tr (suc n) x =
    Σ (A x) λ a → ((y : I) (e : E x a y) → Tr n y)

  head : ∀ {n : ℕ} {x : I} → Tr (suc n) x → A x
  head = proj₁

  kids : ∀ {n : ℕ} {x : I} (q : Tr (suc n) x)
         (y : I) (e : E x (head q) y) → Tr n y
  kids q y e = proj₂ q y e

  ----------------------------------------------------------------------
  -- Bonding map of the terminal sequence: erase the deepest layer.
  -- 终序列的结合映射：抹去最深层。

  drop : ∀ {n : ℕ} {x : I} → Tr (suc n) x → Tr n x
  drop {n = zero}  _        = tt
  drop {n = suc m} (a , k)  =
    a , λ y e → drop (k y e)

  -- Truncation of an infinite tree to depth n.
  -- 无穷树到深度 n 的截断。
  take : ∀ {n : ℕ} {x : I} → M A E x → Tr n x
  take {n = zero}  _ = tt
  take {n = suc m} t =
    M.here t , λ y e → take (M.below t y e)

  ----------------------------------------------------------------------
  -- Carried finite-depth setoid. The successor case is one
  -- bisimulation step — a label equivalence and, per target index, an
  -- edge adjunction with pointwise related children — recursive in the
  -- depth. It carries the edge adjunction as data, so no equality is
  -- matched and there is no subst.
  -- 携带式有限深度 setoid。后继情形即一步互模拟——标签等价，且对每个
  -- 目标索引给一个边伴随与逐点相关的子树——并对深度递归。边伴随作为
  -- 数据携带，故不匹配等式、无 subst。

  _≈Tr_ : ∀ {n : ℕ} {x : I} → Tr n x → Tr n x → Set ℓeq
  _≈Tr_ {n = zero}  _       _       = ⊤ {ℓeq}
  _≈Tr_ {n = suc m} {x = x} (a , k) (a' , k') =
      EqOn._≈_ (≈A x) a a'
    × ((y : I)
       → Σ (FiberAdjˢ (≈E x a' y) (≈E x a y)) λ adj
       →   (∀ (e : E x a y)
            → _≈Tr_ {n = m} (k y e) (k' y (to adj e)))
         × (∀ (e' : E x a' y)
            → _≈Tr_ {n = m} (k' y e') (k y (fro adj e'))))

  -- Each node already stores both directions, so symmetry only swaps
  -- the adjunction and exchanges the two components (no recursion into
  -- the children).
  -- 每个节点已存放两个方向，故对称只需交换伴随、对调两个分量（无需递归
  -- 进入子树）。
  ≈Tr-sym : ∀ {n : ℕ} {x : I} {q r : Tr n x}
          → q ≈Tr r → r ≈Tr q
  ≈Tr-sym {n = zero}  _           = tt
  ≈Tr-sym {n = suc m} (ha , body) =
      EqOn.sym (≈A _) ha
    , λ y → let adj , fwd , bwd = body y
            in symAdjˢ adj , ( bwd , fwd )

  ≈Tr-refl : ∀ {n : ℕ} {x : I} (q : Tr n x) → q ≈Tr q
  ≈Tr-refl {n = zero}  _       = tt
  ≈Tr-refl {n = suc m} (a , k) =
      EqOn.refl (≈A _)
    , λ y → idAdjˢ (≈E _ a y)
          , ( (λ e → ≈Tr-refl (k y e))
            , (λ e → ≈Tr-refl (k y e)) )

  ----------------------------------------------------------------------
  -- M is a cone over the terminal sequence: truncating to n+1 and then
  -- erasing the deepest layer agrees, at depth n, with truncating to n.
  -- Induction on n; the successor step only rearranges carried
  -- pointwise children, so it never compares functions propositionally.
  -- M 是终序列上的锥：先截断到 n+1 再抹去最深层，在深度 n 处与直接截断
  -- 到 n 一致。对 n 归纳；后继步只重排携带的逐点子树，故绝不命题式地
  -- 比较函数。

  take-cone : ∀ {n : ℕ} {x : I} (t : M A E x)
            → take {n = n} t ≈Tr drop (take {n = suc n} t)
  take-cone {n = zero}  t = tt
  take-cone {n = suc m} t =
      EqOn.refl (≈A _)
    , λ y → idAdjˢ (≈E _ (M.here t) y)
          , ( (λ e → take-cone (M.below t y e))
            , (λ e → ≈Tr-sym (take-cone (M.below t y e))) )

  ----------------------------------------------------------------------
  -- Finite-depth necessity of bisimulation: two bisimilar trees agree
  -- at every finite depth. The bisimulation's edge adjunction is reused
  -- at every depth; induction is on n and the recursive calls are the
  -- carried pointwise children.
  -- 互模拟的有限深度必要性：两棵互模拟的树在每个有限深度一致。互模拟
  -- 的边伴随在每个深度复用；对 n 归纳，递归调用即携带的逐点子树。

  bisim→finite : ∀ {x : I} {t s : M A E x}
               → _≈Mˢ_ ≈A ≈E t s
               → (n : ℕ) → take {n = n} t ≈Tr take {n = n} s
  bisim→finite _ zero = tt
  bisim→finite {x = x} p (suc m) =
      _≈Mˢ_.here-eq p
    , λ y →
        let adj , fwd , bwd = _≈Mˢ_.below-eq p y
        in adj
         , ( (λ e  → bisim→finite (fwd e) m)
           , (λ e' → bisim→finite (bwd e') m) )
