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
-- is not assumed. This module gives the approximants, the M cone, the
-- finite-depth necessity of bisimulation, the compatible-family cone
-- and the unconditional mediating map (limit → νF); the round trips and
-- uniqueness up to _≈Mˢ_ follow in a separate slice, together with the
-- carried-adjunction condition they require.
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
-- 假设。本模块给出近似物、M 锥、互模拟的有限深度必要性、相容族锥与无
-- 条件的中介映射（极限 → νF）；两个往返与到 _≈Mˢ_ 的唯一性连同其所需的
-- 携带伴随条件在另一切片给出。
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
  using (SysEq; EqOn; FiberAdjˢ; idAdjˢ; symAdjˢ; compAdjˢ; _≈Mˢ_)

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

  ----------------------------------------------------------------------
  -- Limit cone: a compatible family of finite-depth observations, with
  -- coherence at the carried setoid (not _≡_). M supplies a cone via
  -- truncation.
  -- 极限锥：有限深度观察的相容族，相容性在携带 setoid（非 _≡_）上。M 经
  -- 截断给出一个锥。

  record Cone (x : I) : Set ℓeq where
    field
      obs : (n : ℕ) → Tr n x
      coh : (n : ℕ) → obs n ≈Tr drop (obs (suc n))
  open Cone

  take-coneM : ∀ {x : I} → M A E x → Cone x
  take-coneM t .obs n = take {n = n} t
  take-coneM t .coh n = take-cone {n = n} t

  -- Label at depth m+1 of a cone.
  -- 锥在深度 m+1 处的标签。
  cone-head : ∀ {x : I} → Cone x → ℕ → A x
  cone-head c m = head (obs c (suc m))

  -- Cumulative edge relabeling: Γ c m y is the adjunction from the
  -- depth-0 edge fibre to the depth-m edge fibre, built by composing the
  -- adjunctions stored in the cone's coherence. `to` sends a depth-0
  -- edge to its depth-m representative.
  -- 累积边重定域：Γ c m y 是从深度 0 边纤维到深度 m 边纤维的伴随，由锥
  -- 相容性中存放的伴随复合而成。`to` 把深度 0 的边映到其在深度 m 的代表。
  relabel : ∀ {x : I} (c : Cone x) (m : ℕ) (y : I)
          → FiberAdjˢ (≈E x (cone-head c m) y)
                       (≈E x (cone-head c 0) y)
  relabel {x = x} c zero    y = idAdjˢ (≈E x (cone-head c 0) y)
  relabel {x = x} c (suc m) y
    with coh c (suc m)
  ... | _ , body
    with body y
  ... | α , _ , _ =
    compAdjˢ (≈E x (cone-head c 0) y)
             (≈E x (cone-head c m) y)
             (≈E x (cone-head c (suc m)) y)
             (relabel c m y) α

  -- Tail cone at the target index y for a depth-0 edge e: its depth-m
  -- observation is the depth-(m+1) child of the cone, read along the
  -- relabelled edge. Coherence is exactly the forward component of the
  -- cone's coherence, using `to (Γ (suc m)) = to α ∘ to (Γ m)`.
  -- 目标索引 y 处、对深度 0 边 e 的尾锥：其深度 m 观察是锥的深度 m+1
  -- 子节点，沿重定域后的边读取。相容性恰为锥相容性的前向分量，用到
  -- `to (Γ (suc m)) = to α ∘ to (Γ m)`。
  tail-obs : ∀ {x : I} (c : Cone x) (y : I)
             (e : E x (cone-head c 0) y) (m : ℕ) → Tr m y
  tail-obs c y e m =
    kids (obs c (suc m)) y (to (relabel c m y) e)

  tail-coh : ∀ {x : I} (c : Cone x) (y : I)
             (e : E x (cone-head c 0) y) (m : ℕ)
           → tail-obs c y e m ≈Tr drop (tail-obs c y e (suc m))
  tail-coh c y e m
    with coh c (suc m)
  ... | _ , body
    with body y
  ... | _ , fwd , _ = fwd (to (relabel c m y) e)

  tail-cone : ∀ {x : I} (c : Cone x) (y : I)
              (e : E x (cone-head c 0) y) → Cone y
  tail-cone c y e .obs = tail-obs c y e
  tail-cone c y e .coh = tail-coh c y e

  ----------------------------------------------------------------------
  -- Mediating map: every compatible cone realizes an M-tree. The head
  -- is the depth-1 label; each child mediates the corresponding tail
  -- cone. The only recursive call is directly under M.below, so the
  -- definition is guarded; all relabeling is carried, no subst.
  -- 中介映射：每个相容锥都实现为一棵 M-树。头部取深度 1 标签；每个子
  -- 节点中介相应的尾锥。唯一的递归调用直接位于 M.below 之下，故受守护；
  -- 所有重定域皆携带，无 subst。

  mediate : ∀ {x : I} → Cone x → M A E x
  mediate c .M.here        = cone-head c 0
  mediate c .M.below y e   = mediate (tail-cone c y e)

  -- This gives the limit→νF leg unconditionally: every compatible
  -- family of finite observations realizes an M-tree, with all
  -- cross-depth edge relabeling carried by FiberAdjˢ (no subst, no
  -- funExt). The two round trips and uniqueness up to _≈Mˢ_ are the next
  -- sub-slice. For a generic cone the cumulative adjunction is the
  -- identity only up to the edge EqOn (η/ε), and the backward leg
  -- compares children at η-related edges; closing it propositionally
  -- either carries the cumulative adjunction as cone data (identity for
  -- truncation cones) or assumes child maps are edge-setoid congruent.
  -- This is the same proof-relevance/funExt boundary as elsewhere, not a
  -- logical necessity, and is stated rather than assumed away.
  --
  -- 这无条件给出极限→νF 一侧：每个有限观察相容族都实现为一棵 M-树，
  -- 跨深度边重定域全部由 FiberAdjˢ 携带（无 subst、无 funExt）。两个往返
  -- 与到 _≈Mˢ_ 的唯一性是下一子切片。对一般锥，累积伴随只在边 EqOn
  -- （η/ε）意义下为恒等，反向腿要在 η 相关的边处比较子树；命题式地闭合
  -- 它，要么把累积伴随作为锥的数据携带（截断锥处即恒等），要么假设子树
  -- 映射是边 setoid 同余。这与别处同属证明相关/funExt 边界，并非逻辑
  -- 必然，此处点明而不偷偷假设。
