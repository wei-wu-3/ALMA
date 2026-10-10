------------------------------------------------------------------------
-- Composition of forward edge-following simulations
--
-- Two PushSimˢ through a common middle system compose relationally:
-- the composite index layer is the Σ of the middle index and the two
-- layer witnesses, and the composite label correspondence carries the
-- middle label. The construction is coinductive (copatterns); it is
-- the push counterpart of compMˢ/compFMˢ and is the primitive needed
-- for cocone coherence and mediating triangles.
--
-- 前向边跟随模拟的复合
--
-- 经过同一中间系统的两个 PushSimˢ 以关系方式复合：复合索引层是中间
-- 索引与两个层见证的 Σ，复合标签对应携带中间标签。构造为余归纳
-- （copattern）；它是 compMˢ/compFMˢ 的 push 对偶，也是余锥相干性与
-- mediate 三角所需的原语。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrSetoidPushComp where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)

open SysEq

------------------------------------------------------------------------
-- Composite layer and label relations through the middle system Y
--
-- 经中间系统 Y 的复合层关系与标签对应

module _ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓf ℓe3 ℓr ℓs ℓh ℓg : Level}
         {X : SysEq i a b ℓa ℓe}
         {Y : SysEq j c d ℓc ℓd}
         {Z : SysEq k e f ℓf ℓe3}
         (R : I X → I Y → Set ℓr)
         (S : I Y → I Z → Set ℓs)
         (H : (x : I X) (v : I Y) (r : R x v)
            → A X x → A Y v → Set ℓh)
         (G : (v : I Y) (z : I Z) (s : S v z)
            → A Y v → A Z z → Set ℓg)
         where

  -- Composite index relation: x is related to z through some middle v.
  --
  -- 复合索引关系：x 经某个中间 v 与 z 相关。
  R∘S : I X → I Z → Set (j ⊔ ℓr ⊔ ℓs)
  R∘S x z = Σ (I Y) λ v → Σ (R x v) λ r → S v z

  -- Composite label correspondence: a middle label mediates the two
  -- cross-system label relations.
  --
  -- 复合标签对应：一个中间标签居间连接两个跨系统标签关系。
  H∘G : (x : I X) (z : I Z) (w : R∘S x z)
      → A X x → A Z z → Set (c ⊔ ℓh ⊔ ℓg)
  H∘G x z (v , r , s) a c =
    Σ (A Y v) λ b → H x v r a b × G v z s b c

  -- Relational composition of forward simulations.
  --
  -- 前向模拟的关系复合。
  push-comp : ∀ {x : I X} {v : I Y} {z : I Z}
                {r : R x v} {s : S v z}
                {t : M (A X) (E X) x}
                {u : M (A Y) (E Y) v}
                {w : M (A Z) (E Z) z}
            → PushSimˢ X Y R H r t u
            → PushSimˢ Y Z S G s u w
            → PushSimˢ X Z R∘S H∘G (v , r , s) t w
  push-comp {u = u} p q .PushSimˢ.here-eq =
    M.here u , PushSimˢ.here-eq p , PushSimˢ.here-eq q
  push-comp p q .PushSimˢ.push y e
    with PushSimˢ.push p y e
  ... | v' , eY , r' , p'
    with PushSimˢ.push q v' eY
  ... | z' , eZ , s' , q'
    = z' , eZ , (v' , r' , s') , push-comp p' q'
