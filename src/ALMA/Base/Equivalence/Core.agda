------------------------------------------------------------------------
-- the core definitions that the rest of Equivalence/ depends on
--   _⊣_          adjunction skeleton on shape-indexed fibres
--   Adj-Unit / Adj-Counit  the two components of the adjunction
--   LayeredEqGen    generic coinductive skeleton, as an application of Mᵢ
--   IndexedLayeredEq indexed skeleton, as an application of Mᵢ
--   LayeredEq       LayeredEqGen at a constant observation family
--
-- Equivalence/ 其余模块所依赖的核心定义
--   _⊣_          形状索引纤维上的伴随骨架
--   Adj-Unit / Adj-Counit  伴随骨架的两个分量
--   LayeredEqGen    通用余归纳骨架，作为 Mᵢ 的应用
--   IndexedLayeredEq 索引骨架，作为 Mᵢ 的应用
--   LayeredEq       LayeredEqGen 在常数观察族处的特化
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.Core where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)

open import ALMA.Base.IndexedMType using (Mᵢ)

------------------------------------------------------------------------
-- Fibre-wise adjunction skeleton
-- The adjunction on each shape-indexed fibre: unit and counit are the
-- two round-trip propositions. They are independent of each other, so
-- a product suffices
--
-- 纤维层面的伴随骨架
-- 每根 shape 索引纤维上的伴随：unit 与 counit 是两条往返命题
-- 两者互相独立，故乘积即可
module _ {a b c d e : Level}
         {S : Set a} {T : Set c} (P : T → Set b) (R : S → Set d)
         {F : Set e} (shape : F → S → T)
         (posL : (f : F) → ∀ {s} → R s → P (shape f s))
         (posR : (f : F) → ∀ {s} → P (shape f s) → R s) where

  Adj-Unit   = ∀ f {s} (r : R s) → posR f (posL f r) ≡ r

  Adj-Counit = ∀ f {s} (p : P (shape f s)) → posL f (posR f p) ≡ p

  _⊣_ : Set (a ⊔ b ⊔ d ⊔ e)
  _⊣_ = Adj-Unit × Adj-Counit

------------------------------------------------------------------------
-- LayeredEqGen as an application of Mᵢ
-- Index is X × X. A (x, y) = layer x y; B (x, y) _ = Obs x
-- Successor at (x, y), p : layer x y, s : Obs x returns
-- (step x s, step y (obs-map x y p s))
--
-- 作为 Mᵢ 应用的 LayeredEqGen
-- 索引为 X × X。A (x, y) = layer x y；B (x, y) _ = Obs x
-- 后继在 (x, y)、p : layer x y、s : Obs x 处返回
-- (step x s, step y (obs-map x y p s))
module _ {a b c : Level} {X : Set a}
         (Obs : X → Set b)
         (step : (x : X) → Obs x → X)
         (layer : X → X → Set c)
         (obs-map : (x y : X) → layer x y → Obs x → Obs y) where
  LayeredEqGen : (x y : X) → Set (c ⊔ b)
  LayeredEqGen x y = Mᵢ A B next (x , y)
    where
      A : X × X → Set c
      A (x , y) = layer x y
      B : (i : X × X) → A i → Set b
      B (x , _) _ = Obs x
      next : (i : X × X) (p : A i) (s : B i p) → X × X
      next (x , y) p s = step x s , step y (obs-map x y p s)

------------------------------------------------------------------------
-- IndexedLayeredEq as an application of Mᵢ
-- Index is Σ I (λ j → X' j × X' j): a shared i together with the pair
-- of states. A (i, x, y) = layerI i x y; B (i, _, _) _ = ObsI i;
-- successor returns to next i with the states advanced by stepI
--
-- 作为 Mᵢ 应用的 IndexedLayeredEq
-- 索引为 Σ I (λ j → X' j × X' j)：共享的 i 与状态对
-- A (i, x, y) = layerI i x y；B (i, _, _) _ = ObsI i；
-- 后继返回 next i 并用 stepI 推进状态
module _ {a b c d : Level}
         {I : Set a} (X' : I → Set b)
         (next : I → I)
         (ObsI : I → Set c)
         (stepI : (i : I) → X' i → ObsI i → X' (next i))
         (layerI : (i : I) → X' i → X' i → Set d) where
  IndexedLayeredEq : (i : I) (x y : X' i) → Set (d ⊔ c)
  IndexedLayeredEq i x y = Mᵢ {I = I'} A B next' (i , x , y)
    where
      I' : Set (a ⊔ b)
      I' = Σ I (λ j → X' j × X' j)
      A : I' → Set d
      A (_ , x , y) = layerI _ x y
      B : (i' : I') → A i' → Set c
      B (i , _ , _) _ = ObsI i
      next' : (i' : I') (p : A i') (s : B i' p) → I'
      next' (i , x , y) p s = next i , stepI i x s , stepI i y s

------------------------------------------------------------------------
-- LayeredEq: constant observation set
-- A specialisation of LayeredEqGen at a constant observation family;
-- obs-map is the identity function
--
-- LayeredEq：常数观察集
-- LayeredEqGen 在常数观察族处的特化；obs-map 为恒等函数
LayeredEq : {a b c : Level} {X : Set a}
            (Obs : Set b) (step : X → Obs → X) (layer : X → X → Set c)
            (x y : X) → Set (c ⊔ b)
LayeredEq Obs step layer x y =
  LayeredEqGen (λ _ → Obs) step layer (λ _ _ _ o → o) x y
