------------------------------------------------------------------------
-- Deterministic carried morphisms over setoid systems.
--
-- This is the setoid generalisation of the deterministic FMap in
-- Base/MCorr.agda.  A FMapˢ carries an index function u : I X → I Y, a
-- shape map, a canonical source child together with the graph witness
-- u x' ≡ v, and a whole-fibre carried adjunction FiberAdjˢ at that
-- child.  It induces a tree map mapFˢ via the relation-general Morphˢ
-- along the graph relation (λ x v → u x ≡ v).
--
-- Compared with the propositional FMap, the edge adjunction is a
-- FiberAdjˢ (round-trips at the carried EqOn rather than _≡_), and the
-- propositional childF-coh field (which aligned a label reflow a ≡ a')
-- is dropped: under the carried regime that coherence is absorbed by
-- FiberAdjˢ's to-cong / fro-cong, and Stepˢ itself has no such field.
--
-- This slice defines FMapˢ, its identity and composition and the
-- induced tree map only; the behavioural equivalence and the
-- MCorrCatˢ category are assembled in subsequent slices.
--
-- setoid 系统上的确定性携带态射。
--
-- 这是 Base/MCorr.agda 中确定性 FMap 的 setoid 泛化。FMapˢ 携带索引函
-- 数 u : I X → I Y、形状映射、连同图见证 u x' ≡ v 的规范源子节点，以
-- 及该子节点上的整纤维携带伴随 FiberAdjˢ。它沿图关系
-- （λ x v → u x ≡ v）经关系泛化的 Morphˢ 诱导出树映射 mapFˢ。
--
-- 与命题版 FMap 相比，边伴随为 FiberAdjˢ（往返律建立在携带的 EqOn 而
-- 非 _≡_ 上），并去掉命题版的 childF-coh 字段（用于对齐标签重排
-- a ≡ a'）：在携带制度下该相干性由 FiberAdjˢ 的 to-cong / fro-cong
-- 吸收，Stepˢ 本身也无此字段。
--
-- 本切片只定义 FMapˢ、其恒等/复合与诱导树映射；行为等价与 MCorrCatˢ
-- 范畴在后续切片装配。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrSetoidCat where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Base using (_∘_)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid
  using (SysEq; EqOn; FiberAdjˢ; Stepˢ; Morphˢ; idAdjˢ; compAdjˢ
        ; shapeᴿ; child; edge-adj
        ; _≈Mˢ_; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)

open SysEq
open FiberAdjˢ
open Morphˢ

------------------------------------------------------------------------
-- Deterministic carried morphism
--
-- 确定性携带态射
------------------------------------------------------------------------
record FMapˢ {i j a b c d ℓa ℓe ℓc ℓd : Level}
             (X : SysEq i a b ℓa ℓe)
             (Y : SysEq j c d ℓc ℓd)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓa ⊔ ℓe ⊔ ℓc ⊔ ℓd) where
  field
    u      : I X → I Y
    shape  : (x : I X) → A X x → A Y (u x)

    -- Canonical source child of target child v, carrying u x' ≡ v.
    --
    -- 目标子节点 v 的规范源子节点，携带 u x' ≡ v。
    childF : (x : I X) (a : A X x) (v : I Y)
           → Σ (I X) λ x' → u x' ≡ v

    -- Whole-fibre carried adjunction at the canonical child.
    --
    -- 规范子节点上的整纤维携带伴随。
    adjFˢ  : (x : I X) (a : A X x) (v : I Y)
           → FiberAdjˢ (≈E Y (u x) (shape x a) v)
                       (≈E X x a (proj₁ (childF x a v)))

  -- The deterministic map as a relation-general Morphˢ along the graph
  -- of u; the only graph witness at (x , u x) is ≡refl.
  --
  -- 确定性映射作为沿 u 之图的关系泛化 Morphˢ；(x , u x) 处唯一的图见
  -- 证为 ≡refl。
  asMorphˢ : Morphˢ X Y (λ (x : I X) (v : I Y) → u x ≡ v)
  asMorphˢ .Morphˢ.step {x = x} {y = .(u x)} ≡refl = record
    { shapeᴿ   = shape x
    ; child    = childF x
    ; edge-adj = adjFˢ x
    }

  -- Induced tree map.
  --
  -- 诱导树映射。
  mapFˢ : (x : I X) → M (A X) (E X) x → M (A Y) (E Y) (u x)
  mapFˢ x t = Morphˢ.mapR asMorphˢ ≡refl t

open FMapˢ public

------------------------------------------------------------------------
-- Identity
--
-- 恒等
------------------------------------------------------------------------
idFˢ : ∀ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe}
      → FMapˢ X X
idFˢ {X = X} = record
  { u      = λ x → x
  ; shape  = λ _ a → a
  ; childF = λ x _ v → v , ≡refl
  ; adjFˢ  = λ x a v → idAdjˢ (≈E X x a v)
  }

------------------------------------------------------------------------
-- Composition; the graph witness is the transitive closure of the two
-- stage witnesses, and the fibre adjunctions compose via compAdjˢ.
--
-- 复合；图见证为两段见证的传递闭包，纤维伴随经 compAdjˢ 复合。
------------------------------------------------------------------------
compFˢ : ∀ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓg ℓh : Level}
           {X : SysEq i a b ℓa ℓe}
           {Y : SysEq j c d ℓc ℓd}
           {Z : SysEq k e f ℓg ℓh}
       → FMapˢ Y Z → FMapˢ X Y → FMapˢ X Z
compFˢ {X = X} {Y = Y} {Z = Z} g f = record
  { u      = ug ∘ uf
  ; shape  = λ x a → shapeg (uf x) (shapef x a)
  ; childF = childcomp
  ; adjFˢ  = adjcomp
  }
  where
  uf     = FMapˢ.u f
  ug     = FMapˢ.u g
  shapef = FMapˢ.shape f
  shapeg = FMapˢ.shape g

  childcomp : (x : I X) (a : A X x) (w : I Z)
            → Σ (I X) λ x'' → ug (uf x'') ≡ w
  childcomp x a w =
    let y' , eg  = FMapˢ.childF g (uf x) (shapef x a) w
        x'' , ef = FMapˢ.childF f x a y'
    in x'' , trans (cong ug ef) eg

  adjcomp : (x : I X) (a : A X x) (w : I Z)
          → FiberAdjˢ (≈E Z (ug (uf x))
                            (shapeg (uf x) (shapef x a)) w)
                      (≈E X x a (proj₁ (childcomp x a w)))
  adjcomp x a w =
    let y' , _   = FMapˢ.childF g (uf x) (shapef x a) w
        x'' , _  = FMapˢ.childF f x a y'
    in compAdjˢ (≈E X x a x'')
                (≈E Y (uf x) (shapef x a) y')
                (≈E Z (ug (uf x)) (shapeg (uf x) (shapef x a)) w)
                (FMapˢ.adjFˢ f x a y')
                (FMapˢ.adjFˢ g (uf x) (shapef x a) w)

------------------------------------------------------------------------
-- Subst-free relocation along a propositional index equality.
-- relocate is defined by matching ≡refl, so at ≡refl it is the identity
-- and every round-trip / congruence lemma collapses to the carried
-- bisimulation reflexivity; no coinductive machine and no transport.
--
-- 沿命题索引等式的零 subst 重定位。relocate 按 ≡refl 匹配定义，故在
-- ≡refl 处为恒等，所有往返/同余引理都坍缩为携带式互模拟自反；无需余
-- 归纳机器，也无需传输。
------------------------------------------------------------------------
private
  relocate : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
               {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
           → x ≡ y → M A E x → M A E y
  relocate ≡refl t = t

  ≈rel-respˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                 (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                 {x y : I} (r : x ≡ y) {t s : M A E x}
             → _≈Mˢ_ ≈A ≈E t s
             → _≈Mˢ_ ≈A ≈E (relocate r t) (relocate r s)
  ≈rel-respˢ ≈A ≈E ≡refl p = p

  ≈rel-roundˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                  {E : (x : I) (a : A x) (y : I) → Set b}
                  (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                  (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                  {x y : I} (r : x ≡ y) (t : M A E x)
              → _≈Mˢ_ ≈A ≈E (relocate (sym r) (relocate r t)) t
  ≈rel-roundˢ ≈A ≈E ≡refl t = ≈Mˢ-refl ≈A ≈E t

  ≈rel-compˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                 (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                 {x y z : I} (r : x ≡ y) (s : y ≡ z) (t : M A E x)
             → _≈Mˢ_ ≈A ≈E (relocate (trans r s) t)
                           (relocate s (relocate r t))
  ≈rel-compˢ ≈A ≈E ≡refl ≡refl t = ≈Mˢ-refl ≈A ≈E t

------------------------------------------------------------------------
-- Behavioural equivalence of deterministic carried morphisms.
-- The index functions must agree (first component); after matching that
-- ≡refl the two image trees share an index and are related by the
-- carried bisimulation ≈Mˢ.  In every category law the index component
-- is definitionally ≡refl (id / composition), so no transport ever
-- occurs in the proofs.
--
-- 确定性携带态射的行为等价。索引函数必须一致（第一分量）；匹配该
-- ≡refl 后两棵像树共享索引，由携带式互模拟 ≈Mˢ 相关。在所有范畴律
-- 中索引分量定义性地为 ≡refl（恒等/复合），故证明中从不发生传输。
------------------------------------------------------------------------
module _ {i j a b c d ℓa ℓe ℓc ℓd : Level}
         {X : SysEq i a b ℓa ℓe} {Y : SysEq j c d ℓc ℓd} where

  _≈Fˢ_ : FMapˢ X Y → FMapˢ X Y
        → Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓc ⊔ ℓd)
  _≈Fˢ_ f g =
    ∀ (x : I X)
    → Σ (FMapˢ.u f x ≡ FMapˢ.u g x)
        (λ r → ∀ (t : M (A X) (E X) x)
             → _≈Mˢ_ (≈A Y) (≈E Y)
                      (relocate r (FMapˢ.mapFˢ f x t))
                      (FMapˢ.mapFˢ g x t))

  ≈Fˢ-refl : (f : FMapˢ X Y) → f ≈Fˢ f
  ≈Fˢ-refl f x =
      ≡refl
    , λ t → ≈Mˢ-refl (≈A Y) (≈E Y) (FMapˢ.mapFˢ f x t)

  ≈Fˢ-sym : {f g : FMapˢ X Y} → f ≈Fˢ g → g ≈Fˢ f
  ≈Fˢ-sym {f = f} {g = g} p x with p x
  ... | r , h =
      sym r
    , λ t → ≈Mˢ-trans (≈A Y) (≈E Y)
              (≈rel-respˢ (≈A Y) (≈E Y) (sym r)
                 (≈Mˢ-sym (≈A Y) (≈E Y) (h t)))
              (≈rel-roundˢ (≈A Y) (≈E Y) r (FMapˢ.mapFˢ f x t))

  ≈Fˢ-trans : {f g h : FMapˢ X Y}
            → f ≈Fˢ g → g ≈Fˢ h → f ≈Fˢ h
  ≈Fˢ-trans {f = f} {g = g} {h = h} p q x with p x | q x
  ... | r1 , h1 | r2 , h2 =
      trans r1 r2
    , λ t → ≈Mˢ-trans (≈A Y) (≈E Y)
              (≈rel-compˢ (≈A Y) (≈E Y) r1 r2 (FMapˢ.mapFˢ f x t))
              (≈Mˢ-trans (≈A Y) (≈E Y)
                 (≈rel-respˢ (≈A Y) (≈E Y) r2 (h1 t))
                 (h2 t))

  ≈Fˢ-isEquivalence : IsEquivalence _≈Fˢ_
  ≈Fˢ-isEquivalence = record
    { refl  = λ {f} → ≈Fˢ-refl f
    ; sym   = λ {f g} → ≈Fˢ-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈Fˢ-trans {f = f} {g = g} {h = h}
    }
