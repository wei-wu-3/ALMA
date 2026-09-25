------------------------------------------------------------------------
-- Work in progress: mediate triangle and uniqueness
-- 未完成工作：mediate 三角等式与唯一性
--
-- the mediating morphism mediate, the triangle equation
-- mediate-triangle, the uniqueness statement mediate-unique, the
-- candidate endomorphisms C-1 to C-4, and all bridge lemmas whose only
-- purpose is to serve those statements
-- 中介态射 mediate、三角等式 mediate-triangle、唯一性陈述
-- mediate-unique、候选自同态 C-1 至 C-4，以及所有仅服务于这些陈述
-- 的桥接引理
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.WIP where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-total; m+[n∸m]≡n; +-identityʳ; +-suc; ≤-refl; ≤-trans
        ;m≤n⇒m≤1+n; 1+n≰n; ≡-irrelevant; <⇒≤; _≤?_; ≤-antisym)
open import Data.Fin.Base using (Fin; toℕ; inject₁)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ<n; toℕ-injective)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality.Core using (cong; cong₂; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (J; subst-∘; subst-sym-subst; trans-symˡ; module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (_∘_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding; module Unfolding)
open import ALMA.Cosmos using (Cosmos; out; _⇒ℱ[_]_; _⇒ℱ_; ⇒ℱLayer[_])
open import ALMA.Cosmos.MorphismObject using (MorphismObject; compMorphismObject)
open import ALMA.Cosmos.MorphismMorphism using (MorphismMorphism; compMorphismMorphism)
open import ALMA.Cosmos.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import ALMA.Cosmos.MorphismCorrespondence using (≈C→⇒ℱ)
open import ALMA.Cosmos.FinCatNWitness using (module FinCatN)
open import ALMA.Cosmos.FinCatInfinity
  using (FinCat∞; TrivialFC∞; n-at; natToFin; toℕ-natToFin)
open import ALMA.Cosmos.FinCatInfinityProjection
  using (finFromℕ-maybe; toℕ-finFromℕ-maybe; finFromℕ-maybe-just⇒≤
        ; finFromℕ-maybe-nothing⇒>; module FinCatNColimitProjection)
open FinCatNColimitProjection
  using (defaultFin; defaultFin-toℕ-self; projCosmos; projCosmos-F₀-spec; toℕ≤n∸1)
open import ALMA.Cosmos.FinCatInfinityTowerCompat using (module FinCatTowerCompat)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (_+ʳ_)
open import ALMA.Cosmos.FinCatInfinityColimit
  using (CompatibleTower; subtower; towerColimit; towerColimit-spec
        ; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX; id⇒ℱX; module TowerShapeFunctors
        ; module ProjCosmosMorphism; module EmbedCosmosMorphism)
open import ALMA.Cosmos.FinCatInfinityColimitUniversal
  using (colimitCocone; _≈⇒ℱX_; ≈⇒ℱXLayer; _≈⇒ℱX[id]_; ≈⇒ℱX-refl
        ; ≈⇒ℱX-sym; ≈⇒ℱX-trans; ≡-to-≈⇒ℱX; comp⇒ℱX-cong-≈⇒ℱX
        ; comp⇒ℱX-id-left; lift-subtower; transport-to-S-proj; toℕ-defaultFin
        ; left-id-law; id-satisfies-h-tri; split≤)
open _≈C_
open ⇒ℱLayer[_]
open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open CompatibleTower
open _≈⇒ℱX_
open ≈⇒ℱXLayer
open MorphismObject
open MorphismMorphism

sub-cocone-k≤m
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ) (k≤m : k ≤ m)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      Unfolding.unfold-next (out Y) {A = k} (lift tt)
sub-cocone-k≤m tower Y g k m k≤m =
  subst (λ Y' → CompatibleTower.seq (subtower tower k) m
              ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y')
        (cong (λ k' → Unfolding.unfold-next (out Y) {A = k'} (lift tt))
              (toℕ-defaultFin m k
                (≤-trans k≤m (m≤n⇒m≤1+n ≤-refl))))
        (g m .out .onunfold-next {A = defaultFin m k} (lift tt))

sub-cocone-m≤k≤sucm
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ) (m≤k : m ≤ k) (k≤sucm : k ≤ suc m)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      Unfolding.unfold-next (out Y) {A = k} (lift tt)
sub-cocone-m≤k≤sucm tower Y g k m m≤k k≤sucm =
  subst (λ Y' → CompatibleTower.seq (subtower tower k) m
              ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y')
        (cong (λ k' → Unfolding.unfold-next (out Y) {A = k'} (lift tt))
              (toℕ-defaultFin m k k≤sucm))
        (g m .out .onunfold-next {A = defaultFin m k} (lift tt))

sub-cocone-far
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ) (m≤k : m ≤ k) (ssucm≤k : suc (suc m) ≤ k)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      Unfolding.unfold-next (out Y) {A = k} (lift tt)
sub-cocone-far tower Y g k m m≤k ssucm≤k =
  let d          = k ∸ m
      k≡m+d      = sym (m+[n∸m]≡n m≤k)
      k≤m+d      : k ≤ m + d
      k≤m+d      = subst (λ x → k ≤ x) k≡m+d ≤-refl
      k≤suc-m+d  : k ≤ suc (m + d)
      k≤suc-m+d  = m≤n⇒m≤1+n k≤m+d
      emb        = lift-subtower tower k m d
      gk         = subst (λ Y' → CompatibleTower.seq (subtower tower k) (m + d)
                             ⇒ℱX[ TowerShapeFunctors.S-proj (m + d) ] Y')
                         (cong (λ k' → Unfolding.unfold-next (out Y) {A = k'} (lift tt))
                               (toℕ-defaultFin (m + d) k k≤suc-m+d))
                         (g (m + d) .out .onunfold-next
                            {A = defaultFin (m + d) k} (lift tt))
      comp       = comp⇒ℱX gk emb
  in transport-to-S-proj comp

sub-cocone-with-dec
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ)
    (d₁ : m ≤ k ⊎ k ≤ m)
    (d₂ : k ≤ suc m ⊎ suc (suc m) ≤ k)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      Unfolding.unfold-next (out Y) {A = k} (lift tt)
sub-cocone-with-dec tower Y g k m (inj₂ k≤m) _ =
  sub-cocone-k≤m tower Y g k m k≤m
sub-cocone-with-dec tower Y g k m (inj₁ m≤k) (inj₁ k≤sucm) =
  sub-cocone-m≤k≤sucm tower Y g k m m≤k k≤sucm
sub-cocone-with-dec tower Y g k m (inj₁ m≤k) (inj₂ ssucm≤k) =
  sub-cocone-far tower Y g k m m≤k ssucm≤k

sub-cocone-zero
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
              ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (m : ℕ)
  → CompatibleTower.seq (subtower tower 0) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      Unfolding.unfold-next (out Y) {A = 0} (lift tt)
sub-cocone-zero tower Y g m =
  g m .out .onunfold-next {A = defaultFin m 0} (lift tt)

-- Sub-cocone: the layer-k component of a cocone, restricted to a
-- subtower. This is the local data out of which mediate is built
-- 子余锥：余锥的第 k 层分量限制到子塔。这是构造 mediate 的局部数据
sub-cocone
  : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
  → ∀ k m
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      Unfolding.unfold-next (out Y) {A = k} (lift tt)
sub-cocone tower Y g k m =
  sub-cocone-with-dec tower Y g k m
    (≤-total m k) (split≤ k (suc m))

-- Mediating morphism from the colimit to Y, given a cocone g
-- Coinductively defined; its onunfold-next recurses into the sub-tower
-- The triangle and uniqueness statements below concern this morphism
-- 给定余锥 g，从余极限到 Y 的中介态射
-- 余归纳定义；其 onunfold-next 递归进入子塔
-- 下方的三角等式与唯一性陈述均关于该态射
mediate : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m → CompatibleTower.seq tower m
        ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → towerColimit tower ⇒ℱX[ id ] Y
mediate tower Y g .out .shapeTrans _ = lift tt
mediate tower Y g .out .morphismObj .MorphismObject.onPos _ = lift tt
mediate tower Y g .out .morphismObj .MorphismObject.pts-compat _ = refl
mediate tower Y g .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
mediate tower Y g .out .onunfold-next {A = k} (lift tt) =
  mediate (subtower tower k)
          (YU.unfold-next {A = k} (lift tt))
          (sub-cocone tower Y g k)
  where
    module YU = Unfolding (out Y)

-- Source substitution: transport a cross-category morphism along an
-- equality of the source cosmos
-- 源端替换：沿源宇宙的等式传输跨范畴态射
subst-src-FinCatN : ∀ {m}
  {x x' : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  {Y : Cosmos FinCat∞ TrivialFC∞}
  → x ≡ x'
  → (x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → (x' ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
subst-src-FinCatN {m} {x} {x'} {Y} eq f =
  subst (λ z → z ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y) eq f

-- Double symmetry of source substitution
-- 源端替换的双重对称
subst-src-sym-sym-≈⇒ℱX :
  ∀ {m} {x x′ : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
    {Y : Cosmos FinCat∞ TrivialFC∞}
  (eq : x ≡ x′)
  (f : x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → subst-src-FinCatN (sym eq) (subst-src-FinCatN eq f)
    ≈⇒ℱX f
subst-src-sym-sym-≈⇒ℱX {m} {x} {x′} {Y = Y} eq f =
  ≡-to-≈⇒ℱX
    (subst-sym-subst
       {P = λ z → z ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y}
       eq
       {p = f})

-- Source substitution preserves _≈⇒ℱX_
-- 源端替换保持 _≈⇒ℱX_
subst-src-≈ : ∀ {m}
  {x x' : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  {Y : Cosmos FinCat∞ TrivialFC∞}
  (eq : x ≡ x')
  {f g : x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y}
  → f ≈⇒ℱX g
  → subst-src-FinCatN eq f ≈⇒ℱX subst-src-FinCatN eq g
subst-src-≈ refl p = p

-- defaultFin-src-eq: the unfold-next at A equals that at
-- defaultFin m (toℕ A)
-- defaultFin-src-eq：A 处的 unfold-next 等于
-- defaultFin m (toℕ A) 处的 unfold-next
defaultFin-src-eq : ∀ {m} (tower : CompatibleTower) (A : Fin (n-at m))
  → Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
  ≡ Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m (toℕ A)} (lift tt)
defaultFin-src-eq {m} tower A =
  cong (λ z → Unfolding.unfold-next (out (seq tower m)) {A = z} (lift tt))
       (sym (FinCatNColimitProjection.defaultFin-toℕ-self m A))

-- Composition commutes with source substitution
-- 复合与源端替换交换
comp⇒ℱX-subst-src : ∀ {m}
  {x x' : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  {Y Z : Cosmos FinCat∞ TrivialFC∞}
  {g : Y ⇒ℱX[ id ] Z}
  {f : x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y}
  (eq : x ≡ x')
  → subst-src-FinCatN eq (comp⇒ℱX g f) ≡ comp⇒ℱX g (subst-src-FinCatN eq f)
comp⇒ℱX-subst-src refl = refl

-- Source and target substitutions agree on projCosmos-morphism
-- 源端与目标端替换在 projCosmos-morphism 上一致
subst-src-vs-subst-dst : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let x0 = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
        x1 = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m (toℕ A)} (lift tt)
        S  = TowerShapeFunctors.S-proj m
    in  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
          (ProjCosmosMorphism.projCosmos-morphism m x1)
      ≡ subst (λ z → x0 ⇒ℱX[ S ] projCosmos m z) (defaultFin-src-eq tower A)
              (ProjCosmosMorphism.projCosmos-morphism m x0)
subst-src-vs-subst-dst tower m A =
  let x0 = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
      S  = TowerShapeFunctors.S-proj m
  in  J {x = x0} (λ y (e : x0 ≡ y) →
         subst (λ z → z ⇒ℱX[ S ] projCosmos m y) (sym e)
               (ProjCosmosMorphism.projCosmos-morphism m y)
         ≡ subst (λ z → x0 ⇒ℱX[ S ] projCosmos m z) e
               (ProjCosmosMorphism.projCosmos-morphism m x0))
      (defaultFin-src-eq tower A)
      refl

-- Unfold-next of projCosmos-morphism, related by source and target substitutions
-- projCosmos-morphism 的 unfold-next，通过源端与目标端替换相关联
projCosmos-morphism-onunfold-next : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        x = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S = TowerShapeFunctors.S-proj m
    in  subst-src-FinCatN (sym eq) (ProjCosmosMorphism.projCosmos-morphism m x')
        ≡ subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
                (ProjCosmosMorphism.projCosmos-morphism m x)
projCosmos-morphism-onunfold-next tower m A =
  let x  = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
      S  = TowerShapeFunctors.S-proj m
      eq = defaultFin-src-eq tower A
  in  J {x = x} (λ y (e : x ≡ y) →
         subst (λ z → z ⇒ℱX[ S ] projCosmos m y) (sym e)
               (ProjCosmosMorphism.projCosmos-morphism m y)
         ≡ subst (λ z → x ⇒ℱX[ S ] projCosmos m z) e
               (ProjCosmosMorphism.projCosmos-morphism m x))
      eq
      refl

-- _≈⇒ℱX_ version of the previous statement
-- 前一陈述的 _≈⇒ℱX_ 版本
projCosmos-morphism-onunfold-next-≈ :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        x  = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
    in  subst-src-FinCatN (sym eq) (ProjCosmosMorphism.projCosmos-morphism m x')
        ≈⇒ℱX
        subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
              (ProjCosmosMorphism.projCosmos-morphism m x)
projCosmos-morphism-onunfold-next-≈ tower m A =
  ≡-to-≈⇒ℱX (projCosmos-morphism-onunfold-next tower m A)

-- Reverse direction: target substitution corresponds to source substitution
-- 反方向：目标端替换对应源端替换
subst-dst-≈⇒ℱX :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        x  = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
    in  subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
              (ProjCosmosMorphism.projCosmos-morphism m x)
        ≈⇒ℱX
        subst-src-FinCatN (sym eq)
          (ProjCosmosMorphism.projCosmos-morphism m x')
subst-dst-≈⇒ℱX tower m A =
  ≈⇒ℱX-sym (projCosmos-morphism-onunfold-next-≈ tower m A)

-- Unfold-next of projCosmos-morphism expressed by target substitution
-- projCosmos-morphism 的 unfold-next 用目标端替换表示
f-onunfold-next-eq :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k  = toℕ A
        x  = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
        f  = ProjCosmosMorphism.projCosmos-morphism m (CompatibleTower.seq tower m)
    in  f .out .onunfold-next {A = A} (lift tt)
        ≡ subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
                (ProjCosmosMorphism.projCosmos-morphism m x)
f-onunfold-next-eq tower m A
  with FinCatNColimitProjection.defaultFin m (toℕ A)
     | FinCatNColimitProjection.defaultFin-toℕ-self m A
... | .A | refl = refl

-- Inverse direction of the previous statement
-- 前一陈述的反方向
subst-src-projCosmos-eq-onunfold :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k  = toℕ A
        x' = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
        f  = ProjCosmosMorphism.projCosmos-morphism m (CompatibleTower.seq tower m)
    in  subst-src-FinCatN (sym eq)
          (ProjCosmosMorphism.projCosmos-morphism m x')
        ≡ f .out .onunfold-next {A = A} (lift tt)
subst-src-projCosmos-eq-onunfold tower m A
  with FinCatNColimitProjection.defaultFin m (toℕ A)
     | FinCatNColimitProjection.defaultFin-toℕ-self m A
... | .A | refl = refl

-- Unfold-next of colimitCocone, related to the subtower's colimitCocone
-- by source substitution
-- colimitCocone 的 unfold-next，通过源端替换与子塔的 colimitCocone 关联
colimitCocone-onunfold-next : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        Y = towerColimit (subtower tower k)
    in  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
          (colimitCocone (subtower tower k) m)
        ≈⇒ℱX
        (colimitCocone tower m .out .onunfold-next {A = A} (lift tt))
colimitCocone-onunfold-next tower m A =
  let k  = toℕ A
      eq = defaultFin-src-eq tower A
  in ≈⇒ℱX-trans
       (≡-to-≈⇒ℱX (comp⇒ℱX-subst-src (sym eq)))
       (comp⇒ℱX-cong-≈⇒ℱX
          (≡-to-≈⇒ℱX (subst-src-projCosmos-eq-onunfold tower m A))
          ≈⇒ℱX-refl)

-- Target substitution distributes over onunfold-next
-- 目标端替换关于 onunfold-next 分配
subst-⇒ℱX-dst-onunfold-next :
  ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y y′ : Cosmos D FD}
    (eq : y ≡ y′)
    (f : x ⇒ℱX[ S ] y)
    {A : Category.Obj C}
    (s : ShapeOf FC A)
  → (subst (λ (z : Cosmos _ _) → x ⇒ℱX[ S ] z) eq f)
      .out .onunfold-next {A = A} s
    ≡ subst
        (λ (z : Cosmos _ _) →
           Unfolding.unfold-next (out x) {A = A} s
           ⇒ℱX[ S ]
           Unfolding.unfold-next (out z)
             {A = proj₁ (Functor.F₀ S (A , s))}
             (proj₂ (Functor.F₀ S (A , s))))
        eq
        (f .out .onunfold-next {A = A} s)
subst-⇒ℱX-dst-onunfold-next {y = y} {y′ = y′} eq f {A = A} s with y′ | eq
... | .y | refl = refl

-- Proof irrelevance for Lift ⊤
-- Lift ⊤ 的证明无关性
≡-Lift-⊤ : ∀ {ℓ} (x y : Lift ℓ (⊤ {ℓ})) → x ≡ y
≡-Lift-⊤ (lift tt) (lift tt) = refl

-- subst commutes with cong
-- subst 与 cong 交换
subst-cong′ :
  ∀ {a b c} {A : Set a} {B : Set b} {P : B → Set c}
    {x y : A} (f : A → B) (e : x ≡ y) {u : P (f x)}
  → subst (λ z → P (f z)) e u ≡ subst P (cong f e) u
subst-cong′ {x = x} {y = y} f e with y | e
... | .x | refl = refl

-- Correctness of sub-cocone when k = toℕ A is in range
-- 当 k = toℕ A 在范围内时，sub-cocone 的正确性
sub-cocone-correct-k≤m :
  (tower : CompatibleTower)
  (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
           ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  (A : Fin (n-at m))
  (k≤n∸1 : toℕ A ≤ n-at m ∸ 1)
  → let k    = toℕ A
        B    = defaultFin m k
        p    = toℕ-defaultFin m k k≤n∸1
        S    = TowerShapeFunctors.S-proj m
        src  = CompatibleTower.seq (subtower tower k) m
        Tgt  = λ (Z : Cosmos FinCat∞ TrivialFC∞) → src ⇒ℱX[ S ] Z
        Yk   = λ (j : ℕ) →
          Unfolding.unfold-next (out Y) {A = j} (lift tt)
    in  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
          (subst Tgt (cong Yk p)
             (g m .out .onunfold-next {A = B} (lift tt)))
        ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
sub-cocone-correct-k≤m tower Y g m A k≤n∸1 =
  J {A = Fin (n-at m)} {x = B}
    (λ A' e' → (p' : toℕ B ≡ toℕ A') → motive A' e' p')
    {y = A}
    e
    base
    p
  where
    k : ℕ
    k = toℕ A
    B : Fin (n-at m)
    B = defaultFin m k
    e : B ≡ A
    e = defaultFin-toℕ-self m A
    p : toℕ B ≡ toℕ A
    p = toℕ-defaultFin m k k≤n∸1

    S : Functor (ShapeCat (FinCatN.FinCatN m) (FinCatN.TrivialFCN m))
                (ShapeCat FinCat∞ TrivialFC∞)
    S = TowerShapeFunctors.S-proj m

    src : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
    src = CompatibleTower.seq (subtower tower k) m

    Tgt : Cosmos FinCat∞ TrivialFC∞ → Set _
    Tgt = λ Z → src ⇒ℱX[ S ] Z

    Yk : ℕ → Cosmos FinCat∞ TrivialFC∞
    Yk = λ j → Unfolding.unfold-next (out Y) {A = j} (lift tt)

    unfold-src : Fin (n-at m) → Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
    unfold-src = λ z →
      Unfolding.unfold-next (out (CompatibleTower.seq tower m)) {A = z} (lift tt)

    src-eq : ∀ (A' : Fin (n-at m)) (e' : B ≡ A') → unfold-src B ≡ unfold-src A'
    src-eq = λ A' e' → sym (cong unfold-src (sym e'))

    motive : (A' : Fin (n-at m)) (e' : B ≡ A')
             (p' : toℕ B ≡ toℕ A') → Set _
    motive A' e' p' =
      _≈⇒ℱX_
        {S = S}
        {x = unfold-src A'} {y = Yk (toℕ A')}
        (subst-src-FinCatN
          {m = m} {x = unfold-src B} {x' = unfold-src A'}
          {Y = Yk (toℕ A')}
          (src-eq A' e')
          (subst (λ Z → unfold-src B ⇒ℱX[ S ] Z) (cong Yk p')
             (g m .out .onunfold-next {A = B} (lift tt))))
        (g m .out .onunfold-next {A = A'} (lift tt))

    base : (p' : toℕ B ≡ toℕ B) → motive B refl p'
    base p' =
      ≡-to-≈⇒ℱX
        {S = S}
        {x = unfold-src B} {y = Yk (toℕ B)}
        (cong
           (λ p0 → subst (λ Z → unfold-src B ⇒ℱX[ S ] Z) (cong Yk p0)
                     (g m .out .onunfold-next {A = B} (lift tt)))
           (≡-irrelevant p' refl))

-- Correctness of sub-cocone in general
-- sub-cocone 的一般正确性
sub-cocone-correct
  : ∀ tower Y g m A
  → subst-src-FinCatN (sym (defaultFin-src-eq tower A))
      (sub-cocone tower Y g (toℕ A) m)
    ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
sub-cocone-correct tower Y g m A
  with ≤-total m (toℕ A) | split≤ (toℕ A) (suc m)
... | inj₂ k≤m | _ =
      sub-cocone-correct-k≤m tower Y g m A
        (≤-trans k≤m (m≤n⇒m≤1+n ≤-refl))
... | inj₁ m≤k | inj₁ k≤sucm =
      sub-cocone-correct-k≤m tower Y g m A k≤sucm
... | inj₁ m≤k | inj₂ ssucm≤k =
      ⊥-elim (1+n≰n (≤-trans ssucm≤k (toℕ≤n∸1 m A)))

-- Target substitution on shapeTrans
-- 目标端替换在 shapeTrans 上
subst-⇒ℱX-dst-shapeTrans :
  ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y y′ : Cosmos D FD}
  (eq : y ≡ y′) (f : x ⇒ℱX[ S ] y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → ⇒ℱXLayer[_].shapeTrans
      ((subst (λ z → x ⇒ℱX[ S ] z) eq f) .out) p
    ≡ subst
        (λ z → ShapeOf FD
          (Functor.F₀ (Unfolding.unfoldFunctor (out z))
                      (Functor.F₀ S (A , s))))
        eq
        (⇒ℱXLayer[_].shapeTrans (f .out) p)
subst-⇒ℱX-dst-shapeTrans {y = y} {y′ = y′} eq f {A = A} {s = s} p with y′ | eq
... | .y | refl = refl

-- Target substitution on onPos
-- 目标端替换在 onPos 上
subst-⇒ℱX-dst-onPos :
  ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y y′ : Cosmos D FD}
  (eq : y ≡ y′) (f : x ⇒ℱX[ S ] y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → MorphismObject.onPos
      (⇒ℱXLayer[_].morphismObj
         ((subst (λ z → x ⇒ℱX[ S ] z) eq f) .out)) p
    ≡ MorphismObject.onPos
        (⇒ℱXLayer[_].morphismObj (f .out)) p
subst-⇒ℱX-dst-onPos {y = y} {y′ = y′} eq f {A = A} {s = s} p with y′ | eq
... | .y | refl = refl

subst-dst-general-≈⇒ℱX
  : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {Y Y' : Cosmos D FD}     -- ← Y 和 Y' 分开声明
    (eq : Y ≡ Y')
    {f : x ⇒ℱX[ S ] Y} {g : x ⇒ℱX[ S ] Y'}
  → subst (λ Z → x ⇒ℱX[ S ] Z) eq f ≈⇒ℱX g
  → subst (λ Z → x ⇒ℱX[ S ] Z) (sym eq) g ≈⇒ℱX f
subst-dst-general-≈⇒ℱX refl p = ≈⇒ℱX-sym p

subst-sym-subst-≈⇒ℱX
  : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {Y Y' : Cosmos D FD}
    (eq : Y ≡ Y')
    {f : x ⇒ℱX[ S ] Y}
  → subst (λ Z → x ⇒ℱX[ S ] Z) (sym eq)
      (subst (λ Z → x ⇒ℱX[ S ] Z) eq f)
    ≈⇒ℱX f
subst-sym-subst-≈⇒ℱX refl = ≈⇒ℱX-refl

-- Target substitution by a self-equality is _≈⇒ℱX_-trivial
-- 沿自等式的目标端替换在 _≈⇒ℱX_ 下平凡
subst-dst-self-≈⇒ℱX
  : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {Y : Cosmos D FD}
    {eq : Y ≡ Y}
    {f : x ⇒ℱX[ S ] Y}
  → subst (λ Z → x ⇒ℱX[ S ] Z) eq f ≈⇒ℱX f
subst-dst-self-≈⇒ℱX
  {C = C} {D = D} {FC = FC} {FD = FD} {S = S}
  {x = x} {Y = Y} {eq = eq} {f = f} =
  go x Y f eq
  where
    subst-∘' : ∀ {a b c} {A : Set a} {B : Set b} {x y : A}
               (P : B → Set c) (f : A → B) (e : x ≡ y)
               (p : P (f x))
             → subst (P ∘ f) e p ≡ subst P (cong f e) p
    subst-∘' P f refl p = refl

    go : (x′ : Cosmos C FC) (Y′ : Cosmos D FD)
         (g : x′ ⇒ℱX[ S ] Y′) (e : Y′ ≡ Y′)
       → subst (λ Z → x′ ⇒ℱX[ S ] Z) e g ≈⇒ℱX g
    go x′ Y′ g e .out .shapeTrans-eq {A} {s} p = {!   !}
    go x′ Y′ g e .out .onPos-eq {A} {s} p =
      subst-⇒ℱX-dst-onPos e g p
    go x′ Y′ g e .out .onunfold-next-eq {A = A} s
      rewrite subst-⇒ℱX-dst-onunfold-next e g s
            | subst-∘' (λ W → Unfolding.unfold-next (out x′) {A = A} s
                                 ⇒ℱX[ S ] W)
                       (λ z → Unfolding.unfold-next (out z)
                                {A = proj₁ (Functor.F₀ S (A , s))}
                                (proj₂ (Functor.F₀ S (A , s))))
                       e
                       (g .out .onunfold-next {A = A} s)
      = go (Unfolding.unfold-next (out x′) {A = A} s)
           (Unfolding.unfold-next (out Y′)
              {A = proj₁ (Functor.F₀ S (A , s))}
              (proj₂ (Functor.F₀ S (A , s))))
           (g .out .onunfold-next {A = A} s)
           (cong (λ z → Unfolding.unfold-next (out z)
                          {A = proj₁ (Functor.F₀ S (A , s))}
                          (proj₂ (Functor.F₀ S (A , s))))
                 e)

-- Symmetric form of projCosmos-morphism's unfold-next equality
-- projCosmos-morphism 的 unfold-next 等式的对称形式
projCosmos-morphism-unfold-sym : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let src-A = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
        x'    = Unfolding.unfold-next (out (seq tower m)) {A = defaultFin m (toℕ A)} (lift tt)
        eq    = defaultFin-src-eq tower A
        S     = TowerShapeFunctors.S-proj m
    in  ProjCosmosMorphism.projCosmos-morphism m (seq tower m)
          .out .onunfold-next {A = A} (lift tt)
        ≡ subst-src-FinCatN (sym eq)
            (ProjCosmosMorphism.projCosmos-morphism m x')
projCosmos-morphism-unfold-sym tower m A =
  trans (f-onunfold-next-eq tower m A)
        (J {x = src-A}
           (λ x' eq →
             subst (λ z → src-A ⇒ℱX[ S ] projCosmos m z) eq
                   (ProjCosmosMorphism.projCosmos-morphism m src-A)
             ≡ subst-src-FinCatN (sym eq)
                   (ProjCosmosMorphism.projCosmos-morphism m x'))
           eq
           refl)
  where
    src-A = Unfolding.unfold-next (out (seq tower m)) {A = A} (lift tt)
    eq    = defaultFin-src-eq tower A
    S     = TowerShapeFunctors.S-proj m

-- colimitCocone's unfold-next at A, packaged with source substitution
-- colimitCocone 在 A 处的 unfold-next，配合源端替换打包
colimitCocone-unfold : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → Unfolding.unfold-next (out (CompatibleTower.seq tower m)) {A = A} (lift tt)
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
    towerColimit (subtower tower (toℕ A))
colimitCocone-unfold tower m A =
  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
    (colimitCocone (subtower tower (toℕ A)) m)

-- g's unfold-next at A, packaged with source substitution
-- g 在 A 处的 unfold-next，配合源端替换打包
g-unfold : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
         ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  m (A : Fin (n-at m))
  → Unfolding.unfold-next (out (CompatibleTower.seq tower m)) {A = A} (lift tt)
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
    Unfolding.unfold-next (out Y) {A = toℕ A} (lift tt)
g-unfold tower Y g m A =
  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
    (sub-cocone tower Y g (toℕ A) m)

-- colimitCocone-unfold agrees with colimitCocone's onunfold-next
-- colimitCocone-unfold 与 colimitCocone 的 onunfold-next 一致
colimitCocone-unfold-eq' : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → colimitCocone-unfold tower m A
    ≡ colimitCocone tower m .out .onunfold-next {A = A} (lift tt)
colimitCocone-unfold-eq' tower m A =
  trans (comp⇒ℱX-subst-src (sym eq))
        (cong₂ comp⇒ℱX
          refl
          (sym (projCosmos-morphism-unfold-sym tower m A)))
  where
    eq = defaultFin-src-eq tower A

-- Unfolding to cosmos conversion
-- 展开到宇宙的转换
cosmos-from-unfolding :
  Unfolding TrivialFC∞ (Cosmos FinCat∞ TrivialFC∞)
  → Cosmos FinCat∞ TrivialFC∞
cosmos-from-unfolding u .out = u

-- Triangle equation: mediate composed with the cocone is the cocone
-- 三角等式：mediate 与余锥的复合等于余锥
subst-⇒ℱX-src-shapeTrans : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x') (f : x ⇒ℱX[ S ] Y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → ⇒ℱXLayer[_].shapeTrans ((subst (λ z → z ⇒ℱX[ S ] Y) eq f) .out) p
    ≡ ⇒ℱXLayer[_].shapeTrans (f .out) p
subst-⇒ℱX-src-shapeTrans refl f p = refl

subst-⇒ℱX-src-onPos : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x') (f : x ⇒ℱX[ S ] Y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → MorphismObject.onPos (⇒ℱXLayer[_].morphismObj ((subst (λ z → z ⇒ℱX[ S ] Y) eq f) .out)) p
    ≡ MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p
subst-⇒ℱX-src-onPos refl f p = refl

subst-⇒ℱX-src-onunfold-next : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x') (f : x ⇒ℱX[ S ] Y)
  {A : Category.Obj C} (s : ShapeOf FC A)
  → (subst (λ z → z ⇒ℱX[ S ] Y) eq f) .out .onunfold-next {A = A} s
    ≡ subst (λ z → z ⇒ℱX[ S ]
              Unfolding.unfold-next (out Y)
                {A = proj₁ (Functor.F₀ S (A , s))}
                (proj₂ (Functor.F₀ S (A , s))))
            (cong (λ z → Unfolding.unfold-next (out z) {A = A} s) eq)
            (f .out .onunfold-next {A = A} s)
subst-⇒ℱX-src-onunfold-next refl f p = refl

subst-src-≈-coind : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x')
  {f g : x ⇒ℱX[ S ] Y}
  → f ≈⇒ℱX g
  → subst (λ z → z ⇒ℱX[ S ] Y) eq f ≈⇒ℱX subst (λ z → z ⇒ℱX[ S ] Y) eq g
subst-src-≈-coind eq {f} {g} p .out .shapeTrans-eq {A} {s} p' =
  trans (subst-⇒ℱX-src-shapeTrans eq f p')
        (trans (p .out .shapeTrans-eq {A} {s} p')
               (sym (subst-⇒ℱX-src-shapeTrans eq g p')))
subst-src-≈-coind eq {f} {g} p .out .onPos-eq {A} {s} p' =
  trans (subst-⇒ℱX-src-onPos eq f p')
        (trans (p .out .onPos-eq {A} {s} p')
               (sym (subst-⇒ℱX-src-onPos eq g p')))
subst-src-≈-coind eq {f} {g} p .out .onunfold-next-eq {A = A} s
  rewrite subst-⇒ℱX-src-onunfold-next eq f {A} s
        | subst-⇒ℱX-src-onunfold-next eq g {A} s
  = subst-src-≈-coind
      (cong (λ z → Unfolding.unfold-next (out z) {A = A} s) eq)
      (p .out .onunfold-next-eq {A = A} s)

mt-go : (tower : CompatibleTower)
      → (Y : Cosmos FinCat∞ TrivialFC∞)
      → (g : ∀ m → CompatibleTower.seq tower m
              ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
      → (m : ℕ)
      → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m) ≈⇒ℱX g m
mt-go tower Y g m .out .shapeTrans-eq _ = ≡-Lift-⊤ _ _
mt-go tower Y g m .out .onPos-eq _     = ≡-Lift-⊤ _ _
mt-go tower Y g m .out .onunfold-next-eq {A = A} (lift tt) =
  let
    k      = toℕ A
    eq-src = defaultFin-src-eq tower A
    Yk     = Unfolding.unfold-next (out Y) {A = k} (lift tt)
    sub-g  = sub-cocone tower Y g k

    -- 1. 复合的展开 = 展开后的复合（定义性等价）
    step₁ : comp⇒ℱX (mediate tower Y g) (colimitCocone tower m) .out .onunfold-next {A = A} (lift tt)
            ≡ comp⇒ℱX (mediate tower Y g .out .onunfold-next {A = k} (lift tt))
                                   (colimitCocone tower m .out .onunfold-next {A = A} (lift tt))
    step₁ = refl

    -- 2. 余锥展开等价于「源替换后的子塔余锥」
    cocone-unfold : colimitCocone tower m .out .onunfold-next {A = A} (lift tt)
                   ≈⇒ℱX subst-src-FinCatN (sym eq-src) (colimitCocone (subtower tower k) m)
    cocone-unfold = ≈⇒ℱX-sym (colimitCocone-onunfold-next tower m A)

    -- 3. 复合的同余性：替换第二个分量
    step₃ : comp⇒ℱX (mediate tower Y g .out .onunfold-next {A = k} (lift tt))
                                (colimitCocone tower m .out .onunfold-next {A = A} (lift tt))
             ≈⇒ℱX comp⇒ℱX (mediate (subtower tower k) Yk sub-g)
                                   (subst-src-FinCatN (sym eq-src) (colimitCocone (subtower tower k) m))
    step₃ = {!   !}

    -- 4. 源替换与复合交换顺序
    step₄ : comp⇒ℱX (mediate (subtower tower k) Yk sub-g)
                                (subst-src-FinCatN (sym eq-src) (colimitCocone (subtower tower k) m))
             ≡ subst-src-FinCatN (sym eq-src)
                 (comp⇒ℱX (mediate (subtower tower k) Yk sub-g)
                           (colimitCocone (subtower tower k) m))
    step₄ = sym (comp⇒ℱX-subst-src (sym eq-src))

    -- 5. 归纳假设：子塔上三角等式成立
    ih : comp⇒ℱX (mediate (subtower tower k) Yk sub-g)
                 (colimitCocone (subtower tower k) m)
          ≈⇒ℱX sub-g m
    ih = mt-go (subtower tower k) Yk sub-g m

    -- 6. 源替换保持等价关系
    step₆ : subst-src-FinCatN (sym eq-src)
                    (comp⇒ℱX (mediate (subtower tower k) Yk sub-g)
                              (colimitCocone (subtower tower k) m))
             ≈⇒ℱX subst-src-FinCatN (sym eq-src) (sub-g m)
    step₆ = subst-src-≈ (sym eq-src) ih

    -- 7. 子余锥正确性：匹配右边 g 的展开
    step₇ : subst-src-FinCatN (sym eq-src) (sub-g m)
            ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
    step₇ = sub-cocone-correct tower Y g m A
  in
    ≈⇒ℱX-trans (≡-to-≈⇒ℱX step₁)
      (≈⇒ℱX-trans step₃
        (≈⇒ℱX-trans (≡-to-≈⇒ℱX step₄)
          (≈⇒ℱX-trans step₆ step₇)))




mediate-triangle : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m → CompatibleTower.seq tower m
        ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → ∀ m
  → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m) ≈⇒ℱX g m
mediate-triangle tower Y g m = mt-go tower Y g m

-- Candidate endomorphisms on towerColimit. C-1 and C-2 place id⇒ℱX at
-- the head, C-3 and C-4 recurse into subtower without mediation
-- Whether any of these is non-trivial under _≈⇒ℱX_ is open
-- towerColimit 上的候选自同态。C-1 与 C-2 在头部放置 id⇒ℱX，
-- C-3 与 C-4 不经过中介直接递归进入 subtower
-- 其中是否有在 _≈⇒ℱX_ 下非平凡者，尚无定论
C-1 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-1 tower .out .shapeTrans _ = lift tt
C-1 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-1 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-1 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-1 tower .out .onunfold-next {A = k} (lift tt) =
  id⇒ℱX {F = towerColimit (subtower tower k)}

C-2 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-2 tower .out .shapeTrans _ = lift tt
C-2 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-2 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-2 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-2 tower .out .onunfold-next {A = k} (lift tt) =
  comp⇒ℱX-id-left
    (id⇒ℱX {F = towerColimit (subtower tower k)})
    (id⇒ℱX {F = towerColimit (subtower tower k)})

C-3 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-3 tower .out .shapeTrans _ = lift tt
C-3 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-3 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-3 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-3 tower .out .onunfold-next {A = k} (lift tt) = C-3 (subtower tower k)

C-4 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-4 tower .out .shapeTrans _ = lift tt
C-4 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-4 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-4 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .shapeTrans _ = lift tt
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .morphismObj .MorphismObject.onPos _ = lift tt
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .morphismObj .MorphismObject.pts-compat _ = refl
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .onunfold-next {A = j} (lift tt) =
  C-4 (subtower (subtower tower k) j)

-- Uniqueness: any h satisfying the triangle equation is _≈⇒ℱX_-equivalent
-- to mediate
-- 唯一性：任何满足三角等式的 h 都 _≈⇒ℱX_-等价于 mediate
mediate-unique : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m → CompatibleTower.seq tower m
        ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → (h : towerColimit tower ⇒ℱX[ id ] Y)
  → (∀ m → comp⇒ℱX h (colimitCocone tower m) ≈⇒ℱX g m)
  → _≈⇒ℱX_ {C = FinCat∞} {D = FinCat∞}
            {FC = TrivialFC∞} {FD = TrivialFC∞} {S = id}
            h (mediate tower Y g)
mediate-unique tower Y g h h-tri = {!   !}
