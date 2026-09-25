------------------------------------------------------------------------
-- Universal property of the compatible-tower colimit
-- 相容塔余极限泛性质
--
-- Provides the colimit cocone, the cross-category morphism equivalence
-- _≈⇒ℱX_, the iterated tower embeddings embedCosmos^d / lift-subtower,
-- and the left-unit law for comp⇒ℱX-id-left
-- 提供余极限余锥、跨范畴态射等价 _≈⇒ℱX_、迭代塔嵌入 embedCosmos^d /
-- lift-subtower，以及 comp⇒ℱX-id-left 的左单位律
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCatInfinityColimitUniversal where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-trans;1+n≰n)
open import Data.Fin.Base using (Fin; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Maybe.Base using (just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding; module Unfolding)
open import ALMA.Cosmos using (Cosmos; out; _⇒ℱ_; ⇒ℱLayer[_])
open import ALMA.Cosmos.MorphismObject using (MorphismObject; compMorphismObject)
open import ALMA.Cosmos.MorphismMorphism using (MorphismMorphism; compMorphismMorphism)
open import ALMA.Cosmos.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import ALMA.Cosmos.MorphismCorrespondence using (≈C→⇒ℱ)
open import ALMA.Cosmos.FinCatNWitness using (module FinCatN)
open import ALMA.Cosmos.FinCatInfinity using (FinCat∞; TrivialFC∞; n-at)
open import ALMA.Cosmos.FinCatInfinityProjection
  using (finFromℕ-maybe; toℕ-finFromℕ-maybe; finFromℕ-maybe-nothing⇒>; module FinCatNColimitProjection)
open import ALMA.Cosmos.FinCatInfinityTowerCompat using (module FinCatTowerCompat)
open import ALMA.Cosmos.FinCatInfinityColimit
  using (CompatibleTower; subtower; towerColimit; towerColimit-spec
        ; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX; id⇒ℱX; module TowerShapeFunctors
        ; module ProjCosmosMorphism; module EmbedCosmosMorphism)
open FinCatNColimitProjection using (defaultFin)
open _≈C_
open ⇒ℱLayer[_]
open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open CompatibleTower
open MorphismObject
open MorphismMorphism

-- Conversion from the S = id specialisation to the general cross-category
-- morphism along the identity shape functor
-- 从 S = id 特化到沿恒等形状函子的一般跨范畴态射的转换
⇒ℱ→⇒ℱX[id] : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → {F G : Cosmos C FC} → F ⇒ℱ G → F ⇒ℱX[ id ] G
⇒ℱ→⇒ℱX[id] m .out = record
  { shapeTrans    = ⇒ℱLayer[_].shapeTrans (m .out)
  ; morphismObj   = ⇒ℱLayer[_].morphismObj (m .out)
  ; morphismMor   = ⇒ℱLayer[_].morphismMor (m .out)
  ; onunfold-next = λ s → ⇒ℱ→⇒ℱX[id] (⇒ℱLayer[_].onunfold-next (m .out) s)
  }

-- Colimit cocone: layer m of the tower maps to the colimit, as a
-- cross-category morphism along the projection shape functor S-proj m
-- 余极限余锥：塔的第 m 层映射到余极限，作为沿投影形状函子 S-proj m
-- 的跨范畴态射
colimitCocone : ∀ (tower : CompatibleTower) m
  → CompatibleTower.seq tower m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ] towerColimit tower
colimitCocone tower m =
  comp⇒ℱX
    (⇒ℱ→⇒ℱX[id] (≈C→⇒ℱ (towerColimit-spec tower m)))
    (ProjCosmosMorphism.projCosmos-morphism m (CompatibleTower.seq tower m))

-- Decision: either m ≤ n or suc n ≤ m
-- 判定：要么 m ≤ n，要么 suc n ≤ m
split≤ : ∀ m n → (m ≤ n) ⊎ (suc n ≤ m)
split≤ zero    n       = inj₁ z≤n
split≤ (suc m) zero    = inj₂ (s≤s z≤n)
split≤ (suc m) (suc n) with split≤ m n
... | inj₁ m≤n   = inj₁ (s≤s m≤n)
... | inj₂ sn≤m  = inj₂ (s≤s sn≤m)

-- Iterated inject₁: Fin (n-at m) → Fin (n-at (m + d))
-- inject₁ 的 d 次迭代：Fin (n-at m) → Fin (n-at (m + d))
inject₁^d : ∀ d {m} → Fin (n-at m) → Fin (n-at (m + d))
inject₁^d zero    {m} x rewrite +-identityʳ m = x
inject₁^d (suc d) {m} x rewrite +-suc m d     = inject₁ (inject₁^d d x)

-- inject₁^d preserves toℕ
-- inject₁^d 保持 toℕ
toℕ-inject₁^d : ∀ d {m} (x : Fin (n-at m)) → toℕ (inject₁^d d x) ≡ toℕ x
toℕ-inject₁^d zero    {m} x rewrite +-identityʳ m = refl
toℕ-inject₁^d (suc d) {m} x rewrite +-suc m d =
  begin
    toℕ (inject₁ (inject₁^d d x))
      ≡⟨ toℕ-inject₁ (inject₁^d d x) ⟩
    toℕ (inject₁^d d x)
      ≡⟨ toℕ-inject₁^d d x ⟩
    toℕ x
  ∎

-- Iterated S-embed: FinCatN m → FinCatN (m + d) at the shape level
-- S-embed 的 d 次迭代：形状层面 FinCatN m → FinCatN (m + d)
S-embed^d : ∀ d m → Functor (ShapeCat (FinCatN.FinCatN m) (FinCatN.TrivialFCN m))
                            (ShapeCat (FinCatN.FinCatN (m + d)) (FinCatN.TrivialFCN (m + d)))
S-embed^d zero    m rewrite +-identityʳ m = id
S-embed^d (suc d) m rewrite +-suc m d =
  let open TowerShapeFunctors (m + d) using (S-embed)
  in S-embed ∘F S-embed^d d m

-- Iterated embedCosmos: FinCatN m → FinCatN (m + d) at the cosmos level
-- embedCosmos 的 d 次迭代：宇宙层面 FinCatN m → FinCatN (m + d)
embedCosmos^d : ∀ d m
  → Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
  → Cosmos (FinCatN.FinCatN (m + d)) (FinCatN.TrivialFCN (m + d))
embedCosmos^d zero    m x rewrite +-identityʳ m = x
embedCosmos^d (suc d) m x rewrite +-suc m d =
  FinCatTowerCompat.embedCosmos (m + d) (embedCosmos^d d m x)

-- embedCosmos preserves _≈C_
-- embedCosmos 保持 _≈C_
embedCosmos-resp-≈C : ∀ m {x y}
  → x ≈C y
  → FinCatTowerCompat.embedCosmos m x ≈C FinCatTowerCompat.embedCosmos m y
embedCosmos-resp-≈C m {x} {y} eq .unfoldFunctor₀-eq {A = A'} _
  with finFromℕ-maybe (n-at m ∸ 1) (toℕ A')
... | just z  = cong inject₁ (eq .unfoldFunctor₀-eq {A = z} (lift tt))
... | nothing = refl
embedCosmos-resp-≈C m eq .pos-to-shape-eq _ _ = refl
embedCosmos-resp-≈C m eq .unfold-next-eq {A = A'} _ =
  embedCosmos-resp-≈C m
    (eq .unfold-next-eq {A = FinCatTowerCompat.restrictFin m A'} (lift tt))

-- Iterated compatibility: seq of subtower at layer m+d is the
-- embedCosmos^d image of its value at layer m
-- 迭代相容性：subtower 在第 m+d 层的 seq 是其第 m 层值的 embedCosmos^d 像
subtower-compat-iter : ∀ tower k m d
  → CompatibleTower.seq (subtower tower k) (m + d)
    ≈C embedCosmos^d d m (CompatibleTower.seq (subtower tower k) m)
subtower-compat-iter tower k m zero    rewrite +-identityʳ m = ≈C-refl
subtower-compat-iter tower k m (suc d) rewrite +-suc m d =
  ≈C-trans
    (CompatibleTower.compat (subtower tower k) (m + d))
    (embedCosmos-resp-≈C (m + d) (subtower-compat-iter tower k m d))

-- embedCosmos^d as a cross-category morphism along S-embed^d
-- embedCosmos^d 作为沿 S-embed^d 的跨范畴态射
embedCosmos^d-morphism : ∀ d m (x : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m))
  → x ⇒ℱX[ S-embed^d d m ] embedCosmos^d d m x
embedCosmos^d-morphism zero    m x rewrite +-identityʳ m = id⇒ℱX
embedCosmos^d-morphism (suc d) m x rewrite +-suc m d =
  comp⇒ℱX
    (EmbedCosmosMorphism.embedCosmos-morphism (m + d) (embedCosmos^d d m x))
    (embedCosmos^d-morphism d m x)

-- Composition of a cross-category morphism along id on the left,
-- with a morphism along an arbitrary shape functor on the right
-- 左复合：沿 id 的跨范畴态射与沿任意形状函子的跨范畴态射的复合
comp⇒ℱX-id-left : ∀
  {o h e o′ ℓ′ e′ s p}
  {C : Category o h e} {D : Category o′ ℓ′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {F : Cosmos C FC} {G H : Cosmos D FD}
  → G ⇒ℱX[ id ] H → F ⇒ℱX[ S ] G → F ⇒ℱX[ S ] H
comp⇒ℱX-id-left {S = S} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ {A} {s} p →
      ⇒ℱXLayer[_].shapeTrans gLayer
        (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj fLayer) p)
  ; morphismObj   = record
    { onPos      = MorphismObject.onPos moComp
    ; pts-compat = MorphismObject.pts-compat moComp
    }
  ; morphismMor   = record
    { onActP = MorphismMorphism.onActP mmComp
    }
  ; onunfold-next = λ {A} s′ →
      let A′  = proj₁ (Sf.₀ (A , s′))
          s″ = proj₂ (Sf.₀ (A , s′))
      in  comp⇒ℱX-id-left
            (⇒ℱXLayer[_].onunfold-next gLayer {A = A′} s″)
            (⇒ℱXLayer[_].onunfold-next fLayer s′)
  }
  where
    open MorphismObject
    open MorphismMorphism
    module Sf = Functor S
    UF = out F
    UG = out G
    UH = out H
    fLayer = _⇒ℱX[_]_.out f
    gLayer = _⇒ℱX[_]_.out g
    stF = ⇒ℱXLayer[_].shapeTrans fLayer
    stG = ⇒ℱXLayer[_].shapeTrans gLayer
    moF = ⇒ℱXLayer[_].morphismObj fLayer
    moG = ⇒ℱXLayer[_].morphismObj gLayer
    mmF = ⇒ℱXLayer[_].morphismMor fLayer
    mmG = ⇒ℱXLayer[_].morphismMor gLayer
    moComp = compMorphismObject UF UG UH S id stF stG moF moG
    mmComp = compMorphismMorphism UF UG UH S id stF stG mmF mmG

-- Lift a subtower's layer-m value to layer m+d along S-embed^d
-- 沿 S-embed^d 将 subtower 的第 m 层值提升到第 m+d 层
lift-subtower : ∀ tower k m d
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ S-embed^d d m ] CompatibleTower.seq (subtower tower k) (m + d)
lift-subtower tower k m d =
  comp⇒ℱX-id-left
    (⇒ℱ→⇒ℱX[id] (≈C→⇒ℱ (≈C-sym (subtower-compat-iter tower k m d))))
    (embedCosmos^d-morphism d m (CompatibleTower.seq (subtower tower k) m))

-- First component of F₀ (S-embed^d d m) is inject₁^d d
-- F₀ (S-embed^d d m) 的第一分量是 inject₁^d d
S-embed^d-F₀-proj₁ : ∀ d m (A : Fin (n-at m))
    (s : ShapeOf (FinCatN.TrivialFCN m) A)
  → Functor.F₀ (S-embed^d d m) (A , s) .proj₁ ≡ inject₁^d d A
S-embed^d-F₀-proj₁ zero    m A s rewrite +-identityʳ m = refl
S-embed^d-F₀-proj₁ (suc d) m A s rewrite +-suc m d =
  cong inject₁ (S-embed^d-F₀-proj₁ d m A s)

-- Transport a cross-category morphism along S-proj (m+d) ∘ S-embed^d d m
-- to one along S-proj m
-- 将沿 S-proj (m+d) ∘ S-embed^d d m 的跨范畴态射传输为沿 S-proj m 的
transport-to-S-proj : ∀ {m : ℕ} {d : ℕ}
    {F : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
    {G : Cosmos FinCat∞ TrivialFC∞}
  → F ⇒ℱX[ TowerShapeFunctors.S-proj (m + d) ∘F S-embed^d d m ] G
  → F ⇒ℱX[ TowerShapeFunctors.S-proj m ] G
transport-to-S-proj {m} {d} {F} {G} h .out .shapeTrans {A} _ = lift tt
transport-to-S-proj {m} {d} {F} {G} h .out .morphismObj .onPos {A} _ = lift tt
transport-to-S-proj {m} {d} {F} {G} h .out .morphismObj .pts-compat {A} _ = refl
transport-to-S-proj {m} {d} {F} {G} h .out .morphismMor .onActP {A} {B} _ _ _ = refl
transport-to-S-proj {m} {d} {F} {G} h .out .onunfold-next {A} s =
  transport-to-S-proj
    (subst (λ Y' → uF.unfold-next {A = A} (lift tt)
              ⇒ℱX[ TowerShapeFunctors.S-proj (m + d) ∘F S-embed^d d m ] Y')
          (cong (λ k' → uG.unfold-next {A = k'} (lift tt))
                (begin
                    toℕ (Functor.F₀ (S-embed^d d m) (A , s) .proj₁)
                      ≡⟨ cong toℕ (S-embed^d-F₀-proj₁ d m A s) ⟩
                    toℕ (inject₁^d d A)
                      ≡⟨ toℕ-inject₁^d d {m = m} A ⟩
                    toℕ A
                  ∎))
          (h .out .onunfold-next {A = A} s))
  where
    uF = out F
    module uF = Unfolding uF
    uG = out G
    module uG = Unfolding uG

-- defaultFin preserves toℕ when k is in range
-- 当 k 在范围内时，defaultFin 保持 toℕ
toℕ-defaultFin : ∀ m k → k ≤ n-at m ∸ 1 → toℕ (defaultFin m k) ≡ k
toℕ-defaultFin m k k≤
  with finFromℕ-maybe (n-at m ∸ 1) k in eq
... | just x  = toℕ-finFromℕ-maybe (n-at m ∸ 1) k x eq
... | nothing = ⊥-elim (1+n≰n
      (≤-trans (finFromℕ-maybe-nothing⇒> (n-at m ∸ 1) k eq) k≤))

mutual
  -- Cross-category morphism equivalence: a coinductive bisimulation
  -- comparing shapeTrans, onPos, and onunfold-next
  -- 跨范畴态射等价：余归纳互模拟，比较 shapeTrans、onPos 与 onunfold-next
  record _≈⇒ℱX_ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y : Cosmos D FD}
    (f g : x ⇒ℱX[ S ] y)
    : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ h′ ⊔ e′ ⊔ s ⊔ p) where
    coinductive
    field
      out : ≈⇒ℱXLayer f g

  -- One-layer content of the equivalence
  -- 等价的单层内容
  record ≈⇒ℱXLayer {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y : Cosmos D FD}
    (f g : x ⇒ℱX[ S ] y)
    : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ h′ ⊔ e′ ⊔ s ⊔ p) where
    inductive
    field
      shapeTrans-eq : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
                    → ⇒ℱXLayer[_].shapeTrans (f .out) p
                    ≡ ⇒ℱXLayer[_].shapeTrans (g .out) p
      onPos-eq : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
               → MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p
               ≡ MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out)) p
      onunfold-next-eq : ∀ {A} (s : ShapeOf FC A)
                       → f .out .onunfold-next {A = A} s
                         ≈⇒ℱX g .out .onunfold-next {A = A} s

open _≈⇒ℱX_ public
open ≈⇒ℱXLayer public

-- Specialisation of _≈⇒ℱX_ to FinCat∞ with S = id
-- _≈⇒ℱX_ 在 FinCat∞ 上、S = id 的特化
_≈⇒ℱX[id]_ : ∀ {x y : Cosmos FinCat∞ TrivialFC∞}
            → (f g : x ⇒ℱX[ id ] y) → Set
_≈⇒ℱX[id]_ = _≈⇒ℱX_ {C = FinCat∞} {D = FinCat∞}
                     {FC = TrivialFC∞} {FD = TrivialFC∞} {S = id}

-- Reflexivity of _≈⇒ℱX_
-- _≈⇒ℱX_ 的自反性
≈⇒ℱX-refl : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f : x ⇒ℱX[ S ] y} → f ≈⇒ℱX f
≈⇒ℱX-refl .out .shapeTrans-eq _ = refl
≈⇒ℱX-refl .out .onPos-eq _ = refl
≈⇒ℱX-refl .out .onunfold-next-eq s = ≈⇒ℱX-refl

-- Symmetry of _≈⇒ℱX_
-- _≈⇒ℱX_ 的对称性
≈⇒ℱX-sym : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f g : x ⇒ℱX[ S ] y} → f ≈⇒ℱX g → g ≈⇒ℱX f
≈⇒ℱX-sym p .out .shapeTrans-eq q = sym (p .out .shapeTrans-eq q)
≈⇒ℱX-sym p .out .onPos-eq q = sym (p .out .onPos-eq q)
≈⇒ℱX-sym p .out .onunfold-next-eq s = ≈⇒ℱX-sym (p .out .onunfold-next-eq s)

-- Transitivity of _≈⇒ℱX_
-- _≈⇒ℱX_ 的传递性
≈⇒ℱX-trans : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f g h : x ⇒ℱX[ S ] y}
  → f ≈⇒ℱX g → g ≈⇒ℱX h → f ≈⇒ℱX h
≈⇒ℱX-trans p q .out .shapeTrans-eq r =
  trans (p .out .shapeTrans-eq r) (q .out .shapeTrans-eq r)
≈⇒ℱX-trans p q .out .onPos-eq r =
  trans (p .out .onPos-eq r) (q .out .onPos-eq r)
≈⇒ℱX-trans p q .out .onunfold-next-eq s =
  ≈⇒ℱX-trans (p .out .onunfold-next-eq s) (q .out .onunfold-next-eq s)

-- Propositional equality implies _≈⇒ℱX_
-- 命题相等蕴含 _≈⇒ℱX_
≡-to-≈⇒ℱX : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f g : x ⇒ℱX[ S ] y} → f ≡ g → f ≈⇒ℱX g
≡-to-≈⇒ℱX refl = ≈⇒ℱX-refl

-- Congruence of composition with respect to _≈⇒ℱX_
-- 复合关于 _≈⇒ℱX_ 的同余性
comp⇒ℱX-cong-≈⇒ℱX :
  ∀ {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p}
    {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {FE : Functor E (ContCat s p)}
    {S₁ : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {S₂ : Functor (ShapeCat D FD) (ShapeCat E FE)}
    {F : Cosmos C FC} {G : Cosmos D FD} {H : Cosmos E FE}
    {f f′ : F ⇒ℱX[ S₁ ] G} {g g′ : G ⇒ℱX[ S₂ ] H}
  → f ≈⇒ℱX f′ → g ≈⇒ℱX g′
  → comp⇒ℱX g f ≈⇒ℱX comp⇒ℱX g′ f′
comp⇒ℱX-cong-≈⇒ℱX
  {S₁ = S₁} {S₂ = S₂}
  {f = f} {f′ = f′} {g = g} {g′ = g′} eqf eqg = result
  where
    result : comp⇒ℱX g f ≈⇒ℱX comp⇒ℱX g′ f′
    result .out .shapeTrans-eq {A} {s} p =
      begin
        ⇒ℱXLayer[_].shapeTrans (g .out)
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p)
          ≡⟨ cong (λ q → ⇒ℱXLayer[_].shapeTrans (g .out) q)
                  (eqf .out .onPos-eq {A} {s} p) ⟩
        ⇒ℱXLayer[_].shapeTrans (g .out)
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
          ≡⟨ eqg .out .shapeTrans-eq
              (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p) ⟩
        ⇒ℱXLayer[_].shapeTrans (g′ .out)
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
      ∎
    result .out .onPos-eq {A} {s} p =
      begin
        MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out))
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p)
          ≡⟨ cong (λ q → MorphismObject.onPos
                          (⇒ℱXLayer[_].morphismObj (g .out)) q)
                  (eqf .out .onPos-eq {A} {s} p) ⟩
        MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out))
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
          ≡⟨ eqg .out .onPos-eq
              (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p) ⟩
        MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g′ .out))
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
      ∎
    result .out .onunfold-next-eq {A} s =
      comp⇒ℱX-cong-≈⇒ℱX
        {S₁ = S₁} {S₂ = S₂}
        (eqf .out .onunfold-next-eq {A = A} s)
        (eqg .out .onunfold-next-eq
           {A = proj₁ (Functor.F₀ S₁ (A , s))}
           (proj₂ (Functor.F₀ S₁ (A , s))))

-- Left-unit law: composition with id⇒ℱX on the left is _≈⇒ℱX_-equivalent
-- to the original morphism
-- 左单位律：与 id⇒ℱX 的左复合 _≈⇒ℱX_-等价于原态射
left-id-law : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {X : Cosmos C FC} {Y : Cosmos D FD}
  (f : X ⇒ℱX[ S ] Y)
  → comp⇒ℱX-id-left (id⇒ℱX {F = Y}) f ≈⇒ℱX f
left-id-law f .out .shapeTrans-eq {A} {s} p =
  sym (MorphismObject.pts-compat (⇒ℱXLayer[_].morphismObj (f .out))
        {A = A} {s = s} p)
left-id-law f .out .onPos-eq {A} {s} p = refl
left-id-law f .out .onunfold-next-eq {A} s =
  left-id-law (⇒ℱXLayer[_].onunfold-next (f .out) {A = A} s)

-- Consequence: id⇒ℱX satisfies the triangle equation at Y = towerColimit,
-- g = colimitCocone
-- 推论：id⇒ℱX 在 Y = towerColimit、g = colimitCocone 处满足三角等式
id-satisfies-h-tri : ∀ (tower : CompatibleTower) (m : ℕ)
  → comp⇒ℱX-id-left (id⇒ℱX {F = towerColimit tower})
                    (colimitCocone tower m)
    ≈⇒ℱX colimitCocone tower m
id-satisfies-h-tri tower m = left-id-law (colimitCocone tower m)
