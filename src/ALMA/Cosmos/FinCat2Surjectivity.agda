------------------------------------------------------------------------
-- Surjectivity of the dependent embedding on the FinCat 2 tower
-- FinCat 2 塔上依赖嵌入的满射性
--
-- Proves SurjectivityForTower for arbitrary uniform embedding families:
-- every cosmos at layer suc n arises, up to _≈C_, as dep-embed-tower n y
-- for some y at layer n. Uses only the tower's intrinsic structural facts
-- (shape-singleton-at, pos-inhabited-tower)
-- 对任意一致嵌入族证明 SurjectivityForTower：第 suc n 层的任意宇宙都
-- 在 _≈C_ 意义下等于某第 n 层宇宙 y 的 dep-embed-tower n y 像。
-- 仅使用塔的固有结构事实（shape-singleton-at、pos-inhabited-tower）
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2Surjectivity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; suc)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding; unfold-next)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Terminal using (_≈C_)
open import ALMA.Cosmos.CumulativeHierarchy using (EmbeddingData; UniformEmbeddingFamily)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (Tower)
open Tower
open import ALMA.Cosmos.FinCat2Witness using (twoTower)
open import ALMA.Cosmos.FinCat2TowerLemmas using (shape-singleton-at)
open import ALMA.Cosmos.FinCat2Colimit using (pos-inhabited-tower)
open import ALMA.Cosmos.FinCat2ColimitWithDep
  using (SurjectivityForTower; UniformEmbeddingFamilyForTower; dep-embed-tower)

-- Inverse cosmos: read x.F₀ and x.F₁ componentwise at the diagonal lift
-- of ((A, s), s); the choice of lift s is immaterial by shape singleton
-- 逆宇宙：在对角提升 ((A, s), s) 处逐分量读取 x.F₀ 与 x.F₁；
-- 由形状单点性，lift s 的选择无关紧要
y-F₀ : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  (A : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
  (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  → Category.Obj (StrictLayer.C (Tower.layer twoTower n))
y-F₀ n x A s =
  proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s))

y-F₁ : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  {A B : Category.Obj (StrictLayer.C (Tower.layer twoTower n))}
  {s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A}
  {t : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) B}
  (f : Category._⇒_ (StrictLayer.C (Tower.layer twoTower n)) A B)
  (q : actSOf (StrictLayer.FC (Tower.layer twoTower n)) f s ≡ t)
  → Category._⇒_ (StrictLayer.C (Tower.layer twoTower n))
      (y-F₀ n x A s) (y-F₀ n x B t)
y-F₁ n x {A} {B} {s} {t} f q =
  proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₁
           {A = ((A , s) , lift s)}
           {B = ((B , t) , lift t)}
           ((f , q) , cong lift q))

-- Functor laws inherited from x via F-resp-≈ on diagonally-lifted morphisms;
-- the diagonal identity and composite are pointwise equal to the actual
-- ones, so F-resp-≈ applies directly
-- 函子律经 F-resp-≈ 作用于对角提升的态射，从 x 继承；
-- 对角恒等与复合与实际恒等/复合逐分量相等，故 F-resp-≈ 直接适用
y-unfoldFunctor : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  → Functor (ShapeCat
      (StrictLayer.C (Tower.layer twoTower n))
      (StrictLayer.FC (Tower.layer twoTower n)))
      (StrictLayer.C (Tower.layer twoTower n))
y-unfoldFunctor n x = record
  { F₀           = λ { (A , s) → y-F₀ n x A s }
  ; F₁           = λ { {A , s} {B , t} (f , q) →
                       y-F₁ n x {A = A} {B = B} {s = s} {t = t} f q }
  ; identity     = λ { {A , s} →
      let
        module SCₙ = Category (ShapeCat
          (StrictLayer.C (Tower.layer twoTower n))
          (StrictLayer.FC (Tower.layer twoTower n)))
        module SC₊ = Category (ShapeCat
          (StrictLayer.C (Tower.layer twoTower (suc n)))
          (StrictLayer.FC (Tower.layer twoTower (suc n))))
        module Cₙ  = Category (StrictLayer.C (Tower.layer twoTower n))
        UF      = Unfolding.unfoldFunctor (out x)
        id-n    = SCₙ.id {A = (A , s)}
        diag-id = (id-n , cong lift (proj₂ id-n))

        coh-id : SC₊._≈_ diag-id (SC₊.id {A = ((A , s) , lift s)})
        coh-id = Cₙ.Equiv.refl
      in
      Cₙ.Equiv.trans
        (Functor.F-resp-≈ UF {f = diag-id} coh-id)
        (Functor.identity UF {A = ((A , s) , lift s)}) }
  ; homomorphism = λ { {X = (A , s)} {Y = (B , t)} {Z = (C , u)}
                       {f = (f₁ , q₁)} {g = (g₁ , q₂)} →
      let
        module Cₙ  = Category (StrictLayer.C (Tower.layer twoTower n))
        module SCₙ = Category (ShapeCat
          (StrictLayer.C (Tower.layer twoTower n))
          (StrictLayer.FC (Tower.layer twoTower n)))
        module SC₊ = Category (ShapeCat
          (StrictLayer.C (Tower.layer twoTower (suc n)))
          (StrictLayer.FC (Tower.layer twoTower (suc n))))
        UF = Unfolding.unfoldFunctor (out x)
        f-sc : SCₙ._⇒_ (A , s) (B , t)
        f-sc = (f₁ , q₁)
        g-sc : SCₙ._⇒_ (B , t) (C , u)
        g-sc = (g₁ , q₂)
        g∘f : SCₙ._⇒_ (A , s) (C , u)
        g∘f = g-sc SCₙ.∘ f-sc
        f'       = (f-sc , cong lift q₁)
        g'       = (g-sc , cong lift q₂)
        diag-g∘f = (g∘f , cong lift (proj₂ g∘f))
        g'∘f'    = g' SC₊.∘ f'
        coh-hom : SC₊._≈_ diag-g∘f g'∘f'
        coh-hom = Cₙ.Equiv.refl
      in
      Cₙ.Equiv.trans
        (Functor.F-resp-≈ UF {f = diag-g∘f} {g = g'∘f'} coh-hom)
        (Functor.homomorphism UF {f = f'} {g = g'}) }
  ; F-resp-≈     = λ { {A , s} {B , t}
                      {f = (f₁ , q₁)} {g = (f₂ , q₂)} eq-f →
      Unfolding.unfoldFunctor (out x) .Functor.F-resp-≈
        {A = ((A , s) , lift s)}
        {B = ((B , t) , lift t)}
        {f = ((f₁ , q₁) , cong lift q₁)}
        {g = ((f₂ , q₂) , cong lift q₂)}
        eq-f }
  }

-- pos-to-shape-y: the second component of x.F₀ equals the shape of x.F₁'s
-- image, up to shape singleton at the target
-- pos-to-shape-y：x.F₀ 的第二分量等于 x.F₁ 像的形状，
-- 在目标对象上的形状单点性意义下
pos-actS-y : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  {A B : Category.Obj (StrictLayer.C (Tower.layer twoTower n))}
  {s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A}
  {t : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) B}
  (f : Category._⇒_ (StrictLayer.C (Tower.layer twoTower n)) A B)
  (q : actSOf (StrictLayer.FC (Tower.layer twoTower n)) f s ≡ t)
  (p : PosOf (StrictLayer.FC (Tower.layer twoTower n)) {A = A} s)
  → proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((B , t) , lift t))
    ≡ actSOf (StrictLayer.FC (Tower.layer twoTower n))
        (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₁
                 {A = ((A , s) , lift s)}
                 {B = ((B , t) , lift t)}
                 ((f , q) , cong lift q)))
        (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s)))
pos-actS-y n x {A} {B} {s} {t} f q p =
  shape-singleton-at n
    (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((B , t) , lift t)))
    (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((B , t) , lift t)))
    (actSOf (StrictLayer.FC (Tower.layer twoTower n))
      (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₁
               {A = ((A , s) , lift s)}
               {B = ((B , t) , lift t)}
               ((f , q) , cong lift q)))
      (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s))))

-- surj-y: unfoldFunctor is y-unfoldFunctor; unfold-next recurses on the
-- diagonal lift; pos-to-shape reads x.F₀'s second component;
-- pos-actS-compat is pos-actS-y at the canonical position inhabitant
-- surj-y：unfoldFunctor 为 y-unfoldFunctor；unfold-next 在对角提升上
-- 递归；pos-to-shape 读取 x.F₀ 的第二分量；
-- pos-actS-compat 由 pos-actS-y 在典范位置居民处给出
surj-y : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  → Cosmos (StrictLayer.C (Tower.layer twoTower n))
            (StrictLayer.FC (Tower.layer twoTower n))
surj-y n x .out = record
  { unfoldFunctor   = y-unfoldFunctor n x
  ; unfold-next     = λ {A} s →
      surj-y n (x .out .unfold-next {A = (A , s)} (lift s))
  ; pos-to-shape    = λ {A} s _ →
      proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s))
  ; pos-actS-compat = λ {A} {B} {s} {t} f q _ →
      pos-actS-y n x f q (pos-inhabited-tower n A s)
  }

-- x.F₀ is independent of the shape component at layer suc n, by shape
-- singleton at layer n
-- x.F₀ 在 suc n 层的形状分量上无关，由 n 层的形状单点性给出
x-F₀-shape-irrelevant : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  (A : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
  (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  (u v : ShapeOf (StrictLayer.FC (Tower.layer twoTower (suc n))) (A , s))
  → Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , u)
  ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , v)
x-F₀-shape-irrelevant n x A s u v =
  cong F (begin
    u
      ≡˘⟨ lift-lower-eq u ⟩
    lift (lower u)
      ≡⟨ cong lift (shape-singleton-at n A (lower u) (lower v)) ⟩
    lift (lower v)
      ≡⟨ lift-lower-eq v ⟩
    v
    ∎)
  where
    F = λ w → Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , w)
    lift-lower-eq
      : (w : ShapeOf (StrictLayer.FC (Tower.layer twoTower (suc n))) (A , s))
      → lift (lower w) ≡ w
    lift-lower-eq (lift _) = refl

-- dep-F₀ and pos-to-shape of the composite reduce definitionally to
-- x.F₀ at the diagonal lift; the choice of s'' is absorbed by y-F₀'s
-- shape-irrelevance
-- 复合的 dep-F₀ 与 pos-to-shape 定义性归约为对角提升处的 x.F₀；
-- s'' 的选择由 y-F₀ 的形状无关性吸收
dep-F₀-reduce : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  (ed : EmbeddingData (surj-y n x))
  (A : Category.Obj (StrictLayer.C (Tower.layer twoTower n)))
  (s : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  (s'' : ShapeOf (StrictLayer.FC (Tower.layer twoTower n)) A)
  → Unfolding.unfoldFunctor
      (out (dep-embed-tower n (surj-y n x) ed))
      .Functor.F₀ ((A , s) , lift s'')
  ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s)
dep-F₀-reduce n x ed A s s'' = refl

-- Transport of lift along a sigma equality
-- 沿 sigma 等式的 lift 传输
subst-Σ-Lift-≡ : ∀ {a b ℓ} {A : Set a} {B : A → Set b}
  {p q : Σ A B} (e : p ≡ q)
  → subst (λ z → Lift ℓ (B (proj₁ z))) e (lift (proj₂ p))
  ≡ lift (proj₂ q)
subst-Σ-Lift-≡ refl = refl

-- Coinductive bisimulation: unfoldFunctor₀-eq by dep-F₀-reduce +
-- x-F₀-shape-irrelevant; pos-to-shape-eq by shape-singleton-at at the
-- target; unfold-next-eq by rewriting with shape-singleton-at then
-- recursing
-- 余归纳互模拟：unfoldFunctor₀-eq 由 dep-F₀-reduce + x-F₀-shape-irrelevant；
-- pos-to-shape-eq 由目标处的 shape-singleton-at；unfold-next-eq 先用
-- shape-singleton-at 改写再递归
surj-bisim : ∀ n
  (x : Cosmos (StrictLayer.C (Tower.layer twoTower (suc n)))
              (StrictLayer.FC (Tower.layer twoTower (suc n))))
  (ed : EmbeddingData (surj-y n x))
  → x ≈C dep-embed-tower n (surj-y n x) ed
surj-bisim n x ed ._≈C_.unfoldFunctor₀-eq {A = (A , s)} (lift s'') = begin
  Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s'')
    ≡˘⟨ x-F₀-shape-irrelevant n x A s (lift s) (lift s'') ⟩
  Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s)
    ≡˘⟨ dep-F₀-reduce n x ed A s s'' ⟩
  Unfolding.unfoldFunctor (out (dep-embed-tower n (surj-y n x) ed))
    .Functor.F₀ ((A , s) , lift s'')
  ∎
surj-bisim n x ed ._≈C_.pos-to-shape-eq {A = (A , s)} (lift s'') p =
  shape-singleton-at (suc n)
    (Unfolding.unfoldFunctor (out (dep-embed-tower n (surj-y n x) ed))
       .Functor.F₀ ((A , s) , lift s'')) _ _
surj-bisim n x ed ._≈C_.unfold-next-eq {A = (A , s)} (lift s'')
  rewrite shape-singleton-at (suc n) (A , s) (lift s'') (lift s) =
  surj-bisim n
    (x .out .unfold-next {A = (A , s)} (lift s))
    (EmbeddingData.next ed {A = A} s)

-- Surjectivity is unconditional: the proof only invokes
-- shape-singleton-at and pos-inhabited-tower, both intrinsic to the tower
-- 满射性无条件成立：证明只用到 shape-singleton-at 与 pos-inhabited-tower，
-- 二者都是塔的固有结构
surj : (unif : UniformEmbeddingFamilyForTower)
     → SurjectivityForTower unif
surj unif n x =
  surj-y n x ,
  surj-bisim n x (UniformEmbeddingFamily.getData (unif n) (surj-y n x))
