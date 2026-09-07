------------------------------------------------------------------------
-- ALMA — Infinite, Unbounded, Self-Referential Dynamic Cosmos
-- ALMA —— 无穷、无界、自指的动态宇宙
--
-- Built with type theory, category theory, containers, and coalgebraic unfolding
-- Cosmos is the terminal coalgebra of a polynomial functor internalized in type theory
-- 基于类型论、范畴论、容器与余代数展开构建；
-- Cosmos 是内化于类型论中的多项式函子的终余代数
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)

open import ALMA.Cosmos.ContCategory using (≈M-refl; ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding
  using (Unfolding; mapUnfolding; mapUnfolding-id; mapUnfolding-∘; module UnfoldingSetoid)
open import ALMA.Cosmos.MorphismObject using (MorphismObject; idMorphismObject; compMorphismObject)
open import ALMA.Cosmos.MorphismMorphism
  using (MorphismMorphism; idMorphismMorphism; actP-from-S; compMorphismMorphism)

-- Core Definitions: Cosmos as Terminal Coalgebra
-- 核心定义：Cosmos 作为终余代数
-- One-layer unfolding of Cosmos: a container-shaped functorial structure
-- over a parameter X
-- Cosmos 的单层展开：参数 X 上的容器形状函子结构
-- Cosmos: the terminal coalgebra of the polynomial functor Unfolding
-- Defined coinductively: out : Cosmos → Unfolding (Cosmos)
-- Cosmos：多项式函子 Unfolding 的终余代数
-- 以余归纳定义：out : Cosmos → Unfolding (Cosmos)
record Cosmos {o h e s p : Level}
              (C : Category o h e)
              (FC : Functor C (ContCat s p))
              : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
  coinductive
  field
    out : Unfolding FC (Cosmos C FC)
open Cosmos public

-- Lightweight Functoriality of Unfolding
-- Unfolding 的简单函子性
module CosmosMap {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)} where
  -- Functorial action on the parameter: map along X → Y
  -- 参数上的函子作用：沿 X → Y 映射
  mapCosmosF : ∀ {x y : Level} {X : Set x} {Y : Set y}
            → (X → Y) → Unfolding FC X → Unfolding FC Y
  mapCosmosF = mapUnfolding

  -- Identity law: mapCosmosF id ≡ id
  -- 恒等律：mapCosmosF id ≡ id
  map-id : ∀ {x : Level} {X : Set x} (c : Unfolding FC X)
        → mapCosmosF (λ x → x) c ≡ c
  map-id = mapUnfolding-id

  -- Composition law: mapCosmosF (f ∘ g) ≡ mapCosmosF f ∘ mapCosmosF g
  -- 复合律：mapCosmosF (f ∘ g) ≡ mapCosmosF f ∘ mapCosmosF g
  map-∘ : ∀ {x y z : Level} {X : Set x} {Y : Set y} {Z : Set z}
            (f : Y → Z) (g : X → Y) (c : Unfolding FC X)
        → mapCosmosF (f ∘ g) c ≡ mapCosmosF f (mapCosmosF g c)
  map-∘ = mapUnfolding-∘

  -- Congruence: pointwise equal functions induce equal maps
  -- 合同性：逐点相等的函数诱导相等的映射
  map-cong : ∀ {x y : Level} {X : Set x} {Y : Set y}
          → {f g : X → Y} → f ≡ g → mapCosmosF f ≡ mapCosmosF g
  map-cong refl = refl

-- Universe Morphisms: Coalgebra Homomorphisms
-- 宇宙态射：余代数同态
-- Generalized homomorphism _⇒ℱ[_]_ parameterized by a shape functor S.
-- S : Functor (ShapeCat C FC) (ShapeCat C FC) controls how shape indices
-- are transported from source to target.
-- 广义同态 _⇒ℱ[_]_ 以形状函子 S 为参数。
-- S 控制形状索引从源到目标的传输。
mutual
  record _⇒ℱ[_]_ {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
                  (F : Cosmos C FC)
                  (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                  (G : Cosmos C FC)
                  : Set (o ⊔ h ⊔ s ⊔ p) where
    coinductive
    field
      out : ⇒ℱLayer[ S ] F G

  record ⇒ℱLayer[_] {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
                    (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                    (F G : Cosmos C FC)
                    : Set (o ⊔ h ⊔ s ⊔ p) where
    inductive
    private
      module C = Category C
      module S = Functor S
      UF = out F
      UG = out G
    field
      -- Shape translation: maps positions of source to shapes of target
      -- 形状翻译：将源的位置映射为目标宇宙的形状
      shapeTrans  : ∀ {A} {s : ShapeOf FC A}
                  → PosOf FC s
                  → ShapeOf FC (Functor.₀ (Unfolding.unfoldFunctor UG) (S.₀ (A , s)))
      -- Morphism object compatibility
      -- 态射对象相容性
      morphismObj : MorphismObject UF UG S shapeTrans
      -- Morphism morphism compatibility
      -- 态射间态射相容性
      morphismMor : MorphismMorphism UF UG S shapeTrans morphismObj
      -- Recursive universe morphism on next seeds
      -- 下一层种子上的递归宇宙态射
      onunfold-next : ∀ {A} (s : ShapeOf FC A)
                    → Unfolding.unfold-next UF s ⇒ℱ[ S ]
                      Unfolding.unfold-next UG (proj₂ (S.₀ (A , s)))

open _⇒ℱ[_]_ public
open ⇒ℱLayer[_] public

-- S = id specialization
-- S = id 特化
_⇒ℱ_ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
     → Cosmos C FC → Cosmos C FC → Set (o ⊔ h ⊔ s ⊔ p)
_⇒ℱ_ {C = C} {FC = FC} F G = F ⇒ℱ[ id ] G

-- Identity homomorphism exists only at S = id:
-- onunfold-next target = unfold-next UF (proj₂ (id.₀ (A,s))) = unfold-next UF s,
-- so id⇒ℱ applies recursively. For S ≠ id source and target differ, no canonical map.
-- 恒等同态仅在 S = id 存在：
-- onunfold-next 目标 = unfold-next UF s，与源相同，可递归应用 id⇒ℱ。
id⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
     → {F : Cosmos C FC} → F ⇒ℱ F
id⇒ℱ {F = F} .out = record
  { shapeTrans    = λ p → Unfolding.pos-to-shape UF _ p
  ; morphismObj   = idMorphismObject UF
  ; morphismMor   = idMorphismMorphism UF
  ; onunfold-next = λ _ → id⇒ℱ
  }
  where UF = out F

-- Generalized composition: S₂ ∘F S₁, morphismMor via compMorphismMorphism.
-- Non-mixfix name because composite S is determined by argument types.
-- 广义复合：S 按 S₂ ∘F S₁ 封闭，morphismMor 由 compMorphismMorphism 自动导出。
-- 使用非 mixfix 名称，因为复合 S 由参数类型决定。
comp⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
       {S₁ S₂ : Functor (ShapeCat C FC) (ShapeCat C FC)}
       {F G H : Cosmos C FC}
       → G ⇒ℱ[ S₂ ] H → F ⇒ℱ[ S₁ ] G → F ⇒ℱ[ S₂ ∘F S₁ ] H
comp⇒ℱ {S₁ = S₁} {S₂ = S₂} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ p → shapeTrans (g .out) (onPos moF p)
  ; morphismObj   = compMorphismObject UF UG UH S₁ S₂ stF stG moF moG
  ; morphismMor   = compMorphismMorphism UF UG UH S₁ S₂ stF stG mmF mmG
  ; onunfold-next = λ {A} s′ →
      let A′ = proj₁ (S₁.₀ (A , s′))
          s″ = proj₂ (S₁.₀ (A , s′))
      in  comp⇒ℱ (onunfold-next (g .out) {A = A′} s″)
                 (onunfold-next (f .out) s′)
  }
  where
    open MorphismObject
    module S₁ = Functor S₁
    UF  = out F
    UG  = out G
    UH  = out H
    stF = shapeTrans (f .out)
    stG = shapeTrans (g .out)
    moF = morphismObj (f .out)
    moG = morphismObj (g .out)
    mmF = morphismMor (f .out)
    mmG = morphismMor (g .out)

-- S = id specialization of composition
-- S = id 特化的复合
_∘⇒ℱ_ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
       {F G H : Cosmos C FC}
       → G ⇒ℱ H → F ⇒ℱ G → F ⇒ℱ H
_∘⇒ℱ_ {C = C} {FC = FC} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ p → shapeTrans (g .out) (onPos moF p)
  ; morphismObj   = record
      { onPos      = λ p → onPos moG (onPos moF p)
      ; pts-compat = λ p → pts-compat moG (onPos moF p)
      }
  ; morphismMor   = record { onActP = coh }
  ; onunfold-next = λ s → (onunfold-next (g .out) s) ∘⇒ℱ (onunfold-next (f .out) s)
  }
  where
    open MorphismObject
    open MorphismMorphism
    UF = out F
    UG = out G
    UH = out H
    moF = morphismObj (f .out)
    moG = morphismObj (g .out)
    mmF = morphismMor (f .out)
    mmG = morphismMor (g .out)
    coh : ∀ {A B} (f′ : Category._⇒_ C A B) {s : ShapeOf FC A} {t : ShapeOf FC B}
        → (p : actSOf FC f′ s ≡ t) (q : PosOf FC t)
        → onPos moG (onPos moF (actPOf FC f′ s (subst (PosOf FC) (sym p) q)))
          ≡ actP-from-S FC FC id f′ p (onPos moG (onPos moF q))
    coh f′ p q = trans (cong (onPos moG) (onActP mmF f′ p q))
                       (onActP mmG f′ p (onPos moF q))

-- UnitCosmos: Trivial One-Object Cosmos
-- UnitCosmos：平凡单对象宇宙
-- The terminal category with one object and one morphism
-- 只有一个对象和一个态射的终范畴
UnitCat : ∀ {ℓ} → Category ℓ ℓ ℓ
UnitCat = record
  { Obj = ⊤
  ; _⇒_ = λ _ _ → ⊤
  ; _≈_ = λ _ _ → ⊤
  ; id = tt
  ; _∘_ = λ _ _ → tt
  ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
  ; ∘-resp-≈ = λ _ _ → tt
  ; assoc = tt
  ; sym-assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; identity² = tt
  }

-- The constant functor picking the unit container (⊤, λ _ → ⊤)
-- 选取单位容器 (⊤, λ _ → ⊤) 的常值函子
UnitContainerFunctor : ∀ {ℓ} → Functor (UnitCat {ℓ}) (ContCat ℓ ℓ)
UnitContainerFunctor = record
  { F₀ = λ _ → record { Shape = ⊤; Position = λ _ → ⊤ }
  ; F₁ = λ _ → record { shape = λ _ → tt; position = λ _ → tt }
  ; identity = ≈M-refl
  ; homomorphism = ≈M-refl
  ; F-resp-≈ = λ _ → ≈M-refl
  }

-- The trivial Cosmos: a single point unfolding into itself forever
-- 平凡宇宙：一个永远展开为自身的单点
UnitCosmos : ∀ {ℓ} → Cosmos (UnitCat {ℓ}) UnitContainerFunctor
UnitCosmos .out = record
  { unfoldFunctor = record
    { F₀ = proj₁
    ; F₁ = proj₁
    ; identity = Category.Equiv.refl UnitCat
    ; homomorphism = Category.Equiv.refl UnitCat
    ; F-resp-≈ = λ p → p
    }
  ; unfold-next = λ _ → UnitCosmos
  ; pos-to-shape = λ _ _ → tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- Unfolding Functor: Sets → Setoids
-- Unfolding 函子：Sets → Setoids
module CosmosFFunctor {o h e s p : Level}
                      {C : Category o h e}
                      {FC : Functor C (ContCat s p)} where
  open CosmosMap
  private
    -- Instantiate the unfolding setoid module for the current container functor
    -- 为当前容器函子实例化展开集合模块
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {F = FC}

  -- Equivalence relation on Unfolding elements:
  -- unfolding equivalence only
  -- Unfolding 元素上的等价关系：仅基于展开结构的等价
  record _≈F_ {u v : Level} (X : Setoid u v)
              (c₁ c₂ : Unfolding FC (Setoid.Carrier X))
              : Set (o ⊔ s ⊔ p ⊔ v) where
    field
      unfolding-eq : US._≈U_ {X = X} c₁ c₂

  -- Equivalence proofs for ≈F
  -- ≈F 的等价性证明
  ≈F-refl : {u v : Level} {X : Setoid u v} → Reflexive (_≈F_ X)
  ≈F-refl {X = X} = record
    { unfolding-eq = US.≈U-refl {X = X}
    }

  ≈F-sym : {u v : Level} {X : Setoid u v} → Symmetric (_≈F_ X)
  ≈F-sym {X = X} (record { unfolding-eq = ue }) = record
    { unfolding-eq = US.≈U-sym X ue
    }

  ≈F-trans : {u v : Level} {X : Setoid u v} → Transitive (_≈F_ X)
  ≈F-trans {X = X} (record { unfolding-eq = ue₁ })
                  (record { unfolding-eq = ue₂ }) = record
    { unfolding-eq = US.≈U-trans X ue₁ ue₂
    }

  -- Unfolding as a Setoid: carrier is Unfolding, equivalence is ≈F
  -- 将 Unfolding 视为 Setoid：载体为 Unfolding，等价为 ≈F
  CosmosFSetoid : {u v : Level} → Setoid u v
                → Setoid (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
                          (o ⊔ s ⊔ p ⊔ v)
  CosmosFSetoid X = record
    { Carrier       = Unfolding FC (Setoid.Carrier X)
    ; _≈_           = _≈F_ X
    ; isEquivalence = record
      { refl  = ≈F-refl {X = X}
      ; sym   = ≈F-sym {X = X}
      ; trans = ≈F-trans {X = X}
      }
    }

  -- mapCosmosF respects the equivalence ≈F
  -- mapCosmosF 保持等价关系 ≈F
  mapCosmosF-resp : {u v : Level} {X Y : Setoid u v} → Func X Y
                  → Func (CosmosFSetoid X) (CosmosFSetoid Y)
  mapCosmosF-resp {X = X} {Y = Y} f = record
    { to   = λ c → mapCosmosF (Func.to f) c
    ; cong = helper
    }
    where
      helper : {c₁ c₂ : Unfolding FC _} → _≈F_ X c₁ c₂
             → _≈F_ Y (mapCosmosF (Func.to f) c₁) (mapCosmosF (Func.to f) c₂)
      helper (record { unfolding-eq = ue }) = record
        { unfolding-eq = Func.cong (US.mapUnfolding-resp {X = X} {Y = Y} f) ue
        }

  -- The Unfolding functor: Sets u → Setoids
  -- Unfolding 函子：Sets u → Setoids
  toStdFunc : {u : Level} {X Y : Set u} → (X → Y) → Func (setoid X) (setoid Y)
  toStdFunc f = record { to = f ; cong = cong f }

  cosmosFFunctor : (u : Level)
    → Functor (Sets u)
              (Setoids (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
                       (o ⊔ s ⊔ p ⊔ u))
  cosmosFFunctor u = record
    { F₀           = λ X → CosmosFSetoid (setoid X)
    ; F₁           = λ f → mapCosmosF-resp (toStdFunc f)
    ; identity     = λ {X} → ≈F-refl {X = setoid X}
    ; homomorphism = λ {X Y Z} {f g} → ≈F-refl {X = setoid Z}
    ; F-resp-≈ = λ {X Y} {f g} f≈g {c} → record
        { unfolding-eq = US.mapUnfolding-resp-≈ X Y f g (λ {x} → f≈g x) US.≈U-refl
        }
    }
