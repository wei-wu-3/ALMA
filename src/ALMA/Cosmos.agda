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

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id)

open import ALMA.Cosmos.ContCategory using (≈M-refl; ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat; ContCatEquiv)
open import ALMA.Cosmos.Unfolding
  using (Unfolding; mapUnfolding; mapUnfolding-id; mapUnfolding-∘; module UnfoldingSetoid)
open import ALMA.Cosmos.MorphismObject using (MorphismObject; idMorphismObject)
open import ALMA.Cosmos.MorphismMorphism using (MorphismMorphism; idMorphismMorphism)

-- Core Definitions: CosmosF and Cosmos as Terminal Coalgebra
-- 核心定义：CosmosF 与作为终余代数的 Cosmos
-- One-layer unfolding of Cosmos: a container-shaped functorial structure
-- over a parameter X, equipped with a container equivalence witness
-- Cosmos 的单层展开：在参数 X 上的容器形状函子结构，
-- 附带容器等价见证
record CosmosF {o h e s p x : Level}
               (C : Category o h e)
               (FC : Functor C (ContCat s p))
               (X : Set x)
               : Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ x) where
  field
    unfoldingCore : Unfolding FC X

  contEquiv : ContCatEquiv C FC
  contEquiv = record {}
open CosmosF public

-- Cosmos: the terminal coalgebra of the polynomial functor CosmosF
-- Defined coinductively: out : Cosmos → CosmosF (Cosmos)
-- Cosmos：多项式函子 CosmosF 的终余代数
-- 以余归纳定义：out : Cosmos → CosmosF (Cosmos)
record Cosmos {o h e s p : Level}
              (C : Category o h e)
              (FC : Functor C (ContCat s p))
              : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
  coinductive
  field
    out : CosmosF C FC (Cosmos C FC)
open Cosmos public

-- Lightweight Functoriality of CosmosF
-- CosmosF 的轻量函子性
module CosmosMap {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)} where
  -- Functorial action on the parameter: map along X → Y
  -- 参数上的函子作用：沿 X → Y 映射
  mapCosmosF : ∀ {x y : Level} {X : Set x} {Y : Set y}
            → (X → Y) → CosmosF C FC X → CosmosF C FC Y
  mapCosmosF f c = record { unfoldingCore = mapUnfolding f (unfoldingCore c) }
  -- Identity law: mapCosmosF id ≡ id
  -- 恒等律：mapCosmosF id ≡ id
  map-id : ∀ {x : Level} {X : Set x} (c : CosmosF C FC X)
        → mapCosmosF (λ x → x) c ≡ c
  map-id c = cong (λ u → record { unfoldingCore = u }) (mapUnfolding-id (unfoldingCore c))
  -- Composition law: mapCosmosF (f ∘ g) ≡ mapCosmosF f ∘ mapCosmosF g
  -- 复合律：mapCosmosF (f ∘ g) ≡ mapCosmosF f ∘ mapCosmosF g
  map-∘ : ∀ {x y z : Level} {X : Set x} {Y : Set y} {Z : Set z}
            (f : Y → Z) (g : X → Y) (c : CosmosF C FC X)
        → mapCosmosF (f ∘ g) c ≡ mapCosmosF f (mapCosmosF g c)
  map-∘ f g c =
    cong (λ u → record { unfoldingCore = u })
        (mapUnfolding-∘ f g (unfoldingCore c))
  -- Congruence: pointwise equal functions induce equal maps
  -- 合同性：逐点相等的函数诱导相等的映射
  map-cong : ∀ {x y : Level} {X : Set x} {Y : Set y}
          → {f g : X → Y} → f ≡ g → mapCosmosF f ≡ mapCosmosF g
  map-cong refl = refl

-- Universe Morphisms: Coalgebra Homomorphisms
-- 宇宙态射：余代数同态
-- A coalgebra homomorphism F ⇒ℱ G between two Cosmos instances,
-- defined coinductively via a one-layer inductive record ⇒ℱLayer
-- 两个 Cosmos 实例之间的余代数同态 F ⇒ℱ G，
-- 通过单层归纳记录 ⇒ℱLayer 以余归纳方式定义
mutual
  record _⇒ℱ_ {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
             (F G : Cosmos C FC)
             : Set (o ⊔ h ⊔ s ⊔ p) where
    coinductive
    field
      out : ⇒ℱLayer F G

  -- One layer of a coalgebra homomorphism:
  -- shape translation, morphism object/morphism, and recursive step
  -- 余代数同态的单层结构：
  -- 形状翻译、态射对象/态射，以及递归步骤
  record ⇒ℱLayer {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
                (F G : Cosmos C FC)
                : Set (o ⊔ h ⊔ s ⊔ p) where
    inductive
    private
      module C = Category C
      UF = unfoldingCore (out F)
      UG = unfoldingCore (out G)
      S : Functor (ShapeCat C FC) (ShapeCat C FC)
      S = id
      actP : ∀ {A B} (f : C._⇒_ A B) (s : ShapeOf FC A)
           → PosOf FC (proj₂ (Functor.₀ S (B , actSOf FC f s)))
           → PosOf FC (proj₂ (Functor.₀ S (A , s)))
      actP f s = actPOf FC f s
    field
      -- Shape translation: map positions of F to shapes of G
      -- 形状翻译：将 F 的位置映射为 G 的形状
      shapeTrans  : ∀ {A} {s : ShapeOf FC A}
                  → PosOf FC s
                  → ShapeOf FC (Functor.₀ (Unfolding.unfoldFunctor UG) (Functor.₀ S (A , s)))
      -- Morphism object: position-level mapping compatible with shape translation
      -- 态射对象：与形状翻译相容的位置级映射
      morphismObj : MorphismObject UF UG S shapeTrans
      -- Morphism morphism: coherence with the position action actP
      -- 态射的态射：与位置作用 actP 的融贯性
      morphismMor : MorphismMorphism UF UG S shapeTrans morphismObj actP
      -- Recursive step: homomorphism on the next unfolding layer
      -- 递归步骤：下一展开层上的同态
      onunfold-next : ∀ {A} (s : ShapeOf FC A)
                    → Unfolding.unfold-next UF s ⇒ℱ Unfolding.unfold-next UG (proj₂ (Functor.₀ S (A , s)))
open _⇒ℱ_ public
open ⇒ℱLayer public

-- Identity coalgebra homomorphism
-- 恒等余代数同态
id⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
     → {F : Cosmos C FC} → F ⇒ℱ F
id⇒ℱ {F = F} .out = record
  { shapeTrans    = λ p → Unfolding.pos-to-shape UF _ p
  ; morphismObj   = idMorphismObject UF
  ; morphismMor   = idMorphismMorphism UF
  ; onunfold-next = λ _ → id⇒ℱ
  }
  where UF = unfoldingCore (out F)

-- Composition of coalgebra homomorphisms
-- 余代数同态的复合
_∘⇒ℱ_ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
       → {F G H : Cosmos C FC} → G ⇒ℱ H → F ⇒ℱ G → F ⇒ℱ H
_∘⇒ℱ_ {o} {h} {e} {s} {p} {C} {FC} {F = F} {G} {H} g f .out = record
  { shapeTrans    = λ p → shapeTrans (g .out) (onPos moF p)
  ; morphismObj   = record
      { onPos      = λ p → onPos moG (onPos moF p)
      ; pts-compat = λ p → pts-compat moG (onPos moF p)
      }
  ; morphismMor   = record { onActP = coh }
  ; onunfold-next = λ s →
      (onunfold-next (g .out) _) ∘⇒ℱ (onunfold-next (f .out) s)
  }
  where
    open MorphismObject
    open MorphismMorphism
    UF = unfoldingCore (out F)
    UG = unfoldingCore (out G)
    UH = unfoldingCore (out H)
    moF = morphismObj (f .out)
    moG = morphismObj (g .out)
    mmF = morphismMor (f .out)
    mmG = morphismMor (g .out)
    -- Coherence of composed position action with actP
    -- 复合位置作用与 actP 的融贯性
    coh : ∀ {A B} (f′ : Category._⇒_ C A B) (s′ : ShapeOf FC A)
        → (p : PosOf FC (actSOf FC f′ s′))
        → onPos moG (onPos moF (actPOf FC f′ s′ p))
          ≡ actPOf FC f′ s′ (onPos moG (onPos moF p))
    coh f′ s′ p = trans (cong (onPos moG) (onActP mmF f′ s′ p))
                        (onActP mmG f′ s′ (onPos moF p))

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
  { unfoldingCore = record
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
  }

-- StrictSets Category
-- 严格集合范畴
-- The category of strict (proof-irrelevant) sets at level ℓ,
-- with pointwise propositional equality as morphism equivalence
-- 层级 ℓ 上的严格（证明无关）集合范畴，
-- 态射等价取逐点命题相等
StrictSets : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
StrictSets ℓ = record
  { Obj       = Set ℓ
  ; _⇒_       = λ A B → A → B
  ; _≈_       = λ f g → ∀ {x} → f x ≡ g x
  ; id        = λ x → x
  ; _∘_       = λ g f x → g (f x)
  ; assoc     = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv     = record
    { refl  = refl
    ; sym   = λ eq → sym eq
    ; trans = λ eq₁ eq₂ → trans eq₁ eq₂
    }
  ; ∘-resp-≈  = λ {_ _ _ h i f g} eq₁ eq₂ {x} → trans (eq₁ {f x}) (cong i (eq₂ {x}))
  }

-- CosmosF Functor: StrictSets → Setoids
-- CosmosF 函子：StrictSets → Setoids
module CosmosFFunctor {o h e s p : Level}
                      {C : Category o h e}
                      {FC : Functor C (ContCat s p)} where
  open CosmosMap
  private
    module US {u : Level} = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {u = u} {C = C} {F = FC}
  -- Equivalence relation on CosmosF elements:
  -- equality of container equivalence witnesses and unfolding equivalence
  -- CosmosF 元素上的等价关系：
  -- 容器等价见证的相等与展开等价
  record _≈F_ {u : Level} (X : Setoid u u)
              (c₁ c₂ : CosmosF C FC (Setoid.Carrier X))
              : Set (lsuc o ⊔ lsuc h ⊔ lsuc e ⊔ lsuc s ⊔ lsuc p ⊔ lsuc u) where
    field
      contEquiv-eq : contEquiv c₁ ≡ contEquiv c₂
      unfolding-eq : US._≈U_ {X = X} (unfoldingCore c₁) (unfoldingCore c₂)
  -- Equivalence proofs for ≈F
  -- ≈F 的等价性证明
  ≈F-refl : {u : Level} {X : Setoid u u} → Reflexive (_≈F_ X)
  ≈F-refl {X = X} = record
    { contEquiv-eq = refl
    ; unfolding-eq = US.≈U-refl {X = X}
    }
  ≈F-sym : {u : Level} {X : Setoid u u} → Symmetric (_≈F_ X)
  ≈F-sym {X = X} (record { contEquiv-eq = ce ; unfolding-eq = ue }) = record
    { contEquiv-eq = sym ce
    ; unfolding-eq = US.≈U-sym X ue
    }
  ≈F-trans : {u : Level} {X : Setoid u u} → Transitive (_≈F_ X)
  ≈F-trans {X = X} (record { contEquiv-eq = ce₁ ; unfolding-eq = ue₁ })
                  (record { contEquiv-eq = ce₂ ; unfolding-eq = ue₂ }) = record
    { contEquiv-eq = trans ce₁ ce₂
    ; unfolding-eq = US.≈U-trans X ue₁ ue₂
    }
  -- CosmosF as a Setoid: carrier is CosmosF, equivalence is ≈F
  -- 将 CosmosF 视为 Setoid：载体为 CosmosF，等价为 ≈F
  CosmosFSetoid : (u : Level) → Setoid u u
                → Setoid (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
                         (lsuc o ⊔ lsuc h ⊔ lsuc e ⊔ lsuc s ⊔ lsuc p ⊔ lsuc u)
  CosmosFSetoid u X = record
    { Carrier       = CosmosF C FC (Setoid.Carrier X)
    ; _≈_           = _≈F_ X
    ; isEquivalence = record
      { refl  = ≈F-refl {X = X}
      ; sym   = ≈F-sym {X = X}
      ; trans = ≈F-trans {X = X}
      }
    }
  -- mapCosmosF respects the equivalence ≈F
  -- mapCosmosF 保持等价关系 ≈F
  mapCosmosF-resp : {u : Level} {X Y : Setoid u u} → Func X Y
                  → Func (CosmosFSetoid u X) (CosmosFSetoid u Y)
  mapCosmosF-resp {X = X} {Y = Y} f = record
    { to   = λ c → mapCosmosF (Func.to f) c
    ; cong = helper
    }
    where
      helper : {c₁ c₂ : CosmosF C FC _} → _≈F_ X c₁ c₂
            → _≈F_ Y (mapCosmosF (Func.to f) c₁) (mapCosmosF (Func.to f) c₂)
      helper (record { unfolding-eq = ue }) = record
        { contEquiv-eq = refl
        ; unfolding-eq = Func.cong (US.mapUnfolding-resp X Y f) ue
        }
  -- The CosmosF functor: StrictSets u → Setoids
  -- CosmosF 函子：StrictSets u → Setoids
  toStdFunc : {u : Level} {X Y : Set u} → (X → Y) → Func (setoid X) (setoid Y)
  toStdFunc f = record { to = f ; cong = cong f }
  cosmosFFunctor : (u : Level)
                → Functor (StrictSets u)
                          (Setoids (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
                                    (lsuc o ⊔ lsuc h ⊔ lsuc e ⊔ lsuc s ⊔ lsuc p ⊔ lsuc u))
  cosmosFFunctor u = record
    { F₀           = λ X → CosmosFSetoid u (setoid X)
    ; F₁           = λ f → mapCosmosF-resp (toStdFunc f)
    ; identity     = λ {X} → ≈F-refl {X = setoid X}
    ; homomorphism = λ {X Y Z} {f g} → ≈F-refl {X = setoid Z}
    ; F-resp-≈     = λ {X Y} {f g} f≈g {c} → record
        { contEquiv-eq = refl
        ; unfolding-eq = US.mapUnfolding-resp-≈ X Y f g f≈g US.≈U-refl
        }
    }
