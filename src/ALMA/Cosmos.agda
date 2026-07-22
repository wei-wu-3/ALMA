------------------------------------------------------------------------
-- ALMA — Infinite, Unbounded, Self-Referential Dynamic Cosmos
--
-- Built with type theory, category theory, containers, and coalgebraic unfolding
-- Cosmos is the terminal coalgebra of a polynomial functor internalized in type theory
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; isEquivalence; setoid)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Container.Core using (shape)
open import Function using (Func; id; _∘_)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Elements using (Elements)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)

open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; unitorʳ)

open import ALMA.Cosmos.ContCategory using (≈M-refl; ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat; ContCatEquiv)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquivFunctor
  using (ContCatEquivFunctor; idContCatEquivFunctor; compContCatEquivFunctor; module ShapeCatMorphism)
open import ALMA.Cosmos.Unfolding
  using (Unfolding; mapUnfolding; mapUnfolding-id; mapUnfolding-∘; module UnfoldingSetoid)
open import ALMA.Cosmos.MorphismObject
  using (MorphismObject; idMorphismObject; compMorphismObject)
open import ALMA.Cosmos.MorphismMorphism
  using (MorphismMorphism; idMorphismMorphism; compMorphismMorphism; actP-from-S)

-- Core Definitions: CosmosF and Cosmos as Terminal Coalgebra
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

record Cosmos {o h e s p : Level}
              (C : Category o h e)
              (FC : Functor C (ContCat s p))
              : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
  coinductive
  field
    out : CosmosF C FC (Cosmos C FC)
open Cosmos public

-- Lightweight Functoriality of CosmosF
module CosmosMap {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)} where
  mapCosmosF : ∀ {x y : Level} {X : Set x} {Y : Set y}
            → (X → Y) → CosmosF C FC X → CosmosF C FC Y
  mapCosmosF f c = record { unfoldingCore = mapUnfolding f (unfoldingCore c) }
  map-id : ∀ {x : Level} {X : Set x} (c : CosmosF C FC X)
        → mapCosmosF (λ x → x) c ≡ c
  map-id c = cong (λ u → record { unfoldingCore = u }) (mapUnfolding-id (unfoldingCore c))
  map-∘ : ∀ {x y z : Level} {X : Set x} {Y : Set y} {Z : Set z}
            (f : Y → Z) (g : X → Y) (c : CosmosF C FC X)
        → mapCosmosF (f ∘ g) c ≡ mapCosmosF f (mapCosmosF g c)
  map-∘ f g c =
    cong (λ u → record { unfoldingCore = u })
        (mapUnfolding-∘ f g (unfoldingCore c))
  map-cong : ∀ {x y : Level} {X : Set x} {Y : Set y}
          → {f g : X → Y} → f ≡ g → mapCosmosF f ≡ mapCosmosF g
  map-cong refl = refl

-- Universe Morphisms: Coalgebra Homomorphisms
mutual
  record _⇒ℱ_ {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
             (F G : Cosmos C FC)
             : Set (o ⊔ h ⊔ s ⊔ p) where
    coinductive
    field
      out : ⇒ℱLayer F G

  record ⇒ℱLayer {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
                (F G : Cosmos C FC)
                : Set (o ⊔ h ⊔ s ⊔ p) where
    inductive
    private
      module C = Category C
      UF = unfoldingCore (out F)
      UG = unfoldingCore (out G)
      S : Functor (ShapeCat C FC) (ShapeCat C FC)
      S = idF
      actP : ∀ {A B} (f : C._⇒_ A B) (s : ShapeOf FC A)
           → PosOf FC (proj₂ (Functor.₀ S (B , actSOf FC f s)))
           → PosOf FC (proj₂ (Functor.₀ S (A , s)))
      actP f s = actPOf FC f s
    field
      shapeTrans  : ∀ {A} {s : ShapeOf FC A}
                  → PosOf FC s
                  → ShapeOf FC (Functor.₀ (Unfolding.unfoldFunctor UG) (Functor.₀ S (A , s)))
      morphismObj : MorphismObject UF UG S shapeTrans
      morphismMor : MorphismMorphism UF UG S shapeTrans morphismObj actP
      onunfold-next : ∀ {A} (s : ShapeOf FC A)
                    → Unfolding.unfold-next UF s ⇒ℱ Unfolding.unfold-next UG (proj₂ (Functor.₀ S (A , s)))
open _⇒ℱ_ public
open ⇒ℱLayer public

-- Identity coalgebra homomorphism
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
    open import Relation.Binary.PropositionalEquality using (trans; cong)
    UF = unfoldingCore (out F)
    UG = unfoldingCore (out G)
    UH = unfoldingCore (out H)
    moF = morphismObj (f .out)
    moG = morphismObj (g .out)
    mmF = morphismMor (f .out)
    mmG = morphismMor (g .out)
    coh : ∀ {A B} (f′ : Category._⇒_ C A B) (s′ : ShapeOf FC A)
        → (p : PosOf FC (actSOf FC f′ s′))
        → onPos moG (onPos moF (actPOf FC f′ s′ p))
          ≡ actPOf FC f′ s′ (onPos moG (onPos moF p))
    coh f′ s′ p = trans (cong (onPos moG) (onActP mmF f′ s′ p))
                        (onActP mmG f′ s′ (onPos moF p))

-- UnitCosmos: Trivial One-Object Cosmos
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

UnitContainerFunctor : ∀ {ℓ} → Functor (UnitCat {ℓ}) (ContCat ℓ ℓ)
UnitContainerFunctor = record
  { F₀ = λ _ → record { Shape = ⊤; Position = λ _ → ⊤ }
  ; F₁ = λ _ → record { shape = λ _ → tt; position = λ _ → tt }
  ; identity = ≈M-refl
  ; homomorphism = ≈M-refl
  ; F-resp-≈ = λ _ → ≈M-refl
  }

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
module CosmosFFunctor {o h e s p : Level}
                      {C : Category o h e}
                      {FC : Functor C (ContCat s p)} where
  open CosmosMap
  open import Categories.Category.Instance.Setoids using (Setoids)
  open import Function using (Func) renaming (id to idFunc; _∘_ to _∘Func_)
  private
    module US {u : Level} = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {u = u} {C = C} {F = FC}
  -- Equivalence relation on CosmosF elements
  record _≈F_ {u : Level} (X : Setoid u u)
              (c₁ c₂ : CosmosF C FC (Setoid.Carrier X))
              : Set (lsuc o ⊔ lsuc h ⊔ lsuc e ⊔ lsuc s ⊔ lsuc p ⊔ lsuc u) where
    field
      contEquiv-eq : contEquiv c₁ ≡ contEquiv c₂
      unfolding-eq : US._≈U_ {X = X} (unfoldingCore c₁) (unfoldingCore c₂)
  -- Equivalence proofs
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
  -- CosmosF as a Setoid
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
  -- mapCosmosF respects the equivalence
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
  -- The CosmosF functor
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
