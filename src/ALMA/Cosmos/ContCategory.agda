------------------------------------------------------------------------
-- The category of containers
--
-- Defines the equivalence _≈M_ on containers (polynomial functors)
-- (propositional equality of shapes, heterogeneous equality of positions
-- via transport), verifies the category laws, and constructs a Category instance.
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCategory where

open import Agda.Primitive using (_⊔_; lsuc; Level)
open import Categories.Category using (Category)
open import Data.Container using (_⇒_; Container; Position; Shape)
open import Data.Container.Morphism using (_∘_; id)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-subst; subst-subst-sym)

-- The equivalence relation on morphisms: equal on shapes, and on positions up to transport
infix 4 _≈M_
record _≈M_ {s p : Level} {C D : Container s p} (f g : C ⇒ D) : Set (s ⊔ p) where
  private
    module f = _⇒_ f
    module g = _⇒_ g
  field
    shape-eq : ∀ (s : Shape C) → f.shape s ≡ g.shape s
    pos-eq   : ∀ (s : Shape C) (p : Position D (f.shape s))
               → f.position {s} p ≡ g.position {s} (subst (Position D) (shape-eq s) p)

-- Reflexivity of _≈M_
≈M-refl : ∀ {s p} {C D : Container s p} {f : C ⇒ D} → f ≈M f
≈M-refl = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }

-- Symmetry of _≈M_
≈M-sym : ∀ {s p} {C D : Container s p} {f g : C ⇒ D} → f ≈M g → g ≈M f
≈M-sym {s} {p} {C} {D} {f} {g} eq = record
  { shape-eq = shape-sym
  ; pos-eq   = pos-sym
  }
  where
    module f = _⇒_ f
    module g = _⇒_ g
    open _≈M_ eq
    shape-sym : ∀ (s : Shape C) → g.shape s ≡ f.shape s
    shape-sym s = sym (shape-eq s)
    pos-sym : ∀ (s : Shape C) (q : Position D (g.shape s))
              → g.position {s} q ≡ f.position {s} (subst (Position D) (shape-sym s) q)
    pos-sym s q =
      let
        p : Position D (f.shape s)
        p = subst (Position D) (sym (shape-eq s)) q
        eq-fwd : f.position {s} p ≡ g.position {s} (subst (Position D) (shape-eq s) p)
        eq-fwd = pos-eq s p
        subst-cancel : subst (Position D) (shape-eq s) p ≡ q
        subst-cancel = subst-subst-sym (shape-eq s)
        eq-g-cong : g.position {s} (subst (Position D) (shape-eq s) p) ≡ g.position {s} q
        eq-g-cong = cong (g.position {s}) subst-cancel
        eq-f-to-g : f.position {s} p ≡ g.position {s} q
        eq-f-to-g = trans eq-fwd eq-g-cong
      in
      sym eq-f-to-g

-- Transitivity of _≈M_
≈M-trans : ∀ {s p} {C D : Container s p} {f g h : C ⇒ D} → f ≈M g → g ≈M h → f ≈M h
≈M-trans {s} {p} {C} {D} {f} {g} {h} eq-fg eq-gh = record
  { shape-eq = shape-trans
  ; pos-eq   = pos-trans
  }
  where
    module f = _⇒_ f
    module g = _⇒_ g
    module h = _⇒_ h
    open _≈M_ eq-fg renaming (shape-eq to shape-fg; pos-eq to pos-fg)
    open _≈M_ eq-gh renaming (shape-eq to shape-gh; pos-eq to pos-gh)
    shape-trans : ∀ (s : Shape C) → f.shape s ≡ h.shape s
    shape-trans s = trans (shape-fg s) (shape-gh s)
    pos-trans : ∀ (s : Shape C) (p : Position D (f.shape s))
                → f.position {s} p ≡ h.position {s} (subst (Position D) (shape-trans s) p)
    pos-trans s p =
      let
        q : Position D (g.shape s)
        q = subst (Position D) (shape-fg s) p
        step1 : f.position {s} p ≡ g.position {s} q
        step1 = pos-fg s p
        step2 : g.position {s} q ≡ h.position {s} (subst (Position D) (shape-gh s) q)
        step2 = pos-gh s q
        subst-merge : subst (Position D) (shape-trans s) p ≡ subst (Position D) (shape-gh s) q
        subst-merge = sym (subst-subst (shape-fg s) {shape-gh s})
        step3 : h.position {s} (subst (Position D) (shape-gh s) q)
                ≡ h.position {s} (subst (Position D) (shape-trans s) p)
        step3 = cong (h.position {s}) (sym subst-merge)
      in
      trans step1 (trans step2 step3)

-- _≈M_ is an equivalence relation
≈M-isEquiv : ∀ {s p} {C D : Container s p} → IsEquivalence (_≈M_ {s} {p} {C} {D})
≈M-isEquiv = record
  { refl  = ≈M-refl
  ; sym   = ≈M-sym
  ; trans = ≈M-trans
  }

-- Associativity of composition
∘M-assoc : ∀ {s p} {A B C D : Container s p}
           {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
         → (h ∘ g) ∘ f ≈M h ∘ (g ∘ f)
∘M-assoc = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }

-- Left identity law
∘M-identityˡ : ∀ {s p} {A B : Container s p} {f : A ⇒ B} → id B ∘ f ≈M f
∘M-identityˡ = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }

-- Right identity law
∘M-identityʳ : ∀ {s p} {A B : Container s p} {f : A ⇒ B} → f ∘ id A ≈M f
∘M-identityʳ = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }

-- Composition respects equivalence
∘M-resp-≈ : ∀ {s p} {A B C : Container s p}
            {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
          → g₁ ≈M g₂ → f₁ ≈M f₂ → g₁ ∘ f₁ ≈M g₂ ∘ f₂
∘M-resp-≈ {s} {p} {A} {B} {C} {g₁} {g₂} {f₁} {f₂} eq-g eq-f = record
  { shape-eq = shape-compat
  ; pos-eq   = pos-compat
  }
  where
    module f₁ = _⇒_ f₁
    module f₂ = _⇒_ f₂
    module g₁ = _⇒_ g₁
    module g₂ = _⇒_ g₂
    open _≈M_ eq-g renaming (shape-eq to g-shape; pos-eq to g-pos)
    open _≈M_ eq-f renaming (shape-eq to f-shape; pos-eq to f-pos)
    shape-compat : ∀ (s : Shape A) → g₁.shape (f₁.shape s) ≡ g₂.shape (f₂.shape s)
    shape-compat s = trans (g-shape (f₁.shape s)) (cong g₂.shape (f-shape s))
    swap-onPos : ∀ {t₁ t₂ : Shape B} (eq : t₁ ≡ t₂) (q : Position C (g₂.shape t₁))
                → subst (Position B) eq (g₂.position {t₁} q)
                ≡ g₂.position {t₂} (subst (Position C) (cong g₂.shape eq) q)
    swap-onPos refl q = refl
    pos-compat : ∀ (s : Shape A) (p : Position C (g₁.shape (f₁.shape s)))
                → f₁.position {s} (g₁.position {f₁.shape s} p)
                ≡ f₂.position {s} (g₂.position {f₂.shape s} (subst (Position C) (shape-compat s) p))
    pos-compat s p =
      let
        t₁ : Shape B
        t₁ = f₁.shape s
        t₂ : Shape B
        t₂ = f₂.shape s
        eq-t : t₁ ≡ t₂
        eq-t = f-shape s
        step-g : g₁.position {t₁} p ≡ g₂.position {t₁} (subst (Position C) (g-shape t₁) p)
        step-g = g-pos t₁ p
        q1 : Position C (g₂.shape t₁)
        q1 = subst (Position C) (g-shape t₁) p
        step-swap : subst (Position B) eq-t (g₂.position {t₁} q1)
                   ≡ g₂.position {t₂} (subst (Position C) (cong g₂.shape eq-t) q1)
        step-swap = swap-onPos eq-t q1
        q2 : Position C (g₂.shape t₂)
        q2 = subst (Position C) (cong g₂.shape eq-t) q1
        subst-merge : subst (Position C) (shape-compat s) p ≡ q2
        subst-merge = sym (subst-subst (g-shape t₁) {cong g₂.shape eq-t} {p})
        g-eq : subst (Position B) eq-t (g₁.position {t₁} p)
               ≡ g₂.position {t₂} (subst (Position C) (shape-compat s) p)
        g-eq = trans
                (cong (subst (Position B) eq-t) step-g)
                (trans step-swap (cong (g₂.position {t₂}) (sym subst-merge)))
        step-f : f₁.position {s} (g₁.position {t₁} p)
                ≡ f₂.position {s} (subst (Position B) eq-t (g₁.position {t₁} p))
        step-f = f-pos s (g₁.position {t₁} p)
      in
      trans step-f (cong (f₂.position {s}) g-eq)

-- Left whiskering: g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
∘M-resp-≈ˡ : ∀ {s p} {A B C : Container s p} {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
           → g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
∘M-resp-≈ˡ {f = f} g₁≈g₂ = ∘M-resp-≈ g₁≈g₂ (≈M-refl {f = f})

-- Right whiskering: f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
∘M-resp-≈ʳ : ∀ {s p} {A B C : Container s p} {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
           → f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
∘M-resp-≈ʳ {g = g} f₁≈f₂ = ∘M-resp-≈ (≈M-refl {f = g}) f₁≈f₂

-- Pack everything into a Category instance
ContCat : (s p : Level) → Category (lsuc s ⊔ lsuc p) (s ⊔ p) (s ⊔ p)
ContCat s p = record
  { Obj       = Container s p
  ; _⇒_       = _⇒_
  ; _≈_       = _≈M_
  ; id        = λ {A} → id A
  ; _∘_       = _∘_
  ; equiv     = ≈M-isEquiv
  ; ∘-resp-≈  = ∘M-resp-≈
  ; assoc     = λ {A B C D f g h} → ∘M-assoc {s} {p} {A} {B} {C} {D} {f} {g} {h}
  ; sym-assoc = λ {A B C D f g h} → ≈M-sym (∘M-assoc {s} {p} {A} {B} {C} {D} {f} {g} {h})
  ; identityˡ = ∘M-identityˡ
  ; identityʳ = ∘M-identityʳ
  ; identity² = λ {A} → ∘M-identityˡ {f = id A}
  }
