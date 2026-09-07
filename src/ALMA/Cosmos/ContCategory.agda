------------------------------------------------------------------------
-- The category of containers (polynomial functors)
-- 容器（多项式函子）范畴
--
-- Defines the equivalence _≈M_ on morphisms between containers (polynomial functors)
-- (pointwise propositional equality of the shape maps, equality of position
-- components up to transport along the shape equality), verifies the category
-- laws, and constructs a Category instance
-- 定义容器（多项式函子）态射上的等价关系 _≈M_
-- （形状函数逐点命题相等，位置分量经传输（subst）后取命题相等），
-- 验证范畴公理，并构造 Category 实例
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.ContCategory where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≗_; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-subst; subst-subst-sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Container.Core using (Container; Shape; Position; _⇒_)
open import Data.Container.Morphism using (id; _∘_)

open import Categories.Category.Core using (Category)

-- The equivalence relation on morphisms: pointwise equal on shape maps, and on positions up to transport
-- 态射上的等价关系：形状分量逐点相等，位置分量在传输意义下相等
module _ {s p} {C D : Container s p} where
  infix 4 _≈M_
  record _≈M_ (f g : C ⇒ D) : Set (s ⊔ p) where
    private
      module f = _⇒_ f
      module g = _⇒_ g
    field
      shape-eq : f.shape ≗ g.shape
      pos-eq   : ∀ (s : Shape C) (p : Position D (f.shape s))
                → f.position {s} p ≡ g.position {s} (subst (Position D) (shape-eq s) p)

  -- Reflexivity of _≈M_
  -- _≈M_ 的自反性
  ≈M-refl : ∀ {f : C ⇒ D} → f ≈M f
  ≈M-refl = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }
  -- Symmetry of _≈M_
  -- _≈M_ 的对称性
  ≈M-sym : ∀ {f g : C ⇒ D} → f ≈M g → g ≈M f
  ≈M-sym {f} {g} eq = record
    { shape-eq = λ s → sym (eq.shape-eq s)
    ; pos-eq   = λ s q → sym (begin
        F.position {s} (subst (Position D) (sym (eq.shape-eq s)) q)
          ≡⟨ eq.pos-eq s (subst (Position D) (sym (eq.shape-eq s)) q) ⟩
        G.position {s} (subst (Position D) (eq.shape-eq s) (subst (Position D) (sym (eq.shape-eq s)) q))
          ≡⟨ cong (G.position {s}) (subst-subst-sym (eq.shape-eq s)) ⟩
        G.position {s} q
          ∎)
    }
    where
      module F  = _⇒_ f
      module G  = _⇒_ g
      module eq = _≈M_ eq
  -- Transitivity of _≈M_
  -- _≈M_ 的传递性
  ≈M-trans : ∀ {f g h : C ⇒ D} → f ≈M g → g ≈M h → f ≈M h
  ≈M-trans {f} {g} {h} eq-fg eq-gh = record
    { shape-eq = λ s → trans (FG.shape-eq s) (GH.shape-eq s)
    ; pos-eq   = λ s p → begin
        F.position {s} p
          ≡⟨ FG.pos-eq s p ⟩
        G.position {s} (subst (Position D) (FG.shape-eq s) p)
          ≡⟨ GH.pos-eq s (subst (Position D) (FG.shape-eq s) p) ⟩
        H.position {s} (subst (Position D) (GH.shape-eq s) (subst (Position D) (FG.shape-eq s) p))
          ≡⟨ cong (H.position {s}) (subst-subst (FG.shape-eq s) {y≡z = GH.shape-eq s}) ⟩
        H.position {s} (subst (Position D) (trans (FG.shape-eq s) (GH.shape-eq s)) p)
          ∎
    }
    where
      module F  = _⇒_ f
      module G  = _⇒_ g
      module H  = _⇒_ h
      module FG = _≈M_ eq-fg
      module GH = _≈M_ eq-gh
  -- _≈M_ is an equivalence relation
  -- _≈M_ 构成等价关系
  ≈M-isEquiv : IsEquivalence _≈M_
  ≈M-isEquiv = record
    { refl  = ≈M-refl
    ; sym   = ≈M-sym
    ; trans = ≈M-trans
    }
  -- Equational reasoning combinators for container morphism equivalence _≈M_
  -- 容器态射等价 _≈M_ 的等式推理组合子
  module ≈M-Reasoning where
    open import Relation.Binary.Reasoning.Setoid (record
      { Carrier = C ⇒ D ; _≈_ = _≈M_ ; isEquivalence = ≈M-isEquiv })
      public

module _ {s p} {B : Container s p} {C : Container s p} where
  position-natural : ∀ (g : B ⇒ C) {t₁ t₂ : Shape B} (eq : t₁ ≡ t₂)
                    (q : Position C (_⇒_.shape g t₁)) →
                    subst (Position B) eq (_⇒_.position g {t₁} q)
                    ≡ _⇒_.position g {t₂} (subst (Position C) (cong (_⇒_.shape g) eq) q)
  position-natural g refl q = refl
-- Composition respects equivalence
-- 复合保持等价（相容性）
∘M-resp-≈ : ∀ {s p} {A B C : Container s p}
            {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
          → g₁ ≈M g₂ → f₁ ≈M f₂ → g₁ ∘ f₁ ≈M g₂ ∘ f₂
∘M-resp-≈ {s} {p} {A} {B} {C} {g₁} {g₂} {f₁} {f₂} eq-g eq-f = record
  { shape-eq = shape-compat
  ; pos-eq   = λ s p → begin
      F1.position {s} (G1.position {F1.shape s} p)
        ≡⟨ F.pos-eq s (G1.position {F1.shape s} p) ⟩
      F2.position {s} (subst (Position B) (F.shape-eq s) (G1.position {F1.shape s} p))
        ≡⟨ cong (F2.position {s}) (cong (subst (Position B) (F.shape-eq s)) (G.pos-eq (F1.shape s) p)) ⟩
      F2.position {s} (subst (Position B) (F.shape-eq s) (G2.position {F1.shape s} (subst (Position C) (G.shape-eq (F1.shape s)) p)))
        ≡⟨ cong (F2.position {s}) (position-natural g₂ (F.shape-eq s) (subst (Position C) (G.shape-eq (F1.shape s)) p)) ⟩
      F2.position {s} (G2.position {F2.shape s} (subst (Position C) (cong G2.shape (F.shape-eq s)) (subst (Position C) (G.shape-eq (F1.shape s)) p)))
        ≡⟨ cong (F2.position {s}) (cong (G2.position {F2.shape s}) (subst-subst (G.shape-eq (F1.shape s)) {y≡z = cong G2.shape (F.shape-eq s)})) ⟩
      F2.position {s} (G2.position {F2.shape s} (subst (Position C) (shape-compat s) p))
        ∎
  }
  where
    module F1 = _⇒_ f₁
    module F2 = _⇒_ f₂
    module G1 = _⇒_ g₁
    module G2 = _⇒_ g₂
    module F  = _≈M_ eq-f
    module G  = _≈M_ eq-g
    shape-compat : ∀ (s : Shape A) → G1.shape (F1.shape s) ≡ G2.shape (F2.shape s)
    shape-compat s = trans (G.shape-eq (F1.shape s)) (cong G2.shape (F.shape-eq s))
-- Left whiskering: g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
-- 左复合保持等价：g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
∘M-resp-≈ˡ : ∀ {s p} {A B C : Container s p} {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
           → g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
∘M-resp-≈ˡ {s} {p} {A} {B} {C} {g₁} {g₂} {f} eq = record
  { shape-eq = λ s → eq.shape-eq (f.shape s)
  ; pos-eq   = λ s p → cong (f.position {s}) (eq.pos-eq (f.shape s) p)
  }
  where
    module f  = _⇒_ f
    module eq = _≈M_ eq
-- Right whiskering: f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
-- 右复合保持等价：f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
∘M-resp-≈ʳ : ∀ {s p} {A B C : Container s p} {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
           → f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
∘M-resp-≈ʳ {s} {p} {A} {B} {C} {g} {f₁} {f₂} eq = record
  { shape-eq = λ s → cong (g.shape) (eq.shape-eq s)
  ; pos-eq   = λ s p → begin
      f₁.position {s} (g.position {f₁.shape s} p)
        ≡⟨ eq.pos-eq s (g.position {f₁.shape s} p) ⟩
      f₂.position {s} (subst (Position B) (eq.shape-eq s) (g.position {f₁.shape s} p))
        ≡⟨ cong (f₂.position {s}) (position-natural g (eq.shape-eq s) p) ⟩
      f₂.position {s} (g.position {f₂.shape s} (subst (Position C) (cong (g.shape) (eq.shape-eq s)) p))
        ∎
  }
  where
    module f₁ = _⇒_ f₁
    module f₂ = _⇒_ f₂
    module g  = _⇒_ g
    module eq = _≈M_ eq

module _ {s p} where
  -- Associativity of composition
  -- 复合的结合律
  ∘M-assoc : ∀ {A B C D : Container s p} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
             → (h ∘ g) ∘ f ≈M h ∘ (g ∘ f)
  ∘M-assoc = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }
  -- Left identity law
  -- 左单位律
  ∘M-identityˡ : ∀ {A B : Container s p} {f : A ⇒ B} → id B ∘ f ≈M f
  ∘M-identityˡ = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }
  -- Right identity law
  -- 右单位律
  ∘M-identityʳ : ∀ {A B : Container s p} {f : A ⇒ B} → f ∘ id A ≈M f
  ∘M-identityʳ = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }

-- Assemble the components into a Category instance
-- 将上述各组件组装为 Category 实例
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
