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
module _ {s p} {X Y : Container s p} where
  infix 4 _≈M_
  record _≈M_ (f g : X ⇒ Y) : Set (s ⊔ p) where
    private
      module f = _⇒_ f
      module g = _⇒_ g
    field
      shape-eq : f.shape ≗ g.shape
      pos-eq   : ∀ (sh : Shape X) (q : Position Y (f.shape sh))
                → f.position {sh} q ≡ g.position {sh} (subst (Position Y) (shape-eq sh) q)

  -- Reflexivity of _≈M_
  -- _≈M_ 的自反性
  ≈M-refl : ∀ {f : X ⇒ Y} → f ≈M f
  ≈M-refl = record { shape-eq = λ _ → refl ; pos-eq = λ _ _ → refl }
  -- Symmetry of _≈M_
  -- _≈M_ 的对称性
  ≈M-sym : ∀ {f g : X ⇒ Y} → f ≈M g → g ≈M f
  ≈M-sym {f} {g} eq = record
    { shape-eq = λ sh → sym (eq.shape-eq sh)
    ; pos-eq   = λ sh q →
        let e = eq.shape-eq sh in
        begin
          G.position {sh} q
            ≡˘⟨ cong (G.position {sh}) (subst-subst-sym e) ⟩
          G.position {sh}
            (subst (Position Y) e (subst (Position Y) (sym e) q))
            ≡˘⟨ eq.pos-eq sh (subst (Position Y) (sym e) q) ⟩
          F.position {sh} (subst (Position Y) (sym e) q)
        ∎
    }
    where
      module F  = _⇒_ f
      module G  = _⇒_ g
      module eq = _≈M_ eq
  -- Transitivity of _≈M_
  -- _≈M_ 的传递性
  ≈M-trans : ∀ {f g h : X ⇒ Y} → f ≈M g → g ≈M h → f ≈M h
  ≈M-trans {f} {g} {h} eq-fg eq-gh = record
    { shape-eq = λ sh → trans (FG.shape-eq sh) (GH.shape-eq sh)
    ; pos-eq   = λ sh q →
        let q₁ = subst (Position Y) (FG.shape-eq sh) q in
        begin
          F.position {sh} q
            ≡⟨ FG.pos-eq sh q ⟩
          G.position {sh} q₁
            ≡⟨ GH.pos-eq sh q₁ ⟩
          H.position {sh} (subst (Position Y) (GH.shape-eq sh) q₁)
            ≡⟨ cong (H.position {sh})
                 (subst-subst (FG.shape-eq sh) {y≡z = GH.shape-eq sh}) ⟩
          H.position {sh} (subst (Position Y) (trans (FG.shape-eq sh) (GH.shape-eq sh)) q)
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
      { Carrier = X ⇒ Y ; _≈_ = _≈M_ ; isEquivalence = ≈M-isEquiv })
      public

-- Position commutes with substitution along shape equalities
-- (naturality of position in the shape index)
-- position 与沿形状相等的 subst 交换（position 在形状指标上的自然性）
module _ {s p} {B : Container s p} {C : Container s p} where
  position-subst : ∀ (g : B ⇒ C) {t₁ t₂ : Shape B} (eq : t₁ ≡ t₂)
                    (q : Position C (_⇒_.shape g t₁)) →
                    subst (Position B) eq (_⇒_.position g {t₁} q)
                    ≡ _⇒_.position g {t₂} (subst (Position C) (cong (_⇒_.shape g) eq) q)
  position-subst g refl q = refl
-- Left whiskering: g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
-- 左复合保持等价：g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
∘M-resp-≈ˡ : ∀ {s p} {A B C : Container s p} {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
           → g₁ ≈M g₂ → g₁ ∘ f ≈M g₂ ∘ f
∘M-resp-≈ˡ {s} {p} {A} {B} {C} {g₁} {g₂} {f} eq = record
  { shape-eq = λ sh → eq.shape-eq (f.shape sh)
  ; pos-eq   = λ sh q → cong (f.position {sh}) (eq.pos-eq (f.shape sh) q)
  }
  where
    module f  = _⇒_ f
    module eq = _≈M_ eq
-- Right whiskering: f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
-- 右复合保持等价：f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
∘M-resp-≈ʳ : ∀ {s p} {A B C : Container s p} {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
           → f₁ ≈M f₂ → g ∘ f₁ ≈M g ∘ f₂
∘M-resp-≈ʳ {s} {p} {A} {B} {C} {g} {f₁} {f₂} eq = record
  { shape-eq = λ sh → cong (g.shape) (eq.shape-eq sh)
  ; pos-eq   = λ sh q →
      let q₁ = g.position {f₁.shape sh} q
          e  = eq.shape-eq sh
      in begin
        f₁.position {sh} q₁
          ≡⟨ eq.pos-eq sh q₁ ⟩
        f₂.position {sh} (subst (Position B) e q₁)
          ≡⟨ cong (f₂.position {sh}) (position-subst g e q) ⟩
        f₂.position {sh}
          (g.position {f₂.shape sh} (subst (Position C) (cong (g.shape) e) q))
          ∎
  }
  where
    module f₁ = _⇒_ f₁
    module f₂ = _⇒_ f₂
    module g  = _⇒_ g
    module eq = _≈M_ eq
-- Composition respects equivalence: derive from whiskering + transitivity
-- 复合保持等价：由左右 whiskering 与传递性组合得到
∘M-resp-≈ : ∀ {s p} {A B C : Container s p}
            {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
          → g₁ ≈M g₂ → f₁ ≈M f₂ → g₁ ∘ f₁ ≈M g₂ ∘ f₂
∘M-resp-≈ {A = A} {C = C} {g₁ = g₁} {g₂ = g₂} {f₁ = f₁} {f₂ = f₂}
          eq-g eq-f =
  R.begin
    g₁ ∘ f₁
  R.≈⟨ ∘M-resp-≈ˡ {f = f₁} eq-g ⟩
    g₂ ∘ f₁
  R.≈⟨ ∘M-resp-≈ʳ {g = g₂} eq-f ⟩
    g₂ ∘ f₂
  R.∎
  where
    module R = ≈M-Reasoning {X = A} {Y = C}

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
