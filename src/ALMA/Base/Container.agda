{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Container where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-subst; subst-subst-sym; module ≡-Reasoning)
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Product.Base using (proj₁; proj₂)
open import Function.Base using (id; _∘_)
open ≡-Reasoning

open import Categories.Category.Core using (Category)

open import ALMA.Base.IndexedMType using (M; fst; snd)

ContObj : (a b : Level) → Set (lsuc (a ⊔ b))
ContObj a b = Σ (Set a) (λ A → A → Set b)

⟦_⟧ : ∀ {a b c} (A : Set a) (B : A → Set b) (X : Set c)
    → Set (a ⊔ b ⊔ c)
⟦ A ⟧ B X = Σ A (λ a → B a → X)

module _ {a b : Level} {A : Set a} {B : A → Set b} where
  map : ∀ {c d} {X : Set c} {Y : Set d} → (X → Y) → ⟦ A ⟧ B X → ⟦ A ⟧ B Y
  map f (s , k) = s , f ∘ k

  map-id : ∀ {c} {X : Set c} (x : ⟦ A ⟧ B X) → map id x ≡ x
  map-id (s , k) = refl

  map-∘ : ∀ {c d e} {X : Set c} {Y : Set d} {Z : Set e}
        (f : Y → Z) (g : X → Y) (x : ⟦ A ⟧ B X)
        → map (f ∘ g) x ≡ map f (map g x)
  map-∘ f g (s , k) = refl

Cont⇒ : ∀ {a₁ a₂ b₁ b₂}
      (A₁ : Set a₁) (B₁ : A₁ → Set b₁)
      (A₂ : Set a₂) (B₂ : A₂ → Set b₂)
      → Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)
Cont⇒ A₁ B₁ A₂ B₂ = (a : A₁) → Σ A₂ (λ a₂ → B₂ a₂ → B₁ a)

Cont⇒-shape : ∀ {a₁ a₂ b₁ b₂}
            {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
            {A₂ : Set a₂} {B₂ : A₂ → Set b₂}
            → Cont⇒ A₁ B₁ A₂ B₂ → A₁ → A₂
Cont⇒-shape f a = proj₁ (f a)

Cont⇒-position : ∀ {a₁ a₂ b₁ b₂}
               {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
               {A₂ : Set a₂} {B₂ : A₂ → Set b₂}
               → (f : Cont⇒ A₁ B₁ A₂ B₂) (a : A₁)
               → B₂ (Cont⇒-shape f a) → B₁ a
Cont⇒-position f a = proj₂ (f a)

id⇒ : ∀ {a b} (A : Set a) (B : A → Set b) → Cont⇒ A B A B
id⇒ A B a = a , id

_∘⇒_ : ∀ {a₁ a₂ a₃ b₁ b₂ b₃}
      {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
      {A₂ : Set a₂} {B₂ : A₂ → Set b₂}
      {A₃ : Set a₃} {B₃ : A₃ → Set b₃}
      → Cont⇒ A₂ B₂ A₃ B₃
      → Cont⇒ A₁ B₁ A₂ B₂
      → Cont⇒ A₁ B₁ A₃ B₃
_∘⇒_ g f a =
  let (a₂ , τ_f) = f a
      (a₃ , τ_g) = g a₂
  in a₃ , τ_f ∘ τ_g

⟪_⟫ : ∀ {a₁ a₂ b₁ b₂ c}
    {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
    {A₂ : Set a₂} {B₂ : A₂ → Set b₂}
    {X : Set c}
    → Cont⇒ A₁ B₁ A₂ B₂ → ⟦ A₁ ⟧ B₁ X → ⟦ A₂ ⟧ B₂ X
⟪ f ⟫ (s , k) =
  let (s' , τ) = f s
  in s' , k ∘ τ

module _ {a₁ a₂ b₁ b₂}
        {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
        {A₂ : Set a₂} {B₂ : A₂ → Set b₂} where

  private
    shape-layer : (f g : Cont⇒ A₁ B₁ A₂ B₂) (a : A₁) → Set a₂
    shape-layer f g a = Cont⇒-shape f a ≡ Cont⇒-shape g a

    pos-transport : {x y : A₂} → x ≡ y → B₂ x → B₂ y
    pos-transport e = subst B₂ e

    pos-coherence : (f g : Cont⇒ A₁ B₁ A₂ B₂) {a : A₁}
                    (e : shape-layer f g a)
                    → Set (b₁ ⊔ b₂)
    pos-coherence f g {a} e =
      ∀ q → Cont⇒-position f a q ≡ Cont⇒-position g a (pos-transport e q)

  layer-⇒ : (f g : Cont⇒ A₁ B₁ A₂ B₂) → Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)
  layer-⇒ f g = ∀ a → Σ (shape-layer f g a) (pos-coherence f g {a = a})

  layer-⇒-refl : (f : Cont⇒ A₁ B₁ A₂ B₂) → layer-⇒ f f
  layer-⇒-refl f a = refl , λ _ → refl

  layer-⇒-sym : {f g : Cont⇒ A₁ B₁ A₂ B₂}
              → layer-⇒ f g → layer-⇒ g f
  layer-⇒-sym {f = f} {g = g} p a =
    let (e , coh) = p a
        e' = sym e
        coh' = λ q →
          begin
            Cont⇒-position g a q
          ≡˘⟨ cong (Cont⇒-position g a) (subst-subst-sym {P = B₂} e {p = q}) ⟩
            Cont⇒-position g a (subst B₂ e (subst B₂ e' q))
          ≡˘⟨ coh (subst B₂ e' q) ⟩
            Cont⇒-position f a (subst B₂ e' q)
          ∎
    in e' , coh'

  layer-⇒-trans : {f g h : Cont⇒ A₁ B₁ A₂ B₂}
                → layer-⇒ f g → layer-⇒ g h → layer-⇒ f h
  layer-⇒-trans {f = f} {g = g} {h = h} p q a =
    let (e₁ , coh₁) = p a
        (e₂ , coh₂) = q a
        e' = trans e₁ e₂
        coh' = λ r →
          begin
            Cont⇒-position f a r
          ≡⟨ coh₁ r ⟩
            Cont⇒-position g a (pos-transport e₁ r)
          ≡⟨ coh₂ (pos-transport e₁ r) ⟩
            Cont⇒-position h a (pos-transport e₂ (pos-transport e₁ r))
          ≡⟨ cong (Cont⇒-position h a) (subst-subst {P = B₂} e₁ {y≡z = e₂} {p = r}) ⟩
            Cont⇒-position h a (pos-transport e' r)
          ∎
    in e' , coh'

  layer-⇒-isEquivalence : IsEquivalence layer-⇒
  layer-⇒-isEquivalence = record
    { refl  = λ {f} → layer-⇒-refl f
    ; sym   = λ {f g} → layer-⇒-sym {f = f} {g = g}
    ; trans = λ {f g h} → layer-⇒-trans {f = f} {g = g} {h = h}
    }

module _ {a a' b b'} {A : Set a} {B : A → Set b}
        {A' : Set a'} {B' : A' → Set b'} where

  ∘⇒-identityˡ : (f : Cont⇒ A B A' B')
                → layer-⇒ (id⇒ A' B' ∘⇒ f) f
  ∘⇒-identityˡ f = λ a → refl , λ _ → refl

  ∘⇒-identityʳ : (f : Cont⇒ A B A' B')
                → layer-⇒ (f ∘⇒ id⇒ A B) f
  ∘⇒-identityʳ f = λ a → refl , λ _ → refl

module _ {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄}
        {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
        {A₂ : Set a₂} {B₂ : A₂ → Set b₂}
        {A₃ : Set a₃} {B₃ : A₃ → Set b₃}
        {A₄ : Set a₄} {B₄ : A₄ → Set b₄} where

  ∘⇒-assoc : (h : Cont⇒ A₃ B₃ A₄ B₄)
            (g : Cont⇒ A₂ B₂ A₃ B₃)
            (f : Cont⇒ A₁ B₁ A₂ B₂)
            → layer-⇒ ((h ∘⇒ g) ∘⇒ f) (h ∘⇒ (g ∘⇒ f))
  ∘⇒-assoc h g f = λ a → refl , λ _ → refl

module _ {a₁ a₂ a₃ b₁ b₂ b₃ : Level}
        {A₁ : Set a₁} {B₁ : A₁ → Set b₁}
        {A₂ : Set a₂} {B₂ : A₂ → Set b₂}
        {A₃ : Set a₃} {B₃ : A₃ → Set b₃} where

  private
    transport-nat : (g : Cont⇒ A₂ B₂ A₃ B₃)
                    {x y : A₂} (e : x ≡ y)
                    (q : B₃ (Cont⇒-shape g x))
                    → subst B₂ e (Cont⇒-position g x q)
                    ≡ Cont⇒-position g y (subst B₃ (cong (Cont⇒-shape g) e) q)
    transport-nat g refl q = refl

  ∘⇒-resp-≈ʳ : {g₁ g₂ : Cont⇒ A₂ B₂ A₃ B₃} {f : Cont⇒ A₁ B₁ A₂ B₂}
             → layer-⇒ g₁ g₂
             → layer-⇒ (g₁ ∘⇒ f) (g₂ ∘⇒ f)
  ∘⇒-resp-≈ʳ {g₁ = g₁} {g₂ = g₂} {f = f} p a =
    let a₂ = Cont⇒-shape f a
        τ-f = Cont⇒-position f a
        (e-g , coh-g) = p a₂
    in e-g , λ q → cong τ-f (coh-g q)

  ∘⇒-resp-≈ˡ : {f₁ f₂ : Cont⇒ A₁ B₁ A₂ B₂} {g : Cont⇒ A₂ B₂ A₃ B₃}
             → layer-⇒ f₁ f₂
             → layer-⇒ (g ∘⇒ f₁) (g ∘⇒ f₂)
  ∘⇒-resp-≈ˡ {f₁ = f₁} {f₂ = f₂} {g = g} p a =
    let (e-f , coh-f) = p a
        a₂₁ = Cont⇒-shape f₁ a
        τ-g₁ = Cont⇒-position g a₂₁
    in cong (Cont⇒-shape g) e-f ,
       λ q →
         begin
           Cont⇒-position f₁ a (τ-g₁ q)
         ≡⟨ coh-f (τ-g₁ q) ⟩
           Cont⇒-position f₂ a (subst B₂ e-f (τ-g₁ q))
         ≡⟨ cong (Cont⇒-position f₂ a) (transport-nat g e-f q) ⟩
           Cont⇒-position f₂ a (Cont⇒-position g (Cont⇒-shape f₂ a) (subst B₃ (cong (Cont⇒-shape g) e-f) q))
         ∎

  ∘⇒-resp-≈ : {f₁ f₂ : Cont⇒ A₁ B₁ A₂ B₂} {g₁ g₂ : Cont⇒ A₂ B₂ A₃ B₃}
            → layer-⇒ g₁ g₂
            → layer-⇒ f₁ f₂
            → layer-⇒ (g₁ ∘⇒ f₁) (g₂ ∘⇒ f₂)
  ∘⇒-resp-≈ {f₁ = f₁} {f₂ = f₂} {g₁ = g₁} {g₂ = g₂} eq-g eq-f =
    layer-⇒-trans
      {f = g₁ ∘⇒ f₁} {g = g₁ ∘⇒ f₂} {h = g₂ ∘⇒ f₂}
      (∘⇒-resp-≈ˡ {f₁ = f₁} {f₂ = f₂} {g = g₁} eq-f)
      (∘⇒-resp-≈ʳ {g₁ = g₁} {g₂ = g₂} {f = f₂} eq-g)

ContCat : (a b : Level) → Category (lsuc (a ⊔ b)) (a ⊔ b) (a ⊔ b)
ContCat a b = record
  { Obj       = ContObj a b
  ; _⇒_       = λ X Y → Cont⇒ (proj₁ X) (proj₂ X) (proj₁ Y) (proj₂ Y)
  ; _≈_       = λ {X} {Y} → layer-⇒ {A₁ = proj₁ X} {B₁ = proj₂ X} {A₂ = proj₁ Y} {B₂ = proj₂ Y}
  ; id        = λ {X} → id⇒ (proj₁ X) (proj₂ X)
  ; _∘_       = _∘⇒_
  ; equiv     = λ {X} {Y} →
                  layer-⇒-isEquivalence
                    {A₁ = proj₁ X} {B₁ = proj₂ X}
                    {A₂ = proj₁ Y} {B₂ = proj₂ Y}
  ; ∘-resp-≈  = λ { {X} {Y} {Z} {f} {h} {g} {i} eq-fh eq-gi →
                    ∘⇒-resp-≈
                      {A₁ = proj₁ X} {B₁ = proj₂ X}
                      {A₂ = proj₁ Y} {B₂ = proj₂ Y}
                      {A₃ = proj₁ Z} {B₃ = proj₂ Z}
                      {f₁ = g} {f₂ = i} {g₁ = f} {g₂ = h}
                      eq-fh eq-gi
                }
  ; assoc     = λ { {W} {X} {Y} {Z} {f} {g} {h} → ∘⇒-assoc h g f }
  ; sym-assoc = λ { {W} {X} {Y} {Z} {f} {g} {h} →
                    layer-⇒-sym
                      {A₁ = proj₁ W} {B₁ = proj₂ W}
                      {A₂ = proj₁ Z} {B₂ = proj₂ Z}
                      {f = (h ∘⇒ g) ∘⇒ f} {g = h ∘⇒ (g ∘⇒ f)}
                      (∘⇒-assoc h g f)
                }
  ; identityˡ = λ { {X} {Y} {f} → ∘⇒-identityˡ {A = proj₁ X} {B = proj₂ X} {A' = proj₁ Y} {B' = proj₂ Y} f }
  ; identityʳ = λ { {X} {Y} {f} → ∘⇒-identityʳ {A = proj₁ X} {B = proj₂ X} {A' = proj₁ Y} {B' = proj₂ Y} f }
  ; identity² = λ {X} → layer-⇒-refl {A₁ = proj₁ X} {B₁ = proj₂ X} {A₂ = proj₁ X} {B₂ = proj₂ X} (id⇒ (proj₁ X) (proj₂ X))
  }

module _ {a b : Level} (A : Set a) (B : A → Set b) where
  ContainerCoalg : Set (a ⊔ b)
  ContainerCoalg = M A B

  out : ContainerCoalg → ⟦ A ⟧ B ContainerCoalg
  out c = fst c , λ p → snd c p

  ana : ∀ {c} {X : Set c} → (X → ⟦ A ⟧ B X) → X → ContainerCoalg
  ana γ x .fst = proj₁ (γ x)
  ana γ x .snd p = ana γ (proj₂ (γ x) p)
