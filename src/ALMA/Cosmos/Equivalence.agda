------------------------------------------------------------------------
-- Bridge: a fully faithful and split essentially surjective functor
-- induces a StrongEquivalence
-- 桥接：满忠实且分裂本质满射的函子诱导强等价
--
-- Given F : C → D together with witnesses that F is fully faithful
-- and split essentially surjective, constructs a StrongEquivalence C D
-- The inverse functor is obtained from
-- EssSurj×Full×Faithful⇒Invertible; the two natural isomorphisms
-- F∘G ≅ id and G∘F ≅ id are constructed via fullness and faithfulness
-- 给定 F : C → D 以及 F 满忠实与分裂本质满射的见证，构造 StrongEquivalence C D
-- 逆函子取自 EssSurj×Full×Faithful⇒Invertible；
-- 两个自然同构 F∘G ≅ id 与 G∘F ≅ id 经满性与忠实性构造
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Equivalence where

open import Agda.Primitive using (Level)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)
open import Categories.Functor.Properties
  using (FullyFaithful; Full; Faithful; EssentiallySurjective; EssSurj×Full×Faithful⇒Invertible)
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Morphism using (_≅_; Iso)

-- Bridge construction, parameterized by the functor, its fully-faithful
-- witness, and the split essential surjectivity witness
-- 桥接构造，以函子、满忠实见证与分裂本质满射见证为参数
module _ {oc ℓc ec od ℓd ed : Level}
         {C : Category oc ℓc ec}
         {D : Category od ℓd ed}
         (F : Functor C D)
         (ff : FullyFaithful F)
         (ses : EssentiallySurjective F) where

  module C = Category C
  module D = Category D

  open D.HomReasoning

  -- Any D-morphism F X → F Y has a C-preimage
  -- 任意 D-态射 F X → F Y 都有 C-原像
  full : Full F
  full = proj₁ ff

  -- F reflects morphism equality
  -- F 反映态射相等
  faithful : Faithful F
  faithful = proj₂ ff

  module Fm = Functor F

  -- Inverse functor G : D → C, from EssSurj×Full×Faithful⇒Invertible
  -- The library defines F₀ Y = proj₁ (ses Y) and
  -- F₁ f = proj₁ (full (bwd Z ∘ f ∘ fwd Y))
  -- 逆函子 G : D → C，取自 EssSurj×Full×Faithful⇒Invertible
  -- 库定义 F₀ Y = proj₁ (ses Y)，F₁ f = proj₁ (full (bwd Z ∘ f ∘ fwd Y))
  G : Functor D C
  G = EssSurj×Full×Faithful⇒Invertible F ses full faithful

  module Gm = Functor G

  -- The chosen isomorphism F (G Y) ≅ Y
  -- 所选取的同构 F (G Y) ≅ Y
  isoAt : (Y : Category.Obj D) → _≅_ D (Fm.F₀ (Gm.F₀ Y)) Y
  isoAt Y = proj₂ (ses Y)

  -- Forward direction F (G Y) → Y
  -- 正向态射 F (G Y) → Y
  fwd : (Y : Category.Obj D) → Fm.F₀ (Gm.F₀ Y) D.⇒ Y
  fwd Y = _≅_.from (isoAt Y)

  -- Backward direction Y → F (G Y)
  -- 反向态射 Y → F (G Y)
  bwd : (Y : Category.Obj D) → Y D.⇒ Fm.F₀ (Gm.F₀ Y)
  bwd Y = _≅_.to (isoAt Y)

  isoAt-fwd-bwd : (Y : Category.Obj D) → fwd Y D.∘ bwd Y D.≈ D.id
  isoAt-fwd-bwd Y = Iso.isoʳ (_≅_.iso (isoAt Y))

  isoAt-bwd-fwd : (Y : Category.Obj D) → bwd Y D.∘ fwd Y D.≈ D.id
  isoAt-bwd-fwd Y = Iso.isoˡ (_≅_.iso (isoAt Y))

  -- F₁ (G₁ f) ≈ bwd Z ∘ (f ∘ fwd Y), extracted via the fullness witness
  -- F₁ (G₁ f) ≈ bwd Z ∘ (f ∘ fwd Y)，由满性见证给出
  F₁G₁-char : ∀ {Y Z} (f : Y D.⇒ Z) → Fm.F₁ (Gm.F₁ f) D.≈ bwd Z D.∘ (f D.∘ fwd Y)
  F₁G₁-char {Y} {Z} f = proj₂ (full (bwd Z D.∘ (f D.∘ fwd Y)))

  -- Naturality square: fwd Z ∘ F₁ (G₁ f) ≈ f ∘ fwd Y
  -- 自然性方块：fwd Z ∘ F₁ (G₁ f) ≈ f ∘ fwd Y
  FG-comm : ∀ {Y Z} (f : Y D.⇒ Z)
          → fwd Z D.∘ Fm.F₁ (Gm.F₁ f) D.≈ f D.∘ fwd Y
  FG-comm {Y} {Z} f = begin
    fwd Z D.∘ Fm.F₁ (Gm.F₁ f)
      ≈⟨ D.∘-resp-≈ʳ (F₁G₁-char f) ⟩
    fwd Z D.∘ (bwd Z D.∘ (f D.∘ fwd Y))
      ≈˘⟨ D.assoc ⟩
    (fwd Z D.∘ bwd Z) D.∘ (f D.∘ fwd Y)
      ≈⟨ D.∘-resp-≈ˡ (isoAt-fwd-bwd Z) ⟩
    D.id D.∘ (f D.∘ fwd Y)
      ≈⟨ D.identityˡ ⟩
    f D.∘ fwd Y
      ∎

  -- Inverse naturality square: bwd Z ∘ f ≈ F₁ (G₁ f) ∘ bwd Y
  -- 反向自然性方块：bwd Z ∘ f ≈ F₁ (G₁ f) ∘ bwd Y
  FG-comm⁻¹ : ∀ {Y Z} (f : Y D.⇒ Z)
            → bwd Z D.∘ f D.≈ Fm.F₁ (Gm.F₁ f) D.∘ bwd Y
  FG-comm⁻¹ {Y} {Z} f = begin
    bwd Z D.∘ f
      ≈˘⟨ D.∘-resp-≈ʳ D.identityʳ ⟩
    bwd Z D.∘ (f D.∘ D.id)
      ≈˘⟨ D.∘-resp-≈ʳ {g = bwd Z}
             (D.∘-resp-≈ʳ {g = f} (isoAt-fwd-bwd Y)) ⟩
    bwd Z D.∘ (f D.∘ (fwd Y D.∘ bwd Y))
      ≈⟨ D.∘-resp-≈ʳ (D.sym-assoc {f = bwd Y} {g = fwd Y} {h = f}) ⟩
    bwd Z D.∘ ((f D.∘ fwd Y) D.∘ bwd Y)
      ≈˘⟨ D.assoc ⟩
    (bwd Z D.∘ (f D.∘ fwd Y)) D.∘ bwd Y
      ≈˘⟨ D.∘-resp-≈ˡ (F₁G₁-char f) ⟩
    Fm.F₁ (Gm.F₁ f) D.∘ bwd Y
      ∎

  F∘G≅id : NaturalIsomorphism (F ∘F G) id
  F∘G≅id = record
    { F⇒G = ntHelper record
      { η       = λ Y → fwd Y
      ; commute = λ {Y} {Z} f → FG-comm f
      }
    ; F⇐G = ntHelper record
      { η       = λ Y → bwd Y
      ; commute = λ {Y} {Z} f → FG-comm⁻¹ f
      }
    ; iso = λ Y → _≅_.iso (isoAt Y)
    }

  -- Components of the natural isomorphism G ∘ F ≅ id_C
  -- 自然同构 G ∘ F ≅ id_C 的分量
  GF-fwd : ∀ X → Gm.F₀ (Fm.F₀ X) C.⇒ X
  GF-fwd X = proj₁ (full (fwd (Fm.F₀ X)))

  GF-fwd-comm : ∀ X → Fm.F₁ (GF-fwd X) D.≈ fwd (Fm.F₀ X)
  GF-fwd-comm X = proj₂ (full (fwd (Fm.F₀ X)))

  GF-bwd : ∀ X → X C.⇒ Gm.F₀ (Fm.F₀ X)
  GF-bwd X = proj₁ (full (bwd (Fm.F₀ X)))

  GF-bwd-comm : ∀ X → Fm.F₁ (GF-bwd X) D.≈ bwd (Fm.F₀ X)
  GF-bwd-comm X = proj₂ (full (bwd (Fm.F₀ X)))

  -- Helper: if F₁ f ≈ D.id then f ≈ C.id, by faithfulness
  -- 辅助：若 F₁ f ≈ D.id，则由忠实性得 f ≈ C.id
  faithful-id : ∀ {X} {f : X C.⇒ X} → Fm.F₁ f D.≈ D.id → f C.≈ C.id
  faithful-id {f = f} eq = faithful (begin
    Fm.F₁ f
      ≈⟨ eq ⟩
    D.id
      ≈˘⟨ Fm.identity ⟩
    Fm.F₁ C.id
      ∎)

  -- Helper: absorb the round-trip fwd Y ∘ bwd Y on the left
  -- 辅助：在左侧吸收往返 fwd Y ∘ bwd Y
  fwd-bwd-absorb : ∀ {W Z} (g : W D.⇒ Z)
                 → fwd Z D.∘ (bwd Z D.∘ g) D.≈ g
  fwd-bwd-absorb {Z = Z} g = begin
    fwd Z D.∘ (bwd Z D.∘ g)
      ≈˘⟨ D.assoc ⟩
    (fwd Z D.∘ bwd Z) D.∘ g
      ≈⟨ D.∘-resp-≈ˡ (isoAt-fwd-bwd Z) ⟩
    D.id D.∘ g
      ≈⟨ D.identityˡ ⟩
    g
      ∎

  -- Helper: absorb the round-trip fwd X ∘ bwd X on the right
  -- 辅助：在右侧吸收往返 fwd X ∘ bwd X
  bwd-right-absorb : ∀ {X Y} (g : Fm.F₀ X D.⇒ Fm.F₀ Y)
                   → (g D.∘ fwd (Fm.F₀ X)) D.∘ bwd (Fm.F₀ X) D.≈ g
  bwd-right-absorb {X} g = begin
    (g D.∘ fwd (Fm.F₀ X)) D.∘ bwd (Fm.F₀ X)
      ≈⟨ D.assoc ⟩
    g D.∘ (fwd (Fm.F₀ X) D.∘ bwd (Fm.F₀ X))
      ≈⟨ D.∘-resp-≈ʳ (isoAt-fwd-bwd (Fm.F₀ X)) ⟩
    g D.∘ D.id
      ≈⟨ D.identityʳ ⟩
    g
      ∎

  -- Left inverse: GF-fwd ∘ GF-bwd ≈ id
  -- 左逆：GF-fwd ∘ GF-bwd ≈ id
  GF-isoˡ : ∀ X → GF-fwd X C.∘ GF-bwd X C.≈ C.id
  GF-isoˡ X = faithful-id (begin
    Fm.F₁ (GF-fwd X C.∘ GF-bwd X)
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-fwd X) D.∘ Fm.F₁ (GF-bwd X)
      ≈⟨ D.∘-resp-≈ (GF-fwd-comm X) (GF-bwd-comm X) ⟩
    fwd (Fm.F₀ X) D.∘ bwd (Fm.F₀ X)
      ≈⟨ isoAt-fwd-bwd (Fm.F₀ X) ⟩
    D.id
      ∎)

  -- Right inverse: GF-bwd ∘ GF-fwd ≈ id
  -- 右逆：GF-bwd ∘ GF-fwd ≈ id
  GF-isoʳ : ∀ X → GF-bwd X C.∘ GF-fwd X C.≈ C.id
  GF-isoʳ X = faithful-id (begin
    Fm.F₁ (GF-bwd X C.∘ GF-fwd X)
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-bwd X) D.∘ Fm.F₁ (GF-fwd X)
      ≈⟨ D.∘-resp-≈ (GF-bwd-comm X) (GF-fwd-comm X) ⟩
    bwd (Fm.F₀ X) D.∘ fwd (Fm.F₀ X)
      ≈⟨ isoAt-bwd-fwd (Fm.F₀ X) ⟩
    D.id
      ∎)

  -- Naturality: GF-fwd Y ∘ G₁ (F₁ f) ≈ f ∘ GF-fwd X
  -- 自然性：GF-fwd Y ∘ G₁ (F₁ f) ≈ f ∘ GF-fwd X
  GF-comm : ∀ {X Y} (f : X C.⇒ Y)
          → GF-fwd Y C.∘ Gm.F₁ (Fm.F₁ f) C.≈ f C.∘ GF-fwd X
  GF-comm {X} {Y} f = faithful (begin
    Fm.F₁ (GF-fwd Y C.∘ Gm.F₁ (Fm.F₁ f))
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-fwd Y) D.∘ Fm.F₁ (Gm.F₁ (Fm.F₁ f))
      ≈⟨ D.∘-resp-≈ (GF-fwd-comm Y) (F₁G₁-char (Fm.F₁ f)) ⟩
    fwd (Fm.F₀ Y) D.∘ (bwd (Fm.F₀ Y) D.∘ (Fm.F₁ f D.∘ fwd (Fm.F₀ X)))
      ≈⟨ fwd-bwd-absorb (Fm.F₁ f D.∘ fwd (Fm.F₀ X)) ⟩
    Fm.F₁ f D.∘ fwd (Fm.F₀ X)
      ≈˘⟨ D.∘-resp-≈ʳ (GF-fwd-comm X) ⟩
    Fm.F₁ f D.∘ Fm.F₁ (GF-fwd X)
      ≈˘⟨ Fm.homomorphism ⟩
    Fm.F₁ (f C.∘ GF-fwd X)
      ∎)

  -- Inverse naturality: G₁ (F₁ f) ∘ GF-bwd X ≈ GF-bwd Y ∘ f
  -- 反向自然性：G₁ (F₁ f) ∘ GF-bwd X ≈ GF-bwd Y ∘ f
  GF-comm⁻¹ : ∀ {X Y} (f : X C.⇒ Y)
            → Gm.F₁ (Fm.F₁ f) C.∘ GF-bwd X C.≈ GF-bwd Y C.∘ f
  GF-comm⁻¹ {X} {Y} f = faithful (begin
    Fm.F₁ (Gm.F₁ (Fm.F₁ f) C.∘ GF-bwd X)
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (Gm.F₁ (Fm.F₁ f)) D.∘ Fm.F₁ (GF-bwd X)
      ≈⟨ D.∘-resp-≈ (F₁G₁-char (Fm.F₁ f)) (GF-bwd-comm X) ⟩
    (bwd (Fm.F₀ Y) D.∘ (Fm.F₁ f D.∘ fwd (Fm.F₀ X))) D.∘ bwd (Fm.F₀ X)
      ≈⟨ D.assoc ⟩
    bwd (Fm.F₀ Y) D.∘ ((Fm.F₁ f D.∘ fwd (Fm.F₀ X)) D.∘ bwd (Fm.F₀ X))
      ≈⟨ D.∘-resp-≈ʳ (bwd-right-absorb (Fm.F₁ f)) ⟩
    bwd (Fm.F₀ Y) D.∘ Fm.F₁ f
      ≈⟨ D.∘-resp-≈ˡ {g = Fm.F₁ f} (D.Equiv.sym (GF-bwd-comm Y)) ⟩
    Fm.F₁ (GF-bwd Y) D.∘ Fm.F₁ f
      ≈˘⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-bwd Y C.∘ f)
      ∎)

  G∘F≅id : NaturalIsomorphism (G ∘F F) id
  G∘F≅id = record
    { F⇒G = ntHelper record
      { η       = λ X → GF-fwd X
      ; commute = λ {X} {Y} f → GF-comm f
      }
    ; F⇐G = ntHelper record
      { η       = λ X → GF-bwd X
      ; commute = λ {X} {Y} f → C.Equiv.sym (GF-comm⁻¹ f)
      }
    ; iso = λ X → record { isoˡ = GF-isoʳ X ; isoʳ = GF-isoˡ X }
    }

  toStrongEquiv : StrongEquivalence C D
  toStrongEquiv = record
    { F            = F
    ; G            = G
    ; weak-inverse = record
      { F∘G≈id = F∘G≅id
      ; G∘F≈id = G∘F≅id
      }
    }
