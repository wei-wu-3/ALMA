------------------------------------------------------------------------
-- The wide subcategory of MCorrCatˢ on identity-index carried functors.
--
-- Objects are ℕ-indexed deterministic systems with a fixed successor
-- dynamics d : ℕ → ℕ; only the label fibre varies. A morphism is a
-- setoid carried functor FMˢ whose index map is the identity. Every
-- cocone leg in this category therefore follows the identity
-- trajectory, which is the range in which the push colimit mediating
-- functor is total and unique (the non-surjective index obstruction of
-- ColimitPolarity cannot arise). The category laws are those of
-- MCorrCatˢ on the underlying FMˢ; the index proof is propositional and
-- never participates in morphism equality, so no UIP is required.
--
-- MCorrCatˢ 在“索引恒等”携带函子上的宽子范畴。
--
-- 对象是以固定后继动力 d : ℕ → ℕ 的 ℕ 索引确定性系统，只有标签纤维可变；
-- 态射是索引映射为恒等的 setoid 携带函子 FMˢ。故本范畴中每条余锥腿都沿
-- 恒等轨迹，这正是 push 余极限 mediate 函子全且唯一的范围（不会出现
-- ColimitPolarity 的索引非满射障碍）。范畴律即底层 FMˢ 在 MCorrCatˢ
-- 中的律；索引见证是命题性的、不参与态射相等，故无需 UIP。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.SameIndexCatS where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core using (Category)

open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; propEqOn)
open import ALMA.Base.MCorrSetoidCat
  using ( FMapˢ; FMˢ; idFMˢ; compFMˢ; _≈FM_
        ; ≈FM-refl; ≈FM-sym; ≈FM-trans
        ; ∘-resp-≈FM; assocFM; sym-assocFM
        ; identityˡFM; identityʳFM; identity²FM )

open SysEq

------------------------------------------------------------------------
-- An object: a label family over ℕ together with its fibre setoid.
-- 对象：ℕ 上的标签族及其纤维 setoid。

record LabelSys (ℓ : Level) : Set (lsuc ℓ) where
  field
    A₀   : ℕ → Set ℓ
    ≈A₀  : (v : ℕ) → EqOn {ℓ = ℓ} (A₀ v)
open LabelSys public

-- The deterministic system for a label family under dynamics d.
-- 动力 d 下标签族对应的确定性系统。
dsys : (d : ℕ → ℕ) {ℓ : Level} (X : LabelSys ℓ)
     → SysEq lzero ℓ lzero ℓ lzero
dsys d X = record
  { I  = ℕ
  ; A  = A₀ X
  ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ d v
  ; ≈A = ≈A₀ X
  ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ d v)
  }

------------------------------------------------------------------------
-- Identity-index carried functors and the wide subcategory.
-- 索引恒等携带函子与宽子范畴。

module _ (d : ℕ → ℕ) {ℓ : Level} where

  -- A morphism packages an FMˢ together with a pointwise identity index.
  -- 态射打包一个 FMˢ 及逐点恒等索引见证。
  record Idx⇒ (X Y : LabelSys ℓ) : Set ℓ where
    field
      mor  : FMˢ (dsys d X) (dsys d Y)
      u≡id : (v : ℕ) → FMapˢ.u (FMˢ.mor mor) v ≡ v
  open Idx⇒ public

  private
    s = dsys d

  ----------------------------------------------------------------------
  -- Identity and composition; the index proofs collapse to refl along
  -- the identity maps.
  -- 恒等与复合；索引见证沿恒等映射坍缩为 refl。

  idxi : (X : LabelSys ℓ) → Idx⇒ X X
  idxi X = record { mor = idFMˢ {X = s X} ; u≡id = λ _ → refl }

  compi : {X Y Z : LabelSys ℓ} → Idx⇒ Y Z → Idx⇒ X Y → Idx⇒ X Z
  compi {X = X} g f = record { mor = compFMˢ (mor g) (mor f)
                             ; u≡id = ucomp }
    where
    ucomp : (v : ℕ)
          → FMapˢ.u (FMˢ.mor (compFMˢ (mor g) (mor f))) v ≡ v
    ucomp v = trans (u≡id g (FMapˢ.u (FMˢ.mor (mor f)) v))
                    (u≡id f v)

  ----------------------------------------------------------------------
  -- Morphism equality is behavioural equality of the underlying FMˢ.
  -- 态射相等即底层 FMˢ 的行为相等。

  _≈i_ : {X Y : LabelSys ℓ} → Idx⇒ X Y → Idx⇒ X Y → Set ℓ
  f ≈i g = mor f ≈FM mor g

  ≈i-refl : {X Y : LabelSys ℓ} (f : Idx⇒ X Y) → f ≈i f
  ≈i-refl {X = X} {Y = Y} f = ≈FM-refl {X = s X} {Y = s Y} (mor f)

  ≈i-sym : {X Y : LabelSys ℓ} {f g : Idx⇒ X Y} → f ≈i g → g ≈i f
  ≈i-sym {X = X} {Y = Y} {f = f} {g = g} p =
    ≈FM-sym {X = s X} {Y = s Y} {f = mor f} {g = mor g} p

  ≈i-trans : {X Y : LabelSys ℓ} {f g h : Idx⇒ X Y}
           → f ≈i g → g ≈i h → f ≈i h
  ≈i-trans {X = X} {Y = Y} {f = f} {g = g} {h = h} p q =
    ≈FM-trans {X = s X} {Y = s Y}
              {f = mor f} {g = mor g} {h = mor h} p q

  ≈i-isEquivalence : {X Y : LabelSys ℓ} → IsEquivalence (_≈i_ {X} {Y})
  ≈i-isEquivalence = record
    { refl  = λ {f} → ≈i-refl f
    ; sym   = λ {f g} → ≈i-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈i-trans {f = f} {g = g} {h = h}
    }

  ∘-resp-≈i : {X Y Z : LabelSys ℓ}
              {F₁ F₂ : Idx⇒ X Y} {G₁ G₂ : Idx⇒ Y Z}
            → F₁ ≈i F₂ → G₁ ≈i G₂
            → compi G₁ F₁ ≈i compi G₂ F₂
  ∘-resp-≈i {X = X} {Y = Y} {Z = Z}
            {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} eqF eqG =
    ∘-resp-≈FM {X = s X} {Y = s Y} {Z = s Z}
               {F₁ = mor F₁} {F₂ = mor F₂}
               {G₁ = mor G₁} {G₂ = mor G₂} eqF eqG

  ----------------------------------------------------------------------
  -- The wide subcategory.
  -- 宽子范畴。

  SameIndexCat : Category (lsuc ℓ) ℓ ℓ
  SameIndexCat = record
    { Obj       = LabelSys ℓ
    ; _⇒_       = Idx⇒
    ; _≈_       = λ {X} {Y} → _≈i_ {X} {Y}
    ; id        = λ {X} → idxi X
    ; _∘_       = λ {X} {Y} {Z} g f → compi {X} {Y} {Z} g f
    ; equiv     = λ {X} {Y} → ≈i-isEquivalence {X} {Y}
    ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} fh gk →
                     ∘-resp-≈i {X} {Y} {Z}
                                {F₁ = g} {F₂ = k}
                                {G₁ = f} {G₂ = h} gk fh
    ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                     assocFM {W = s W} {X = s X} {Y = s Y} {Z = s Z}
                             {f = mor f} {g = mor g} {h = mor h}
    ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                     sym-assocFM {W = s W} {X = s X} {Y = s Y} {Z = s Z}
                                 {f = mor f} {g = mor g} {h = mor h}
    ; identityˡ = λ {X} {Y} {f} →
                     identityˡFM {X = s X} {Y = s Y} {f = mor f}
    ; identityʳ = λ {X} {Y} {f} →
                     identityʳFM {X = s X} {Y = s Y} {f = mor f}
    ; identity² = λ {X} → identity²FM {X = s X}
    }
