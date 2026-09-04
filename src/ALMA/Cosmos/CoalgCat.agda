------------------------------------------------------------------------
-- Category of F-coalgebras and terminal object packaging
-- F-余代数范畴与终对象封装
--
-- Constructs CoalgCat: objects are CosmosF-coalgebras, morphisms are
-- coalgebra homomorphisms, equivalence is pointwise propositional equality.
-- Packages cosmosCoalg as terminal up to bisimulation _≈C_, without funext
-- or proof irrelevance (strengthening to _≡_ would require both).
-- 构造 CoalgCat：对象为 CosmosF-余代数，态射为余代数同态，等价为逐点命题相等。
-- 将 cosmosCoalg 封装为互模拟 _≈C_ 意义下的终对象（无需函数外延性与证明无关性；
-- 强化到 _≡_ 需要二者）。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.CoalgCat where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (id)
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos using (module CosmosMap)
open import ALMA.Cosmos.Terminal
  using (Coalgebra; CoalgHom; cosmosCoalg; ana-hom; unique-ana; _≈C_)

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p
    module Coal = Coalgebra
    module Hom  = CoalgHom

    -- Pin C/FC explicitly to avoid metavariable leakage from Terminal's anonymous module.
    -- 显式指定 C/FC，避免 Terminal 匿名模块中的元变量泄漏。
    Coalgebra′ : Set (lsuc L)
    Coalgebra′ = Coalgebra {o} {h} {e} {s} {p} {C} {FC}

    CoalgHom′ : Coalgebra′ → Coalgebra′ → Set L
    CoalgHom′ = CoalgHom {o} {h} {e} {s} {p} {C} {FC}

  -- Same as above: explicit C/FC for CosmosMap.
  -- 同上：为 CosmosMap 显式指定 C/FC。
  open CosmosMap {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}
    using (mapCosmosF; map-id; map-∘)

  -- Identity and composition of coalgebra homomorphisms
  -- 余代数同态的恒等与复合
  idCoalg : ∀ {X : Coalgebra′} → CoalgHom′ X X
  idCoalg {X} = record
    { f       = record { to = id; cong = λ eq → eq }
    ; commute = λ x → map-id (Func.to (Coal.α X) x)
    }

  -- Composition: map-∘ reduces mapCosmosF (g∘f) to mapCosmosF g ∘ mapCosmosF f,
  -- then f.commute and g.commute chain to Z.α.
  -- 复合：map-∘ 将 mapCosmosF (g∘f) 归约为 mapCosmosF g ∘ mapCosmosF f，
  -- 再经 f.commute 与 g.commute 链式得到 Z.α。
  _∘Coalg_ : ∀ {X Y Z : Coalgebra′}
           → CoalgHom′ Y Z → CoalgHom′ X Y → CoalgHom′ X Z
  _∘Coalg_ {X} {Y} {Z} g f = record
    { f       = record
      { to   = λ x → Func.to (Hom.f g) (Func.to (Hom.f f) x)
      ; cong = λ x≈y → Func.cong (Hom.f g) (Func.cong (Hom.f f) x≈y)
      }
    ; commute = λ x → begin
        mapCosmosF (λ x → Func.to (Hom.f g) (Func.to (Hom.f f) x)) (Func.to (Coal.α X) x)
          ≡⟨ map-∘ (Func.to (Hom.f g)) (Func.to (Hom.f f)) (Func.to (Coal.α X) x) ⟩
        mapCosmosF (Func.to (Hom.f g)) (mapCosmosF (Func.to (Hom.f f)) (Func.to (Coal.α X) x))
          ≡⟨ cong (mapCosmosF (Func.to (Hom.f g))) (Hom.commute f x) ⟩
        mapCosmosF (Func.to (Hom.f g)) (Func.to (Coal.α Y) (Func.to (Hom.f f) x))
          ≡⟨ Hom.commute g (Func.to (Hom.f f) x) ⟩
        Func.to (Coal.α Z) (Func.to (Hom.f g) (Func.to (Hom.f f) x))
      ∎
    }

  -- Pointwise _≡_ on underlying functions; stronger than _≈C_
  -- 底层函数的逐点 _≡_；强于 _≈C_
  _≈Coalg_ : ∀ {X Y : Coalgebra′} → CoalgHom′ X Y → CoalgHom′ X Y → Set L
  _≈Coalg_ f g = ∀ x → Func.to (Hom.f f) x ≡ Func.to (Hom.f g) x

  -- Category instance
  -- 范畴实例
  -- Laws are inlined: top-level helpers cause metavariable drift via CoalgHom′.
  -- ∘-resp-≈: outer f≈, then inner g≈; proofs end in (x).
  -- 范畴律内联编写：顶层辅助函数会导致 CoalgHom′ 别名上的元变量漂移。
  -- ∘-resp-≈：先外层 f≈，再内层 g≈；证明以 (x) 结尾。
  CoalgCat : Category (lsuc L) L L
  CoalgCat = record
    { Obj       = Coalgebra′
    ; _⇒_       = CoalgHom′
    ; _≈_       = _≈Coalg_
    ; id        = idCoalg
    ; _∘_       = _∘Coalg_
    ; assoc     = λ {A B C D} {f g h} x → refl
    ; sym-assoc = λ {A B C D} {f g h} x → refl
    ; identityˡ = λ {A B} {f} x → refl
    ; identityʳ = λ {A B} {f} x → refl
    ; identity² = λ {A} x → refl
    ; equiv     = λ {A B} → record
      { refl  = λ {f} _ → refl
      ; sym   = λ {f g} eq x → sym (eq x)
      ; trans = λ {f g h} eq1 eq2 x → trans (eq1 x) (eq2 x)
      }
    ; ∘-resp-≈  = λ {A B C} {f h : CoalgHom′ B C} {g i : CoalgHom′ A B}
                  f≈ g≈ x →
        trans (f≈ (Func.to (Hom.f g) x)) (cong (Func.to (Hom.f h)) (g≈ x))
    }

  -- Terminal object up to bisimulation
  -- 互模拟意义下的终对象
  -- Uniqueness only up to _≈C_; upgrading to _≡_ needs funext + proof irrelevance.
  -- 唯一性仅到互模拟 _≈C_；强化到 _≡_ 需要函数外延性与证明无关性。
  record IsTerminalUpToBisim : Set (lsuc L) where
    field
      !        : (X : Coalgebra′) → CoalgHom′ X cosmosCoalg
      !-unique : ∀ {X : Coalgebra′} (f : CoalgHom′ X cosmosCoalg)
               → ∀ x → Func.to (Hom.f f) x ≈C Func.to (Hom.f (! X)) x

  -- cosmosCoalg is terminal up to _≈C_: ! = ana-hom, uniqueness = unique-ana.
  -- cosmosCoalg 在 _≈C_ 意义下为终对象：! = ana-hom，唯一性 = unique-ana。
  cosmosIsTerminal : IsTerminalUpToBisim
  cosmosIsTerminal = record
    { !        = ana-hom
    ; !-unique = λ {X} f x → unique-ana X f x
    }
