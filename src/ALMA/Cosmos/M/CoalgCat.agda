------------------------------------------------------------------------
-- Category of M-Cosmos coalgebras, and the terminal coalgebra.
-- M-base replacement for the legacy Cosmos/CoalgCat.agda. Objects are
-- one-step state coalgebras (MO.Coalgebra over a state family Xst);
-- morphisms are state maps whose induced anamorphisms are bisimilar.
-- This is the carried, zero-subst encoding: the commutation is carried
-- as data, morphism equality is pointwise propositional equality on
-- the underlying state maps, and the terminal object is
-- unfold-coalgebra on CosmosM with ! = ana γ.
--
-- M-Cosmos 余代数范畴与终余代数。旧 Cosmos/CoalgCat.agda 的 M 底座
-- 替代。对象为一步状态余代数（状态族 Xst 上的 MO.Coalgebra）；态射为
-- 其诱导 anamorphism 互模拟的状态映射。这是携带式零 subst 编码：交换
-- 作为数据携带，态射等价取底层状态映射的逐点命题相等，终对象是
-- CosmosM 上的 unfold-coalgebra 且 ! = ana γ。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.CoalgCat where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid using (EqOn)
open import ALMA.Cosmos.M.Object as MO
open import ALMA.Cosmos.M.Terminal as MT

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)} where

  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

  module _ {ℓd : Level}
           (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i)) where

    -- An object: a one-step coalgebra structure on some state family.
    -- 对象：某状态族上的一步余代数结构。
    record CoalgObj : Set (lsuc (L ⊔ ℓd)) where
      constructor mkCoalg
      field
        Xst : MO.I C FC → Set L
        γ   : MO.Coalgebra C FC L Xst
    open CoalgObj public

    -- A morphism: a state map carrying the bisimulation that its image
    -- under δ's anamorphism rebuilds γ's anamorphism.
    -- 态射：状态映射，携带“其在 δ 的 anamorphism 下的像重建 γ 的
    -- anamorphism”这一互模拟。
    record Coalg⇒ (X Y : CoalgObj) : Set (L ⊔ ℓd) where
      field
        map  : ∀ i → Xst X i → Xst Y i
        comm : ∀ i x → MO.≈CosmosM C FC ≈CD
                         (MO.ana C FC (γ Y) i (map i x))
                         (MO.ana C FC (γ X) i x)
    open Coalg⇒ public

    private
      ≈M-trans = MT.≈CosmosM-trans {C = C} {FC = FC} ≈CD

    -- Identity state map; commutation is bisimulation reflexivity.
    -- 恒等状态映射；交换即互模拟自反性。
    idCoalg : ∀ X → Coalg⇒ X X
    idCoalg X .map _ x = x
    idCoalg X .comm i x =
      MO.≈CosmosM-refl C FC ≈CD (MO.ana C FC (γ X) i x)

    -- Composition: chain the two commutation bisimulations.
    -- 复合：串联两条交换互模拟。
    compCoalg : ∀ {X Y Z : CoalgObj}
              → Coalg⇒ Y Z → Coalg⇒ X Y → Coalg⇒ X Z
    compCoalg g f .map i x = map g i (map f i x)
    compCoalg g f .comm i x =
      ≈M-trans (comm g i (map f i x)) (comm f i x)

    -- Pointwise propositional equality of the underlying state maps;
    -- stronger than bisimulation, so no function extensionality is
    -- needed for the category laws.
    -- 底层状态映射的逐点命题相等；强于互模拟，故范畴律无需函数外延性。
    _≈Coalg_ : ∀ {X Y : CoalgObj} → Coalg⇒ X Y → Coalg⇒ X Y → Set L
    _≈Coalg_ f g = ∀ i x → map f i x ≡ map g i x

    -- Laws are inlined to avoid metavariable drift through the Coalg⇒
    -- alias.
    -- 范畴律内联，避免经 Coalg⇒ 别名产生元变量漂移。
    CoalgCatM : Category (lsuc (L ⊔ ℓd)) (L ⊔ ℓd) L
    CoalgCatM = record
      { Obj       = CoalgObj
      ; _⇒_       = Coalg⇒
      ; _≈_       = _≈Coalg_
      ; id        = λ {X} → idCoalg X
      ; _∘_       = λ {X Y Z} g f → compCoalg {X = X} {Y = Y} {Z = Z} g f
      ; assoc     = λ {_ _ _ _} {_ _ _} i x → refl
      ; sym-assoc = λ {_ _ _ _} {_ _ _} i x → refl
      ; identityˡ = λ {_ _} {f} i x → refl
      ; identityʳ = λ {_ _} {f} i x → refl
      ; identity² = λ {_} i x → refl
      ; equiv     = record
        { refl  = λ {_} i x → refl
        ; sym   = λ {_ _} e i x → sym (e i x)
        ; trans = λ {_ _ _} e₁ e₂ i x → trans (e₁ i x) (e₂ i x)
        }
      ; ∘-resp-≈  = λ {_ _ _} {f} {k} {g} {j} f≈ g≈ i x →
          trans (cong (map f i) (g≈ i x)) (f≈ i (map j i x))
      }

    -- The terminal coalgebra: state family CosmosM with the observation
    -- coalgebra unfold-coalgebra; the unique morphism into it is the
    -- anamorphism.
    -- 终余代数：状态族为 CosmosM，余代数为观察余代数 unfold-coalgebra；
    -- 到终余代数的唯一态射即 anamorphism。
    ! : ∀ X → Coalg⇒ X (mkCoalg (MO.CosmosM C FC) (MO.unfold-coalgebra C FC))
    ! X .map i x = MO.ana C FC (γ X) i x
    ! X .comm i x = MO.ana-unfold C FC ≈CD (MO.ana C FC (γ X) i x)

    -- Uniqueness up to bisimulation: eta gives t ≈ ana unfold t, the
    -- morphism's commutation gives ana unfold t ≈ ana γ, and
    -- transitivity closes it with no dependent rewriting.
    -- 互模拟意义下的唯一性：eta 给出 t ≈ ana unfold t，态射交换给出
    -- ana unfold t ≈ ana γ，传递性闭合，无依赖重写。
    !-unique : ∀ X
                 (f : Coalg⇒ X (mkCoalg (MO.CosmosM C FC)
                                        (MO.unfold-coalgebra C FC)))
                 i x
             → MO.≈CosmosM C FC ≈CD
                 (map f i x) (MO.ana C FC (γ X) i x)
    !-unique X f i x =
      ≈M-trans (MO.ana-unfold˘ C FC ≈CD (map f i x)) (comm f i x)

    record IsTerminalUpToBisim : Set (lsuc (L ⊔ ℓd)) where
      field
        bang        : ∀ X → Coalg⇒ X
                         (mkCoalg (MO.CosmosM C FC) (MO.unfold-coalgebra C FC))
        bang-unique : ∀ X
                        (f : Coalg⇒ X
                          (mkCoalg (MO.CosmosM C FC) (MO.unfold-coalgebra C FC)))
                        i x
                    → MO.≈CosmosM C FC ≈CD
                        (map f i x) (MO.ana C FC (γ X) i x)

    cosmosMIsTerminal : IsTerminalUpToBisim
    cosmosMIsTerminal = record
      { bang        = !
      ; bang-unique = !-unique
      }
