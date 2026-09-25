------------------------------------------------------------------------
-- FinCat∞ projection: tower embedding, layer-0 projection, and its
-- faithfulness and conservativity
-- FinCat∞ 投影：塔嵌入、层 0 投影，及其忠实性与保守性
--
-- Along the tower family {FinCatN m} (m → ∞), provides the tower-family
-- embedding embedN and colimit injection projN at the functor level,
-- together with the cocone condition projN (suc m) ∘ embedN m ≅ projN m;
-- and the layer-0 projection projCosmos with its faithfulness (separation
-- is preserved) and conservativity (bisimulation is reflected), so that
-- the projection neither erases nor fabricates bisimulation information
-- between FinCatN and FinCat∞
-- 沿塔族 {FinCatN m}（m → ∞），提供函子层面的塔族嵌入 embedN 与余极限注入
-- projN，以及余锥条件 projN (suc m) ∘ embedN m ≅ projN m；
-- 并提供层 0 投影 projCosmos 及其忠实性（区分保持）与保守性（互模拟反映），
-- 使投影在 FinCatN 与 FinCat∞ 之间既不擦除也不捏造互模拟信息
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCatInfinityProjection where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; z≤n; s≤s; ≤-pred)
open import Data.Nat.Properties using (≤-trans; <-irrefl; 1+n≢n)
open import Data.Fin.Base using (Fin; toℕ; inject₁)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-injective; toℕ<n)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; subst; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (_∘_)

open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)

open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Unfolding using (Unfolding; module Unfolding)
open import ALMA.Cosmos.Terminal using (_≈C_)
open _≈C_
open import ALMA.Cosmos.FinCatNWitness
open import ALMA.Cosmos.FinCatInfinity

-- Tower-family embedding and colimit injection (functor level)
-- 塔族嵌入与余极限注入（函子层面）
module FinCatInfinityEmbedding (m : ℕ) where

  module M = FinCatN m
  module S = FinCatN (suc m)
  open M

  -- Tower-family embedding: F₀ = inject₁, F₁ = tt
  -- 塔族嵌入：F₀ = inject₁，F₁ = tt
  embedN : Functor M.FinCatN S.FinCatN
  embedN = record
    { F₀           = inject₁
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  -- Colimit injection ι_m : FinCatN m → FinCat∞, F₀ = toℕ
  -- 余极限注入 ι_m : FinCatN m → FinCat∞，F₀ = toℕ
  projN : Functor M.FinCatN FinCat∞
  projN = record
    { F₀           = toℕ
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  projN-suc : Functor S.FinCatN FinCat∞
  projN-suc = record
    { F₀           = toℕ
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  projN∘embedN : Functor M.FinCatN FinCat∞
  projN∘embedN = record
    { F₀           = λ x → toℕ (inject₁ x)
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  -- Cocone condition: toℕ ∘ inject₁ ≡ toℕ
  -- 余锥条件：toℕ ∘ inject₁ ≡ toℕ
  embedN-projN-F₀
    : ∀ (x : Fin M.n)
    → Functor.F₀ projN∘embedN x ≡ Functor.F₀ projN x
  embedN-projN-F₀ x =
    begin
      toℕ (inject₁ x) ≡⟨ toℕ-inject₁ x ⟩
      toℕ x           ∎

  -- projN (suc m) ∘ embedN m ≃ projN m
  embedN-projN-iso : NaturalIsomorphism projN∘embedN projN
  embedN-projN-iso = record
    { F⇒G = ntHelper record
        { η       = λ _ → tt
        ; commute = λ _ → refl
        }
    ; F⇐G = ntHelper record
        { η       = λ _ → tt
        ; commute = λ _ → refl
        }
    ; iso = λ _ → record { isoˡ = refl ; isoʳ = refl }
    }

-- Layer-0 projection projCosmos and faithfulness
-- 层 0 投影 projCosmos 与忠实性

-- finFromℕ-maybe budget k: Fin (suc budget) from ℕ, nothing if out of range
-- finFromℕ-maybe budget k：由 ℕ 构造 Fin (suc budget)，越界返回 nothing
finFromℕ-maybe : ∀ (budget : ℕ) (k : ℕ) → Maybe (Fin (suc budget))
finFromℕ-maybe _       zero    = just fzero
finFromℕ-maybe zero    (suc _) = nothing
finFromℕ-maybe (suc b) (suc k) = map fsuc (finFromℕ-maybe b k)

fromMaybe : ∀ {a} {A : Set a} → A → Maybe A → A
fromMaybe d nothing = d
fromMaybe d (just x) = x

isNothing : ∀ {a} {A : Set a} → Maybe A → Set
isNothing nothing = ⊤
isNothing (just _) = ⊥

toℕ-maybe₀ : ∀ {n} → Maybe (Fin n) → ℕ
toℕ-maybe₀ nothing = 0
toℕ-maybe₀ (just x) = toℕ x

just-injective : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
just-injective {x = x} eq = cong (fromMaybe x) eq

nothing-not-just : ∀ {a} {A : Set a} {x : A} → nothing ≢ just x
nothing-not-just eq = subst isNothing eq tt

private
  record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
    (f : (x : A) → B x) (x : A) (y : B x) : Set (a ⊔ b) where
    constructor [_]
    field eq : f x ≡ y

  inspect : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) (x : A)
          → Reveal f · x is (f x)
  inspect f x = [ refl ]

toℕ-finFromℕ-maybe : ∀ budget k (x : Fin (suc budget))
  → finFromℕ-maybe budget k ≡ just x → toℕ x ≡ k
toℕ-finFromℕ-maybe _       zero    x eq = sym (cong toℕ-maybe₀ eq)
toℕ-finFromℕ-maybe zero    (suc _) x eq = ⊥-elim (nothing-not-just eq)
toℕ-finFromℕ-maybe (suc b) (suc k) x eq
  with finFromℕ-maybe b k | inspect (finFromℕ-maybe b) k
... | nothing | [ eq' ] = ⊥-elim (nothing-not-just eq)
... | just y  | [ eq' ] =
  begin
    toℕ x
      ≡⟨ cong toℕ (sym (just-injective eq)) ⟩
    suc (toℕ y)
      ≡⟨ cong suc (toℕ-finFromℕ-maybe b k y eq') ⟩
    suc k
  ∎

finFromℕ-maybe-just⇒≤ : ∀ budget k (x : Fin (suc budget))
  → finFromℕ-maybe budget k ≡ just x → k ≤ budget
finFromℕ-maybe-just⇒≤ budget k x eq =
  subst (λ z → z ≤ budget) (toℕ-finFromℕ-maybe budget k x eq)
    (≤-pred (toℕ<n x))

finFromℕ-maybe-nothing⇒> : ∀ budget k
  → finFromℕ-maybe budget k ≡ nothing → suc budget ≤ k
finFromℕ-maybe-nothing⇒> zero    zero    ()
finFromℕ-maybe-nothing⇒> zero    (suc k) _  = s≤s z≤n
finFromℕ-maybe-nothing⇒> (suc b) zero    ()
finFromℕ-maybe-nothing⇒> (suc b) (suc k) eq =
  s≤s (finFromℕ-maybe-nothing⇒> b k (map-nothing eq))
  where
  map-nothing : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {mx : Maybe A}
    → map f mx ≡ nothing → mx ≡ nothing
  map-nothing {mx = nothing}  _  = refl
  map-nothing {mx = just _}   eq = ⊥-elim (nothing-not-just (sym eq))

module FinCatNColimitProjection (m : ℕ) where
  open FinCatN m

  -- extendFin: f on the range, identity outside
  -- extendFin：范围内用 f，范围外恒等
  extendFin : (Fin n → Fin n) → ℕ → ℕ
  extendFin f k = fromMaybe k (map (toℕ ∘ f) (finFromℕ-maybe (n ∸ 1) k))

  -- defaultFin: finFromℕ-maybe result if in range, else fzero
  -- defaultFin：范围内取 finFromℕ-maybe 结果，否则 fzero
  defaultFin : ℕ → Fin n
  defaultFin k = fromMaybe fzero (finFromℕ-maybe (n ∸ 1) k)

  extendFin-id : ∀ k → extendFin (λ x → x) k ≡ k
  extendFin-id k
    with finFromℕ-maybe (n ∸ 1) k | inspect (finFromℕ-maybe (n ∸ 1)) k
  ... | nothing | [ _ ]  = refl
  ... | just x  | [ eq ] = toℕ-finFromℕ-maybe (n ∸ 1) k x eq

  -- cosmos-id∞: F₀ = proj₁ on FinCat∞
  -- cosmos-id∞：FinCat∞ 上 F₀ = proj₁ 的宇宙
  cosmos-id∞ : Cosmos FinCat∞ TrivialFC∞
  cosmos-id∞ .out = record
    { unfoldFunctor = record
      { F₀           = proj₁
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ _ → cosmos-id∞
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- cosmos-mapN f: F₀ = f ∘ proj₁, constant unfold-next
  -- cosmos-mapN f：F₀ = f ∘ proj₁，unfold-next 常数
  cosmos-mapN : (Fin n → Fin n) → Cosmos FinCatN TrivialFCN
  cosmos-mapN f .out = record
    { unfoldFunctor = record
      { F₀           = λ { (A , _) → f A }
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ _ → cosmos-mapN f
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- projCosmos: layer-0 projection, F₀ is extendFin of input F₀
  -- projCosmos：层 0 投影，F₀ 为输入 F₀ 的 extendFin
  projCosmos : Cosmos FinCatN TrivialFCN → Cosmos FinCat∞ TrivialFC∞
  projCosmos x .out = record
    { unfoldFunctor = record
      { F₀           = λ { (k , _) →
          extendFin (λ A → Functor.F₀ UX.unfoldFunctor (A , lift tt)) k }
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ { {k} _ →
        projCosmos (UX.unfold-next {A = defaultFin k} (lift tt)) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }
    where
      UX = out x
      module UX = Unfolding UX

  projCosmos-F₀-spec
    : ∀ (x : Cosmos FinCatN TrivialFCN) (k : ℕ)
    → Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos x))) (k , lift tt)
      ≡ extendFin (λ A → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A , lift tt)) k
  projCosmos-F₀-spec x k = refl

  -- projCosmos cosmos-idN ≈C cosmos-id∞
  projCosmos-id : projCosmos cosmos-idN ≈C cosmos-id∞
  projCosmos-id .unfoldFunctor₀-eq {A} _ =
    begin
      extendFin (λ x → x) A ≡⟨ extendFin-id A ⟩
      A                     ∎
  projCosmos-id .pos-to-shape-eq _ _ = refl
  projCosmos-id .unfold-next-eq _    = projCosmos-id

  -- Faithfulness: extendFin separation yields non-bisimilarity
  -- 忠实性：extendFin 的分离蕴含不互模拟
  faithfulness
    : ∀ (f g : Fin n → Fin n)
    → Σ ℕ (λ k → extendFin f k ≢ extendFin g k)
    → ¬ (projCosmos (cosmos-mapN f) ≈C projCosmos (cosmos-mapN g))
  faithfulness f g (k , neq) eq =
    neq (begin
      extendFin f k
        ≡˘⟨ specF ⟩
      Ff
        ≡⟨ eqF ⟩
      Fg
        ≡⟨ specG ⟩
      extendFin g k
      ∎)
    where
      Ff = Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos (cosmos-mapN f))))
                     (k , lift tt)
      Fg = Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos (cosmos-mapN g))))
                     (k , lift tt)
      eqF   : Ff ≡ Fg
      eqF   = unfoldFunctor₀-eq eq {A = k} (lift tt)
      specF : Ff ≡ extendFin f k
      specF = projCosmos-F₀-spec (cosmos-mapN f) k
      specG : Fg ≡ extendFin g k
      specG = projCosmos-F₀-spec (cosmos-mapN g) k

  -- finFromℕ-maybe returns just when k is in range
  -- finFromℕ-maybe 在 k 处于范围内时返回 just
  finFromℕ-maybe-in-range
    : ∀ budget k → k ≤ budget
    → Σ (Fin (suc budget)) (λ x → finFromℕ-maybe budget k ≡ just x)
  finFromℕ-maybe-in-range budget k k≤budget
      with finFromℕ-maybe budget k in eq0
  ... | just x  = x , refl
  ... | nothing = ⊥-elim (<-irrefl refl
        (≤-trans (finFromℕ-maybe-nothing⇒> budget k eq0) k≤budget))

  -- toℕ A is within range of finFromℕ-maybe (n ∸ 1)
  -- toℕ A 在 finFromℕ-maybe (n ∸ 1) 的范围内
  toℕ≤n∸1 : ∀ (A : Fin n) → toℕ A ≤ n ∸ 1
  toℕ≤n∸1 A = ≤-pred (toℕ<n A)

  -- In-range application returns the element itself
  -- 范围内应用返回元素自身
  finFromℕ-maybe-just-self
    : ∀ (A : Fin n) → finFromℕ-maybe (n ∸ 1) (toℕ A) ≡ just A
  finFromℕ-maybe-just-self A =
    let (x , eq) = finFromℕ-maybe-in-range (n ∸ 1) (toℕ A) (toℕ≤n∸1 A)
        x≡A : x ≡ A
        x≡A = toℕ-injective (toℕ-finFromℕ-maybe (n ∸ 1) (toℕ A) x eq)
    in begin
        finFromℕ-maybe (n ∸ 1) (toℕ A)
          ≡⟨ eq ⟩
        just x
          ≡⟨ cong just x≡A ⟩
        just A
      ∎

  -- defaultFin (toℕ A) = A
  -- defaultFin (toℕ A) = A
  defaultFin-toℕ-self : ∀ (A : Fin n) → defaultFin (toℕ A) ≡ A
  defaultFin-toℕ-self A = cong (fromMaybe fzero) (finFromℕ-maybe-just-self A)

  -- extendFin f (toℕ A) = toℕ (f A)
  -- extendFin f (toℕ A) = toℕ (f A)
  extendFin-at-toℕ : ∀ (f : Fin n → Fin n) (A : Fin n)
    → extendFin f (toℕ A) ≡ toℕ (f A)
  extendFin-at-toℕ f A rewrite finFromℕ-maybe-just-self A = refl

  -- Conservativity: projCosmos reflects bisimulation
  -- 保守性：projCosmos 反映互模拟
  projCosmos-conservative
    : ∀ (x y : Cosmos FinCatN TrivialFCN)
    → projCosmos x ≈C projCosmos y → x ≈C y
  projCosmos-conservative x y eq .unfoldFunctor₀-eq {A = A} (lift tt) =
    toℕ-injective (begin
      toℕ (Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A , lift tt))
        ≡˘⟨ extendFin-at-toℕ
              (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A' , lift tt)) A ⟩
      extendFin (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A' , lift tt)) (toℕ A)
        ≡˘⟨ projCosmos-F₀-spec x (toℕ A) ⟩
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos x))) (toℕ A , lift tt)
        ≡⟨ eq .unfoldFunctor₀-eq {A = toℕ A} (lift tt) ⟩
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos y))) (toℕ A , lift tt)
        ≡⟨ projCosmos-F₀-spec y (toℕ A) ⟩
      extendFin (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A' , lift tt)) (toℕ A)
        ≡⟨ extendFin-at-toℕ
             (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A' , lift tt)) A ⟩
      toℕ (Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A , lift tt))
      ∎)
  projCosmos-conservative x y eq .pos-to-shape-eq _ _ = refl
  projCosmos-conservative x y eq .unfold-next-eq {A = k} s
    rewrite sym (defaultFin-toℕ-self k)
    = projCosmos-conservative
        (Unfolding.unfold-next (out x) {A = defaultFin (toℕ k)} (lift tt))
        (Unfolding.unfold-next (out y) {A = defaultFin (toℕ k)} (lift tt))
        (eq .unfold-next-eq {A = toℕ k} s)

  -- Concrete witness: swap01 vs swap12 on Fin 3 differ at k = 1
  -- 具体见证：Fin 3 上 swap01 与 swap12 在 k = 1 处不同
  module _ (m=1 : m ≡ 1) where
    private
      f0 : Fin 3
      f0 = fzero
      f1 : Fin 3
      f1 = fsuc fzero
      f2 : Fin 3
      f2 = fsuc (fsuc fzero)

      swap01 : Fin 3 → Fin 3
      swap01 x with toℕ x
      ... | zero        = f1
      ... | suc zero    = f0
      ... | suc (suc _) = f2

      swap12 : Fin 3 → Fin 3
      swap12 x with toℕ x
      ... | zero        = f0
      ... | suc zero    = f2
      ... | suc (suc _) = f1

      n=3 : n ≡ 3
      n=3 = cong (suc ∘ suc) m=1

      -- Composition of the two swaps on Fin 3
      -- Fin 3 上两个对换的复合
      swap01∘swap12 : Fin 3 → Fin 3
      swap01∘swap12 = swap01 ∘ swap12

      swap12∘swap01 : Fin 3 → Fin 3
      swap12∘swap01 = swap12 ∘ swap01

    swap01≢swap12-at-1
      : extendFin (subst (λ n' → Fin n' → Fin n') (sym n=3) swap01) 1
        ≢ extendFin (subst (λ n' → Fin n' → Fin n') (sym n=3) swap12) 1
    swap01≢swap12-at-1 rewrite m=1 = λ ()

    swap01∞≉swap12∞
      : ¬ (projCosmos (cosmos-mapN (subst (λ n' → Fin n' → Fin n') (sym n=3) swap01))
           ≈C
           projCosmos (cosmos-mapN (subst (λ n' → Fin n' → Fin n') (sym n=3) swap12)))
    swap01∞≉swap12∞ =
      faithfulness _ _ (1 , swap01≢swap12-at-1)

    -- Non-commutativity separates at k = 0:
    --   extendFin (swap01 ∘ swap12) 0 = 1, extendFin (swap12 ∘ swap01) 0 = 2
    -- 非交换性在 k = 0 处分离：
    --   extendFin (swap01 ∘ swap12) 0 = 1，extendFin (swap12 ∘ swap01) 0 = 2
    swap01∘swap12≠swap12∘swap01-at-0
      : extendFin (subst (λ n' → Fin n' → Fin n') (sym n=3) swap01∘swap12) 0
        ≢ extendFin (subst (λ n' → Fin n' → Fin n') (sym n=3) swap12∘swap01) 0
    swap01∘swap12≠swap12∘swap01-at-0 rewrite m=1 =
      λ eq → 1+n≢n {1} (sym eq)

    -- The projected cosmoi of the two composition orders are non-bisimilar
    -- 两种复合顺序的投影宇宙不互模拟
    swap01∘swap12∞≉swap12∘swap01∞
      : ¬ (projCosmos (cosmos-mapN
             (subst (λ n' → Fin n' → Fin n') (sym n=3) swap01∘swap12))
           ≈C
           projCosmos (cosmos-mapN
             (subst (λ n' → Fin n' → Fin n') (sym n=3) swap12∘swap01)))
    swap01∘swap12∞≉swap12∘swap01∞ =
      faithfulness _ _ (0 , swap01∘swap12≠swap12∘swap01-at-0)
