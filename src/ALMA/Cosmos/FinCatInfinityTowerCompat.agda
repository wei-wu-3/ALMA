------------------------------------------------------------------------
-- Tower embedding compatibility: projCosmos (suc m) ∘ embedCosmos m ≈C projCosmos m
-- 塔嵌入兼容性：projCosmos (suc m) ∘ embedCosmos m ≈C projCosmos m
--
-- embedCosmos m embeds a cosmos on FinCatN m into FinCatN (suc m):
--   F₀ = embedF₀ f: on the inject₁ image apply f then inject₁, on the new
--   element identity; unfold-next = embedCosmos m ∘ UX.unfold-next after
--   restricting the shape object
-- The key lemma extendFin-embedF₀ says extendFin (embedF₀ f) ≡ extendFin f,
-- so the F₀ components of the two projections agree. The unfold-next
-- components agree because restrictFin (defaultFin' k) ≡ defaultFin k
-- This is the colimit cocone compatibility at the cosmos level
-- embedCosmos m 将层 m 宇宙嵌入层 suc m：
--   F₀ = embedF₀ f：在 inject₁ 像上应用 f 再注入，新元素上恒等；
--   unfold-next = 限制形状对象后递归应用 embedCosmos m
-- 关键引理 extendFin-embedF₀ 表明 extendFin (embedF₀ f) ≡ extendFin f，
-- 因此两个投影的 F₀ 分量一致。unfold-next 分量因
-- restrictFin (defaultFin' k) ≡ defaultFin k 一致
-- 这是余极限余锥在宇宙层面的相容性
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCatInfinityTowerCompat where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Nat using (ℕ; suc; _∸_; _≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; 1+n≰n; m≤n⇒m≤1+n )
open import Data.Fin.Base using (Fin; toℕ; inject₁) renaming (zero to fzero)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-injective)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (inspect; [_])
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (_∘_)

open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Unfolding using (Unfolding; module Unfolding)
open import ALMA.Cosmos.Terminal using (_≈C_)
open _≈C_
open import ALMA.Cosmos.FinCatNWitness
open import ALMA.Cosmos.FinCatInfinity
open import ALMA.Cosmos.FinCatInfinityProjection

module FinCatTowerCompat (m : ℕ) where
  module M  = FinCatN m
  module S  = FinCatN (suc m)
  module PM = FinCatNColimitProjection m
  module PS = FinCatNColimitProjection (suc m)
  open M
  open S using () renaming (n to n′; FinCatN to FinCatN′; TrivialFCN to TrivialFCN′)
  open PM using ( extendFin; defaultFin; projCosmos; cosmos-mapN
                ; extendFin-id; projCosmos-F₀-spec )
  open PS using () renaming ( extendFin to extendFin′; defaultFin to defaultFin′
                            ; projCosmos to projCosmos′; cosmos-mapN to cosmos-mapN′ )

  -- n′ = suc n definitionally (n-at (suc m) = suc (n-at m))
  -- n′ = suc n（定义性，n-at (suc m) = suc (n-at m)）

  -- embedF₀ f: lift f from Fin n → Fin n to Fin n′ → Fin n′
  -- embedF₀ f：将 f 从 Fin n → Fin n 提升到 Fin n′ → Fin n′
  embedF₀ : (Fin n → Fin n) → Fin n′ → Fin n′
  embedF₀ f x′ with finFromℕ-maybe (n ∸ 1) (toℕ x′)
  ... | nothing = x′
  ... | just y  = inject₁ (f y)

  -- embedF₀ on inject₁ y: inject₁ (f y)
  -- embedF₀ 在 inject₁ y 上：inject₁ (f y)
  embedF₀-on-inject₁ : ∀ (f : Fin n → Fin n) (y : Fin n)
    (eq : finFromℕ-maybe (n ∸ 1) (toℕ y) ≡ just y)
    → embedF₀ f (inject₁ y) ≡ inject₁ (f y)
  embedF₀-on-inject₁ f y eq rewrite toℕ-inject₁ y | eq = refl

  -- embedF₀ on the new element (toℕ x′ > n ∸ 1): identity
  -- embedF₀ 在新元素上（toℕ x′ > n ∸ 1）：恒等
  embedF₀-on-new : ∀ (f : Fin n → Fin n) (x′ : Fin n′)
    (eq : finFromℕ-maybe (n ∸ 1) (toℕ x′) ≡ nothing)
    → embedF₀ f x′ ≡ x′
  embedF₀-on-new f x′ eq rewrite eq = refl

  -- restrictFin: project Fin n′ back to Fin n, default fzero if out of range
  -- restrictFin：将 Fin n′ 投影回 Fin n，越界默认 fzero
  restrictFin : Fin n′ → Fin n
  restrictFin x′ with finFromℕ-maybe (n ∸ 1) (toℕ x′)
  ... | nothing = fzero
  ... | just y  = y

  -- embedCosmos: embed a cosmos on FinCatN into FinCatN′
  -- embedCosmos：将宇宙从 FinCatN 嵌入 FinCatN′
  embedCosmos : Cosmos FinCatN TrivialFCN → Cosmos FinCatN′ TrivialFCN′
  embedCosmos x .out = record
    { unfoldFunctor = record
      { F₀           = λ { (A , _) →
          embedF₀ (λ A₁ → Functor.F₀ UX.unfoldFunctor (A₁ , lift tt)) A }
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ { {A} _ →
        embedCosmos (UX.unfold-next {A = restrictFin A} (lift tt)) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }
    where
      UX = out x
      module UX = Unfolding UX

  -- toℕ (embedF₀ f x′) ≡ extendFin f (toℕ x′)
  -- toℕ (embedF₀ f x′) ≡ extendFin f (toℕ x′)
  toℕ-embedF₀ : ∀ (f : Fin n → Fin n) (x′ : Fin n′)
    → toℕ (embedF₀ f x′) ≡ extendFin f (toℕ x′)
  toℕ-embedF₀ f x′
    with finFromℕ-maybe (n ∸ 1) (toℕ x′)
  ... | just y  = toℕ-inject₁ (f y)
  ... | nothing = refl

  extendFin-toℕx′ : ∀ f x′ k y
    (eqn : finFromℕ-maybe n k ≡ just x′)
    (eqm : finFromℕ-maybe (n ∸ 1) k ≡ just y)
    → extendFin f (toℕ x′) ≡ toℕ (f y)
  extendFin-toℕx′ f x′ k y eqn eqm
    with finFromℕ-maybe (n ∸ 1) (toℕ x′)
       | inspect (finFromℕ-maybe (n ∸ 1)) (toℕ x′)
  ... | just z  | [ eqz ] =
      cong (toℕ ∘ f) (toℕ-injective (begin
        toℕ z
          ≡⟨ toℕ-finFromℕ-maybe (n ∸ 1) (toℕ x′) z eqz ⟩
        toℕ x′
          ≡⟨ toℕ-finFromℕ-maybe n k x′ eqn ⟩
        k
          ≡˘⟨ toℕ-finFromℕ-maybe (n ∸ 1) k y eqm ⟩
        toℕ y
        ∎))
  ... | nothing | [ eqz ] =
      ⊥-elim (1+n≰n {n ∸ 1} (≤-trans
        (subst (λ w → suc (n ∸ 1) ≤ w) (toℕ-finFromℕ-maybe n k x′ eqn)
          (finFromℕ-maybe-nothing⇒> (n ∸ 1) (toℕ x′) eqz))
        (finFromℕ-maybe-just⇒≤ (n ∸ 1) k y eqm)))

  extendFin-toℕx′-nothing : ∀ f x′ k
    (eqn : finFromℕ-maybe n k ≡ just x′)
    (eqm : finFromℕ-maybe (n ∸ 1) k ≡ nothing)
    → extendFin f (toℕ x′) ≡ k
  extendFin-toℕx′-nothing f x′ k eqn eqm
    with finFromℕ-maybe (n ∸ 1) (toℕ x′)
       | inspect (finFromℕ-maybe (n ∸ 1)) (toℕ x′)
  ... | just z  | [ eqz ] =
      ⊥-elim (1+n≰n {n ∸ 1} (≤-trans
        (finFromℕ-maybe-nothing⇒> (n ∸ 1) k eqm)
        (subst (_≤ n ∸ 1) (toℕ-finFromℕ-maybe n k x′ eqn)
          (finFromℕ-maybe-just⇒≤ (n ∸ 1) (toℕ x′) z eqz))))
  ... | nothing | [ eqz ] =
      toℕ-finFromℕ-maybe n k x′ eqn

  restrictFin-x′ : ∀ x′ k y
    (eqn : finFromℕ-maybe n k ≡ just x′)
    (eqm : finFromℕ-maybe (n ∸ 1) k ≡ just y)
    → restrictFin x′ ≡ y
  restrictFin-x′ x′ k y eqn eqm
    with finFromℕ-maybe (n ∸ 1) (toℕ x′)
       | inspect (finFromℕ-maybe (n ∸ 1)) (toℕ x′)
  ... | just z  | [ eqz ] =
      toℕ-injective (begin
        toℕ z
          ≡⟨ toℕ-finFromℕ-maybe (n ∸ 1) (toℕ x′) z eqz ⟩
        toℕ x′
          ≡⟨ toℕ-finFromℕ-maybe n k x′ eqn ⟩
        k
          ≡˘⟨ toℕ-finFromℕ-maybe (n ∸ 1) k y eqm ⟩
        toℕ y
        ∎)
  ... | nothing | [ eqz ] =
      ⊥-elim (1+n≰n {n ∸ 1} (≤-trans
        (subst (λ w → suc (n ∸ 1) ≤ w) (toℕ-finFromℕ-maybe n k x′ eqn)
          (finFromℕ-maybe-nothing⇒> (n ∸ 1) (toℕ x′) eqz))
        (finFromℕ-maybe-just⇒≤ (n ∸ 1) k y eqm)))

  restrictFin-x′-nothing : ∀ x′ k
    (eqn : finFromℕ-maybe n k ≡ just x′)
    (eqm : finFromℕ-maybe (n ∸ 1) k ≡ nothing)
    → restrictFin x′ ≡ fzero
  restrictFin-x′-nothing x′ k eqn eqm
    with finFromℕ-maybe (n ∸ 1) (toℕ x′)
       | inspect (finFromℕ-maybe (n ∸ 1)) (toℕ x′)
  ... | just z  | [ eqz ] =
      ⊥-elim (1+n≰n {n ∸ 1} (≤-trans
        (finFromℕ-maybe-nothing⇒> (n ∸ 1) k eqm)
        (subst (_≤ n ∸ 1) (toℕ-finFromℕ-maybe n k x′ eqn)
          (finFromℕ-maybe-just⇒≤ (n ∸ 1) (toℕ x′) z eqz))))
  ... | nothing | [ eqz ] = refl

  -- Main lemma: extendFin′ (embedF₀ f) ≡ extendFin f
  -- 主引理：extendFin′ (embedF₀ f) ≡ extendFin f
  extendFin-embedF₀ : ∀ (f : Fin n → Fin n) (k : ℕ)
    → extendFin′ (embedF₀ f) k ≡ extendFin f k
  extendFin-embedF₀ f k
    with finFromℕ-maybe n k | inspect (finFromℕ-maybe n) k
       | finFromℕ-maybe (n ∸ 1) k | inspect (finFromℕ-maybe (n ∸ 1)) k
  ... | just x′ | [ eqn ] | just y  | [ eqm ] =
      trans (toℕ-embedF₀ f x′) (extendFin-toℕx′ f x′ k y eqn eqm)
  ... | just x′ | [ eqn ] | nothing | [ eqm ] =
      trans (toℕ-embedF₀ f x′) (extendFin-toℕx′-nothing f x′ k eqn eqm)
  ... | nothing | [ eqn ] | just y  | [ eqm ] =
      ⊥-elim (1+n≰n {n} (≤-trans
        (≤-trans (finFromℕ-maybe-nothing⇒> n k eqn)
                 (finFromℕ-maybe-just⇒≤ (n ∸ 1) k y eqm))
        (m≤n⇒m≤1+n (≤-refl {n ∸ 1}))))
  ... | nothing | [ eqn ] | nothing | [ eqm ] = refl

  restrictFin-defaultFin : ∀ k → restrictFin (defaultFin′ k) ≡ defaultFin k
  restrictFin-defaultFin k
    with finFromℕ-maybe n k | inspect (finFromℕ-maybe n) k
       | finFromℕ-maybe (n ∸ 1) k | inspect (finFromℕ-maybe (n ∸ 1)) k
  ... | just x′ | [ eqn ] | just y  | [ eqm ] =
      restrictFin-x′ x′ k y eqn eqm
  ... | just x′ | [ eqn ] | nothing | [ eqm ] =
      restrictFin-x′-nothing x′ k eqn eqm
  ... | nothing | [ eqn ] | just y  | [ eqm ] =
      ⊥-elim (1+n≰n {n} (≤-trans
        (≤-trans (finFromℕ-maybe-nothing⇒> n k eqn)
                 (finFromℕ-maybe-just⇒≤ (n ∸ 1) k y eqm))
        (m≤n⇒m≤1+n (≤-refl {n ∸ 1}))))
  ... | nothing | [ eqn ] | nothing | [ eqm ] = refl

  -- Main theorem: projCosmos′ (embedCosmos x) ≈C projCosmos x
  -- Defined by copattern matching so the recursive call is guarded by
  -- .unfold-next-eq (productivity).
  -- 主定理：projCosmos′ (embedCosmos x) ≈C projCosmos x
  -- 通过 copattern 匹配定义，使递归调用受 .unfold-next-eq 保护（生产性检查）。
  projCosmos-embed-compat : ∀ (x : Cosmos FinCatN TrivialFCN)
    → projCosmos′ (embedCosmos x) ≈C projCosmos x
  projCosmos-embed-compat x .unfoldFunctor₀-eq {A = k} _ =
    begin
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos′ (embedCosmos x)))) (k , lift tt)
        ≡⟨ PS.projCosmos-F₀-spec (embedCosmos x) k ⟩
      extendFin′ (embedF₀ (λ A₁ → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt))) k
        ≡⟨ extendFin-embedF₀ (λ A₁ → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt)) k ⟩
      extendFin (λ A₁ → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt)) k
        ≡⟨ sym (projCosmos-F₀-spec x k) ⟩
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos x))) (k , lift tt)
    ∎
  projCosmos-embed-compat x .pos-to-shape-eq _ _ = refl
  projCosmos-embed-compat x .unfold-next-eq {A = k} _
    with restrictFin (defaultFin′ k) | restrictFin-defaultFin k
  ... | w | eq rewrite eq =
      projCosmos-embed-compat (UX.unfold-next {A = defaultFin k} (lift tt))
    where
      UX = out x
      module UX = Unfolding UX

  -- Corollary: for cosmos-mapN the compatibility is a direct instance
  -- 推论：对 cosmos-mapN，相容性是直接实例
  projCosmos-mapN-embed
    : ∀ (f : Fin n → Fin n)
    → projCosmos′ (embedCosmos (cosmos-mapN f)) ≈C projCosmos (cosmos-mapN f)
  projCosmos-mapN-embed f = projCosmos-embed-compat (cosmos-mapN f)
