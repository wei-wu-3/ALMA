------------------------------------------------------------------------
-- Lambek's lemma for the terminal coalgebra Cosmos
-- Cosmos 终余代数的 Lambek 引理
--
-- out : Cosmos → F Cosmos is an isomorphism up to bisimulation.
-- out 在互模拟意义下为同构。
-- Key pivot: commute is ≡, so in-hom.commute gives out ∘ in-F ≡ F(in-F ∘ out).
-- 关键利用 commute 为 ≡：in-hom.commute 给出 out ∘ in-F ≡ F(in-F ∘ out)。
-- Imported cosmosSetoid / cosmosCoalg are explicitly applied to module params
-- to form CS / CC, eliminating implicit-parameter metavariables.
-- 显式应用 Terminal 模块参数生成 CS / CC，消除隐式元变量。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Lambek where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Bundles using (Setoid)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.Unfolding using (Unfolding; module UnfoldingSetoid)
open import ALMA.Cosmos
  using ( Cosmos; CosmosF; out; unfoldingCore
        ; module CosmosMap; module CosmosFFunctor )
open CosmosMap using (mapCosmosF; map-∘)
open import ALMA.Cosmos.Terminal
  using ( Coalgebra; CoalgHom; cosmosCoalg; ana-hom; unique-ana
        ; _≈C_; ≈C-trans; ≈C-sym; cosmosSetoid )

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

    module CFF = CosmosFFunctor
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {u = L} {C = C} {F = FC}

    T  = Cosmos C FC
    FT : Set L
    FT = CosmosF C FC T
    FFT : Set L
    FFT = CosmosF C FC FT

    -- Explicitly apply Terminal's module params: no implicit metavariables.
    -- 显式应用 Terminal 的模块参数：无隐式元变量。
    CS : Setoid L L
    CS = cosmosSetoid {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}

    CC : Coalgebra
    CC = cosmosCoalg {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}

    outF : Func CS (CFF.CosmosFSetoid L CS)
    outF = Coalgebra.α CC

    -- FT-Setoid: FT under _≡_ (Setoid L L). Carrier = FT.
    -- FT-Setoid：_≡_ 下的 FT，载体为 FT。
    FT-Setoid : Setoid L L
    FT-Setoid = record
      { Carrier       = FT
      ; _≈_           = _≡_ {A = FT}
      ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
      }

    ≡→≈F-FT : ∀ {d₁ d₂ : FFT} → d₁ ≡ d₂ → CFF._≈F_ FT-Setoid d₁ d₂
    ≡→≈F-FT refl = CFF.≈F-refl {X = FT-Setoid}

    FT-α : Func FT-Setoid (CFF.CosmosFSetoid L FT-Setoid)
    FT-α = record
      { to   = mapCosmosF out
      ; cong = λ {c₁} {c₂} c₁≡c₂ → ≡→≈F-FT (cong (mapCosmosF out) c₁≡c₂)
      }

  -- coalgebra (F T, F out)
  -- 余代数 (F T, F out)
  FT-Coalg : Coalgebra
  FT-Coalg = record { Carrier = FT-Setoid ; α = FT-α }

  -- in-F : FT-Coalg → CC by final universality
  -- in-F : FT-Coalg → CC（由终泛性质）
  in-hom : CoalgHom FT-Coalg CC
  in-hom = ana-hom FT-Coalg

  in-F : FT → T
  in-F = Func.to (CoalgHom.f in-hom)

  -- in-F preserves ≈F (coinductive, same pattern as ana-cong).
  -- in-F 保持 ≈F（余归纳，与 ana-cong 相同模式）。
  in-F-resp-≈F : ∀ {c₁ c₂} → CFF._≈F_ CS c₁ c₂ → in-F c₁ ≈C in-F c₂
  in-F-resp-≈F {c₁} {c₂} eq = helper eq
    where
      open _≈C_
      helper : ∀ {d₁ d₂} → CFF._≈F_ CS d₁ d₂ → in-F d₁ ≈C in-F d₂
      helper {d₁} {d₂} eq .unfoldFunctor-eq =
        US._≈U_.unfoldFunctor-eq (CFF._≈F_.unfolding-eq eq)
      helper {d₁} {d₂} eq .pos-to-shape-eq =
        US._≈U_.pos-to-shape-eq (CFF._≈F_.unfolding-eq eq)
      helper {d₁} {d₂} eq .unfold-next-eq s =
        helper (Func.cong outF
          (US._≈U_.unfold-next-eq (CFF._≈F_.unfolding-eq eq) s))

  -- in-F ∘ out as a self-homomorphism of (T, out)
  -- in-F ∘ out 作为 (T, out) 的自同态
  private
    in∘out-f : Func CS CS
    in∘out-f = record
      { to   = in-F ∘ out
      ; cong = λ {x} {y} x≈y → in-F-resp-≈F (Func.cong outF x≈y)
      }

    in∘out-hom : CoalgHom CC CC
    in∘out-hom = record { f = in∘out-f ; commute = commute-proof }
      where
        commute-proof : ∀ x → mapCosmosF (in-F ∘ out) (out x) ≡ out (in-F (out x))
        commute-proof x = begin
          mapCosmosF (in-F ∘ out) (out x)
            ≡⟨ map-∘ in-F out (out x) ⟩
          mapCosmosF in-F (mapCosmosF out (out x))
            ≡⟨ CoalgHom.commute in-hom (out x) ⟩
          out (in-F (out x))
          ∎

    idFunc : Func CS CS
    idFunc = record { to = id ; cong = λ x≈y → x≈y }

    id-hom : CoalgHom CC CC
    id-hom = record { f = idFunc ; commute = λ _ → refl }

  -- in-F ∘ out ≈C id_T
  in∘out≈id : ∀ x → in-F (out x) ≈C x
  in∘out≈id x =
    ≈C-trans (unique-ana CC in∘out-hom x)
             (≈C-sym (unique-ana CC id-hom x))

  -- out ∘ in-F ≡ F(in-F ∘ out)
  out∘in≡F∘ : ∀ y → out (in-F y) ≡ mapCosmosF (in-F ∘ out) y
  out∘in≡F∘ y = begin
    out (in-F y)
      ≡⟨ sym (CoalgHom.commute in-hom y) ⟩
    mapCosmosF in-F (mapCosmosF out y)
      ≡⟨ sym (map-∘ in-F out y) ⟩
    mapCosmosF (in-F ∘ out) y
    ∎

  -- F(in-F ∘ out) ≈F id_{F T}
  private
    open Unfolding using (unfold-next)
    F∘≈Fid : ∀ y → CFF._≈F_ CS (mapCosmosF (in-F ∘ out) y) y
    F∘≈Fid y = record
      { contEquiv-eq = refl
      ; unfolding-eq  = record
          { unfoldFunctor-eq = refl
          ; pos-to-shape-eq  = λ _ _ → refl
          ; unfold-next-eq   = λ {A} s →
              in∘out≈id (unfold-next (unfoldingCore y) s)
          }
      }

  -- out ∘ in-F ≈F id_{F T} (transport along ≡ from previous step)
  -- out ∘ in-F ≈F id_{F T}（沿前步等式传输）
  out∘in≈Fid : ∀ y → CFF._≈F_ CS (out (in-F y)) y
  out∘in≈Fid y =
    subst (λ z → CFF._≈F_ CS z y)
          (sym (out∘in≡F∘ y))
          (F∘≈Fid y)

  -- out is an isomorphism up to bisimulation
  --   in-F ∘ out ≈C id_T
  --   out ∘ in-F ≈F id_{F T}
  -- out 在互模拟意义下为同构
  record LambekIso : Set (lsuc L) where
    field
      inverse      : FT → T
      inverse-left : ∀ x → inverse (out x) ≈C x
      inverse-right : ∀ y → CFF._≈F_ CS (out (inverse y)) y

  -- The canonical Lambek isomorphism obtained from the terminal coalgebra.
  -- 由终余代数得到的典范 Lambek 同构。
  lambekIso : LambekIso
  lambekIso = record
    { inverse      = in-F
    ; inverse-left = in∘out≈id
    ; inverse-right = out∘in≈Fid
    }
