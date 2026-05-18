{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module ALMA.StandardModelAll where
open import ALMA.StandardModel3 public
record StandardModel : Set₁ where
  field
    indestructibility : Indestructibility-Theorem
    indestructibility-uniqueness : Indestructibility-Uniqueness
    process-uniqueness       : Process-Uniqueness
    core-conservation        : ∀ {O C} (p : Process O C) → core (next p) ≡ core p
    self        : Process Attr2D ℕ
    random      : Process Attr1D ℕ
    nonunif     : ∃ λ n1 → ∃ λ n2 → observe random n1 ≢ observe random n2
    conscious   : ∃ λ steps → internalCount steps > externalCount steps
    consciousBidir : ∃ λ steps → bidirInternalCount steps > bidirExternalCount steps
    coherencePhase   : Σ ℕ (λ steps → cInternal5 > cExternal5)
    dissipationPhase : Σ ℕ (λ steps → dExternal > dInternal)
standardModel : StandardModel
standardModel = record
  { indestructibility = indestructibility-proof
  ; indestructibility-uniqueness = indestructibility-uniqueness-proof
  ; process-uniqueness       = process-uniqueness-proof
  ; core-conservation        = c-conservation
  ; self            = selfBeing
  ; random          = randomBeing
  ; nonunif         = 0 , 1 , λ p → contradiction (cong (λ f → f zero) p) (λ ())
  ; conscious       = consciousnessEmergence
  ; consciousBidir  = bidirConsciousnessEmergence
  ; coherencePhase  = 5 , coherence-phase
  ; dissipationPhase = 3 , dissipation-phase
  }
