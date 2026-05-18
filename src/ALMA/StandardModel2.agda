{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module ALMA.StandardModel2 where
open import ALMA.StandardModel1 public
countOver : (ℕ → Bool) → ℕ → ℕ
countOver P zero    = 0
countOver P (suc n) = (if P n then 1 else 0) + countOver P n
pairAt : ℕ → Attr2D × Attr1D
pairAt n = proj₁ (head (stream-tail-n feedbackStream n))
selfAt : ℕ → Attr2D
selfAt n = proj₁ (pairAt n)
randAt : ℕ → Attr1D
randAt n = proj₂ (pairAt n)
randRandom : ℕ → ℕ
randRandom k = observe randomBeing k zero
internalCount : ℕ → ℕ
internalCount steps = countOver (λ k → does (selfAt k zero ≟ selfAt (suc k) zero)) (steps ∸ 1)
externalCount : ℕ → ℕ
externalCount steps = countOver (λ k → does (selfAt k zero ≟ randRandom k)) steps
internal5 : ℕ
internal5 = internalCount 5
internal5≡4 : internal5 ≡ 4
internal5≡4 = refl
external5 : ℕ
external5 = externalCount 5
external5≡1 : external5 ≡ 1
external5≡1 = refl
coherenceProof : internal5 > external5
coherenceProof =
  subst (λ x → x > external5) internal5≡4
  (subst (λ x → 4 > x) external5≡1
  (s≤s (s≤s (z≤n {2}))))
consciousnessEmergence : ∃ λ steps → internalCount steps > externalCount steps
consciousnessEmergence = 5 , coherenceProof
bidirInternalCount : ℕ → ℕ
bidirInternalCount steps = countOver (λ k → does (bidirSelfAt k zero ≟ bidirSelfAt (suc k) zero)) (steps ∸ 1)
bidirExternalCount : ℕ → ℕ
bidirExternalCount steps = countOver (λ k → does (bidirSelfAt k zero ≟ bidirRandAt k zero)) steps
bidirInternal5 : ℕ
bidirInternal5 = bidirInternalCount 5
bidirInternal5≡4 : bidirInternal5 ≡ 4
bidirInternal5≡4 = refl
bidirExternal5 : ℕ
bidirExternal5 = bidirExternalCount 5
bidirExternal5≡0 : bidirExternal5 ≡ 0
bidirExternal5≡0 = refl
bidirCoherenceProof : bidirInternal5 > bidirExternal5
bidirCoherenceProof =
  subst (λ x → x > bidirExternal5) bidirInternal5≡4
  (subst (λ x → 4 > x) bidirExternal5≡0
  (s≤s (z≤n {3})))
bidirConsciousnessEmergence : ∃ λ steps → bidirInternalCount steps > bidirExternalCount steps
bidirConsciousnessEmergence = 5 , bidirCoherenceProof
ConsciousnessTheorem : (Process (Attr2D × Attr1D) ℕ → (ℕ → ℕ)) → Process (Attr2D × Attr1D) ℕ → Set
ConsciousnessTheorem external-source p =
  ∃ λ steps →
    let
      pairAt' n = proj₁ (head (stream-tail-n (stream p) n))
      selfAt' n = proj₁ (pairAt' n)
      internal = countOver (λ k → does (selfAt' k zero ≟ selfAt' (suc k) zero)) (steps ∸ 1)
      external = countOver (λ k → does (selfAt' k zero ≟ external-source p k)) steps
    in internal > external
feedback-external-source : Process (Attr2D × Attr1D) ℕ → (ℕ → ℕ)
feedback-external-source _ k = randRandom k
bidirectional-external-source : Process (Attr2D × Attr1D) ℕ → (ℕ → ℕ)
bidirectional-external-source _ k = bidirRandAt k zero
Theorem-holds-for-feedback : ConsciousnessTheorem feedback-external-source feedbackProcess
Theorem-holds-for-feedback = consciousnessEmergence
Theorem-holds-for-bidirectional : ConsciousnessTheorem bidirectional-external-source bidirectionalProcess
Theorem-holds-for-bidirectional = bidirConsciousnessEmergence
