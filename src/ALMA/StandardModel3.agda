{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module ALMA.StandardModel3 where
open import ALMA.StandardModel2 public
env : ℕ → ℕ
env n = observe randomBeing n zero
env≡n : ∀ n → env n ≡ n
env≡n n = cong (λ f → f zero) (observe-random-n n)
v : ℕ → ℕ
v n = if does (n <? 7) then 0 else n
stage : ℕ → ℕ
stage n = if does (n <? 5) then 0
          else (if does (n <? 7) then 1 else 2)
pair→attr : ℕ × ℕ → Attr2D
pair→attr (val , s) i = if toℕ i ≡ᵇ 0 then val else s
transient-coalg : ℕ → StreamF (Attr2D × ℕ) ℕ
transient-coalg n =
  let state = (v n , stage n)
  in ((pair→attr state , 0) , suc n)
transientStream : Stream (Attr2D × ℕ)
transientStream = ana transient-coalg 0
transient-essence-const : Always (λ x → snd x ≡ 0) transientStream
transient-essence-const = helper 0
  where
    helper : ∀ n → Always (λ x → snd x ≡ 0) (ana transient-coalg n)
    helper n .Always.head = refl
    helper n .Always.tail = helper (suc n)
transientBeing : Process Attr2D ℕ
transientBeing = mkProc
  (pair→attr (v 0 , stage 0))
  0
  transientStream
  transient-essence-const
  refl
cInternal5 : ℕ
cInternal5 = countOver (λ k → v k ==ℕ v (suc k)) 4
cInternal5≡4 : cInternal5 ≡ 4
cInternal5≡4 = refl
cExternal5 : ℕ
cExternal5 = countOver (λ k → v k ==ℕ env k) 5
cExternal5≡1 : cExternal5 ≡ 1
cExternal5≡1 = refl
coherence-phase : cInternal5 > cExternal5
coherence-phase =
  subst (λ x → x > cExternal5) cInternal5≡4
  (subst (λ x → 4 > x) cExternal5≡1
  (s≤s (s≤s (z≤n {2}))))
dInternal : ℕ
dInternal = countOver (λ k → v (7 + k) ==ℕ v (7 + suc k)) 2
dInternal≡0 : dInternal ≡ 0
dInternal≡0 = refl
dExternal : ℕ
dExternal = countOver (λ k → v (7 + k) ==ℕ env (7 + k)) 3
dExternal≡3 : dExternal ≡ 3
dExternal≡3 = refl
dissipation-phase : dExternal > dInternal
dissipation-phase =
  subst (λ x → dExternal > x) dInternal≡0
  (subst (λ x → x > 0) dExternal≡3
  (s≤s (z≤n {2})))
∃-coherence : ∃ λ steps → countOver (λ k → v k ==ℕ v (suc k)) (steps ∸ 1) > countOver (λ k → v k ==ℕ env k) steps
∃-coherence = 5 , subst (λ x → x > cExternal5) (sym cInternal5≡4) coherence-phase
∃-dissipation : ∃ λ steps → countOver (λ k → v (7 + k) ==ℕ v (7 + suc k)) (steps ∸ 1) < countOver (λ k → v (7 + k) ==ℕ env (7 + k)) steps
∃-dissipation = 3 , subst (λ x → dInternal < x) (sym dExternal≡3) dissipation-phase
phase-transition-exists : ∃ λ (p : Process Attr2D ℕ) →
  (∃ λ steps → countOver (λ k → v k ==ℕ v (suc k)) (steps ∸ 1) > countOver (λ k → v k ==ℕ env k) steps) ×
  (∃ λ steps → countOver (λ k → v (7 + k) ==ℕ v (7 + suc k)) (steps ∸ 1) < countOver (λ k → v (7 + k) ==ℕ env (7 + k)) steps)
phase-transition-exists = transientBeing , (∃-coherence , ∃-dissipation)
