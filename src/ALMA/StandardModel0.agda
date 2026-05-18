{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module ALMA.StandardModel0 where
open import ALMA.Interact public
obsS : ∀ {O C} → Stream (O × C) → ℕ → O
obsS s n = fst (head (stream-tail-n s n))
Attr2D : Set
Attr2D = Fin 2 → ℕ
Attr1D : Set
Attr1D = Fin 1 → ℕ
inh-Attr2D : (Σ Attr2D (λ _ → ⊤))
inh-Attr2D = (λ _ → 0) , tt
inh-Attr1D : (Σ Attr1D (λ _ → ⊤))
inh-Attr1D = (λ _ → 0) , tt
inh-ℕ : (Σ ℕ (λ _ → ⊤))
inh-ℕ = 0 , tt
constStream-tail-n : ∀ {A} (a : A) (n : ℕ)
                   → stream-tail-n (constStream a) n ≡ constStream a
constStream-tail-n a zero = refl
constStream-tail-n a (suc n) = constStream-tail-n a n
constStream-obsS-constant : ∀ {O C} (a : O × C) (n : ℕ)
                          → obsS (constStream a) n ≡ fst a
constStream-obsS-constant a n =
  begin
    obsS (constStream a) n
      ≡⟨ refl ⟩
    fst (head (stream-tail-n (constStream a) n))
      ≡⟨ cong (λ s → fst (head s)) (constStream-tail-n a n) ⟩
    fst (head (constStream a))
      ≡⟨ refl ⟩
    fst a
  ∎
self-o : Attr2D
self-o i = if toℕ i ≡ᵇ 0 then 1 else 42
self-c : ℕ
self-c = 0
self-stream : Stream (Attr2D × ℕ)
self-stream = constStream (self-o , self-c)
self-essence-const : Always (λ x → snd x ≡ self-c) self-stream
self-essence-const = constStream-always-gen (self-o , self-c) refl
self-init-consistent : fst (head self-stream) ≡ self-o
self-init-consistent = refl
selfBeing : Process Attr2D ℕ
selfBeing = mkProc self-o self-c self-stream self-essence-const self-init-consistent
self-being-weak-hom : WeakHom selfBeing
self-being-weak-hom n m =
  begin
    obsS (stream selfBeing) n
      ≡⟨ constStream-obsS-constant (self-o , self-c) n ⟩
    self-o
      ≡⟨ sym (constStream-obsS-constant (self-o , self-c) m) ⟩
    obsS (stream selfBeing) m
  ∎
random-c : ℕ
random-c = 0
random-coalg : ℕ → StreamF (Attr1D × ℕ) ℕ
random-coalg n = ((λ _ → n) , random-c) , suc n
random-stream : Stream (Attr1D × ℕ)
random-stream = ana random-coalg 0
random-essence-const : Always (λ x → snd x ≡ random-c) random-stream
random-essence-const = helper 0
  where
    helper : ∀ n → Always (λ x → snd x ≡ random-c) (ana random-coalg n)
    helper n .Always.head = refl
    helper n .Always.tail = helper (suc n)
random-init-consistent : fst (head random-stream) ≡ (λ _ → 0)
random-init-consistent = refl
randomBeing : Process Attr1D ℕ
randomBeing = mkProc (λ _ → 0) random-c random-stream random-essence-const random-init-consistent
add-suc : ∀ n m → n + suc m ≡ suc (n + m)
add-suc zero m = refl
add-suc (suc n) m = cong suc (add-suc n m)
lemma-random-obs : ∀ k n → 
  fst (head (stream-tail-n (ana random-coalg k) n)) ≡ (λ _ → k + n)
lemma-random-obs k zero =
  begin
    fst (head (stream-tail-n (ana random-coalg k) zero))
      ≡⟨ refl ⟩
    (λ _ → k)
      ≡⟨ cong (λ m → λ _ → m) (sym (+-identityʳ k)) ⟩
    (λ _ → k + zero)
  ∎
lemma-random-obs k (suc n) =
  begin
    fst (head (stream-tail-n (ana random-coalg k) (suc n)))
      ≡⟨ refl ⟩
    fst (head (stream-tail-n (Stream.tail (ana random-coalg k)) n))
      ≡⟨ refl ⟩
    fst (head (stream-tail-n (ana random-coalg (suc k)) n))
      ≡⟨ lemma-random-obs (suc k) n ⟩
    (λ _ → suc k + n)
      ≡⟨ refl ⟩
    (λ _ → suc (k + n))
      ≡⟨ cong (λ m → λ _ → m) (sym (add-suc k n)) ⟩
    (λ _ → k + suc n)
  ∎
observe-random-n : ∀ n → observe randomBeing n ≡ (λ _ → n)
observe-random-n n =
  begin
    observe randomBeing n
      ≡⟨ refl ⟩
    fst (head (stream-tail-n random-stream n))
      ≡⟨ lemma-random-obs 0 n ⟩
    (λ _ → 0 + n)
      ≡⟨ refl ⟩
    (λ _ → n)
  ∎
0≢1 : 0 ≢ 1
0≢1 ()
random-being-changes : Changes randomBeing
random-being-changes = 0 , λ eq →
  0≢1 (cong (λ f → f zero)
    (trans (sym (observe-random-n 0))
           (trans eq (observe-random-n 1))))
random-being-delta : Δ randomBeing
random-being-delta = 0 , 1 , λ eq →
  0≢1 (cong (λ f → f zero)
    (trans (sym (observe-random-n 0))
           (trans eq (observe-random-n 1))))
same-essence : core selfBeing ≡ core randomBeing
same-essence = refl
self-random-interact : Process (Attr2D × Attr1D) ℕ
self-random-interact = interact selfBeing randomBeing
interact-essence-conserved : core self-random-interact ≡ core selfBeing
interact-essence-conserved = core-interact selfBeing randomBeing
