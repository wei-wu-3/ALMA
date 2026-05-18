{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
{-
模块：交互、耦合与共同本质
哲学意义：动态关联性——本质持存，观察呈现对偶结构
-}
module ALMA.Interact where
open import ALMA.Inhomogeneity public
fst : ∀ {A B : Set} → A × B → A
fst (a , b) = a
snd : ∀ {A B : Set} → A × B → B
snd (a , b) = b
pair-eq : ∀ {A B : Set} {a1 a2 : A} {b1 b2 : B} → a1 ≡ a2 → b1 ≡ b2 → (a1 , b1) ≡ (a2 , b2)
pair-eq refl refl = refl
map-stream : ∀ {A B : Set} → (A → B) → Stream A → Stream B
map-stream f s .head = f (head s)
map-stream f s .tail = map-stream f (tail s)
map-stream-tail-n : ∀ {A B : Set} (f : A → B) (s : Stream A) (n : ℕ)
                  → head (stream-tail-n (map-stream f s) n) ≡ f (head (stream-tail-n s n))
map-stream-tail-n f s zero = refl
map-stream-tail-n f s (suc n) = map-stream-tail-n f (tail s) n
merge-stream-observe : ∀ {O₁ C₁ O₂ C₂ : Set} (s1 : Stream (O₁ × C₁)) (s2 : Stream (O₂ × C₂)) (n : ℕ)
                     → fst (head (stream-tail-n (merge-stream s1 s2) n)) 
                     ≡ (fst (head (stream-tail-n s1 n)), fst (head (stream-tail-n s2 n)))
merge-stream-observe s1 s2 zero = refl
merge-stream-observe s1 s2 (suc n) = merge-stream-observe (tail s1) (tail s2) n
-- 本体论交互：过程组合并保持同一本质
module Ontological where
  transform : ∀ {O₁ O₂ C : Set} → ((O₁ × O₂) × (C × C)) → ((O₁ × O₂) × C)
  transform ((o12 , (c1 , c2))) = (o12 , c1)
  interact : ∀ {O₁ O₂ C : Set}
    → Process O₁ C
    → Process O₂ C
    → Process (O₁ × O₂) C
  interact {O₁} {O₂} {C} p1 p2 =
    mkProc
      (o p1 , o p2)
      (core p1)
      (map-stream transform (merge-stream (stream p1) (stream p2)))
      transformed-essence-const
      transformed-init-consistent
    where
      transformed-essence-const : Always (λ x → snd x ≡ core p1) 
                                       (map-stream transform (merge-stream (stream p1) (stream p2)))
      transformed-essence-const = helper (stream p1) (stream p2) (essence-const p1)
        where
          helper : ∀ (s1 : Stream (O₁ × C)) (s2 : Stream (O₂ × C))
                 → Always (λ x → snd x ≡ core p1) s1
                 → Always (λ x → snd x ≡ core p1) (map-stream transform (merge-stream s1 s2))
          helper s1 s2 alw1 .Always.head =
            begin
              snd (transform (head (merge-stream s1 s2)))
                ≡⟨ refl ⟩
              snd (head s1)
                ≡⟨ Always.head alw1 ⟩
              core p1
            ∎
          helper s1 s2 alw1 .Always.tail =
            helper (tail s1) (tail s2) (Always.tail alw1)
      transformed-init-consistent : fst (head (map-stream transform (merge-stream (stream p1) (stream p2)))) 
                                    ≡ (o p1 , o p2)
      transformed-init-consistent =
        begin
          fst (transform (head (merge-stream (stream p1) (stream p2))))
            ≡⟨ refl ⟩
          (fst (head (stream p1)) , fst (head (stream p2)))
            ≡⟨ pair-eq (init-consistent p1) (init-consistent p2) ⟩
          (o p1 , o p2)
        ∎
  core-interact : ∀ {O₁ O₂ C : Set}
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → core (interact p1 p2) ≡ core p1
  core-interact p1 p2 = refl
  core-interact-sym : ∀ {O₁ O₂ C : Set}
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → core p1 ≡ core p2
    → core (interact p1 p2) ≡ core p2
  core-interact-sym p1 p2 eq = trans (core-interact p1 p2) eq
  observe-interact : ∀ {O₁ O₂ C : Set}
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → ∀ n → observe (interact p1 p2) n ≡ (observe p1 n , observe p2 n)
  observe-interact p1 p2 n =
    begin
      observe (interact p1 p2) n
        ≡⟨ refl ⟩
      fst (head (stream-tail-n (map-stream transform (merge-stream (stream p1) (stream p2))) n))
        ≡⟨ cong fst (map-stream-tail-n transform (merge-stream (stream p1) (stream p2)) n) ⟩
      fst (transform (head (stream-tail-n (merge-stream (stream p1) (stream p2)) n)))
        ≡⟨ refl ⟩
      fst (head (stream-tail-n (merge-stream (stream p1) (stream p2)) n))
        ≡⟨ merge-stream-observe (stream p1) (stream p2) n ⟩
      (fst (head (stream-tail-n (stream p1) n)), fst (head (stream-tail-n (stream p2) n)))
        ≡⟨ refl ⟩
      (observe p1 n , observe p2 n)
    ∎
-- 认识论耦合：交互的抽象规格，本质守恒与对偶观察
module Epistemic where
  open Ontological public
  Coupling : {O₁ O₂ C : Set} → Set
  Coupling {O₁} {O₂} {C} =
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → Σ (Process (O₁ × O₂) C)
        (λ p' → (core p' ≡ core p1)
              × (∀ n → observe p' n ≡ (observe p1 n , observe p2 n)))
  canonical-coupling : {O₁ O₂ C : Set} → Coupling {O₁} {O₂} {C}
  canonical-coupling p1 p2 =
    interact p1 p2 , core-interact p1 p2 , observe-interact p1 p2
  interact-with : {O₁ O₂ C : Set}
                → Coupling {O₁} {O₂} {C}
                → Process O₁ C
                → Process O₂ C
                → Process (O₁ × O₂) C
  interact-with coupling p1 p2 = proj₁ (coupling p1 p2)
  core-interact-epistemic : {O₁ O₂ C : Set}
                           → (coupling : Coupling {O₁} {O₂} {C})
                           → (p1 : Process O₁ C)
                           → (p2 : Process O₂ C)
                           → core (interact-with coupling p1 p2) ≡ core p1
  core-interact-epistemic coupling p1 p2 = proj₁ (proj₂ (coupling p1 p2))
  observe-interact-epistemic : {O₁ O₂ C : Set}
                               → (coupling : Coupling {O₁} {O₂} {C})
                               → (p1 : Process O₁ C)
                               → (p2 : Process O₂ C)
                               → ∀ n → observe (interact-with coupling p1 p2) n
                                      ≡ (observe p1 n , observe p2 n)
  observe-interact-epistemic coupling p1 p2 n = proj₂ (proj₂ (coupling p1 p2)) n
open Ontological public
open Epistemic public
-- interact 组合子的引理
interact-functor₁ : ∀ {O₁ O₂ C} {p₁ p₁' : Process O₁ C} {p₂ : Process O₂ C} →
                    p₁ ≈ₚ p₁' → interact p₁ p₂ ≈ₚ interact p₁' p₂
interact-functor₁ {p₁ = p₁} {p₁'} {p₂} p₁≈p₁' = helper (stream p₁) (stream p₁') (stream p₂) p₁≈p₁'
  where
    helper : ∀ {O₁ O₂ C} (s₁ s₁' : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             s₁ ≈ s₁' → map-stream transform (merge-stream s₁ s₂) ≈ map-stream transform (merge-stream s₁' s₂)
    helper s₁ s₁' s₂ eq ._≈_.head≈ = cong transform (cong (λ x → merge-state x (Stream.head s₂)) (_≈_.head≈ eq))
    helper s₁ s₁' s₂ eq ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₁') (Stream.tail s₂) (_≈_.tail≈ eq)
interact-functor₂ : ∀ {O₁ O₂ C} {p₁ : Process O₁ C} {p₂ p₂' : Process O₂ C} →
                    p₂ ≈ₚ p₂' → interact p₁ p₂ ≈ₚ interact p₁ p₂'
interact-functor₂ {p₁ = p₁} {p₂} {p₂'} p₂≈p₂' = helper (stream p₁) (stream p₂) (stream p₂') p₂≈p₂'
  where
    helper : ∀ {O₁ O₂ C} (s₁ : Stream (O₁ × C)) (s₂ s₂' : Stream (O₂ × C)) →
             s₂ ≈ s₂' → map-stream transform (merge-stream s₁ s₂) ≈ map-stream transform (merge-stream s₁ s₂')
    helper s₁ s₂ s₂' eq ._≈_.head≈ = cong transform (cong (merge-state (Stream.head s₁)) (_≈_.head≈ eq))
    helper s₁ s₂ s₂' eq ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₂') (_≈_.tail≈ eq)
interact-functor : ∀ {O₁ O₂ C} {p₁ p₁' : Process O₁ C} {p₂ p₂' : Process O₂ C} →
                   p₁ ≈ₚ p₁' → p₂ ≈ₚ p₂' → interact p₁ p₂ ≈ₚ interact p₁' p₂'
interact-functor {O₁} {O₂} {C} {p₁} {p₁'} {p₂} {p₂'} eq1 eq2 =
  helper {O₁} {O₂} {C} (stream p₁) (stream p₁') (stream p₂) (stream p₂') eq1 eq2
  where
    helper : ∀ {O₁ O₂ C} (s₁ s₁' : Stream (O₁ × C)) (s₂ s₂' : Stream (O₂ × C)) →
             s₁ ≈ s₁' → s₂ ≈ s₂' →
             map-stream transform (merge-stream s₁ s₂) ≈ map-stream transform (merge-stream s₁' s₂')
    helper s₁ s₁' s₂ s₂' eq1 eq2 ._≈_.head≈ =
      cong transform (cong₂ merge-state (_≈_.head≈ eq1) (_≈_.head≈ eq2))
    helper s₁ s₁' s₂ s₂' eq1 eq2 ._≈_.tail≈ =
      helper (Stream.tail s₁) (Stream.tail s₁') (Stream.tail s₂) (Stream.tail s₂')
             (_≈_.tail≈ eq1) (_≈_.tail≈ eq2)
interact-core-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                     core (interact p₁ p₂) ≡ core p₁
interact-core-comm = core-interact
interact-next-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                     next (interact p₁ p₂) ≈ₚ interact (next p₁) (next p₂)
interact-next-comm p₁ p₂ = helper (stream p₁) (stream p₂)
  where
    helper : ∀ {O₁ O₂ C} (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             Stream.tail (map-stream transform (merge-stream s₁ s₂)) ≈
             map-stream transform (merge-stream (Stream.tail s₁) (Stream.tail s₂))
    helper s₁ s₂ ._≈_.head≈ = refl
    helper s₁ s₂ ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₂)
interact-observe-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) (n : ℕ) →
                        observe (interact p₁ p₂) n ≡ (observe p₁ n , observe p₂ n)
interact-observe-comm = observe-interact
-- interact 的代数引理
assoc-interact-O : ∀ {O₁ O₂ O₃ : Set} → ((O₁ × O₂) × O₃) → (O₁ × (O₂ × O₃))
assoc-interact-O ((o₁ , o₂) , o₃) = (o₁ , (o₂ , o₃))
interact-assoc : ∀ {O₁ O₂ O₃ C}
                 (p₁ : Process O₁ C) (p₂ : Process O₂ C) (p₃ : Process O₃ C) →
                 ≈ₚ-hetero (interact (interact p₁ p₂) p₃)
                           (interact p₁ (interact p₂ p₃))
                           assoc-interact-O id
interact-assoc p₁ p₂ p₃ = record { stream≈ = helper (stream p₁) (stream p₂) (stream p₃) }
  where
    helper : ∀ {O₁ O₂ O₃ C} (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) (s₃ : Stream (O₃ × C)) →
             ≈-hetero (map-stream transform (merge-stream (map-stream transform (merge-stream s₁ s₂)) s₃))
                      (map-stream transform (merge-stream s₁ (map-stream transform (merge-stream s₂ s₃))))
                      (comb assoc-interact-O id)
    helper s₁ s₂ s₃ .head≈ = refl
    helper s₁ s₂ s₃ .tail≈ = helper (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₃)
interact-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                core p₁ ≡ core p₂ →
                ≈ₚ-hetero (interact p₁ p₂) (interact p₂ p₁) swap-O id
interact-comm {O₁} {O₂} {C} p₁ p₂ eq =
  record { stream≈ = helper (stream p₁) (stream p₂) (essence-const p₁) (essence-const p₂) }
  where
    helper : (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             Always (λ x → proj₂ x ≡ core p₁) s₁ →
             Always (λ x → proj₂ x ≡ core p₂) s₂ →
             ≈-hetero (map-stream transform (merge-stream s₁ s₂))
                      (map-stream transform (merge-stream s₂ s₁))
                      (comb swap-O id)
    helper s₁ s₂ alw₁ alw₂ .head≈ =
      let c1≡c2 = trans (alw₁ .Always.head) (trans eq (sym (alw₂ .Always.head)))
      in cong₂ _,_ refl c1≡c2
    helper s₁ s₂ alw₁ alw₂ .tail≈ =
      helper (Stream.tail s₁) (Stream.tail s₂) (Always.tail alw₁) (Always.tail alw₂)
interact-from-⊗ : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                  ≈ₚ-hetero (p₁ ⊗ p₂) (interact p₁ p₂) id proj₁
interact-from-⊗ p₁ p₂ = record { stream≈ = helper (stream p₁) (stream p₂) }
  where
    helper : ∀ {O₁ O₂ C} (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             ≈-hetero (merge-stream s₁ s₂)
                      (map-stream transform (merge-stream s₁ s₂))
                      (comb id proj₁)
    helper s₁ s₂ .head≈ = refl
    helper s₁ s₂ .tail≈ = helper (Stream.tail s₁) (Stream.tail s₂)
