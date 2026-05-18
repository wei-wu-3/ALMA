{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module ALMA.StandardModel1 where
open import ALMA.StandardModel0 public
_==ℕ_ : ℕ → ℕ → Bool
m ==ℕ n = does (_≟_ m n)
stableSelf : Attr2D
stableSelf i = if toℕ i ≡ᵇ 0 then 1 else 42
initSelf : Attr2D
initSelf = stableSelf
initRandom : Attr1D
initRandom = λ _ → 0
nextSelf : Attr2D → Attr2D × Attr1D → Attr2D
nextSelf self _ = self
nextRandom : Attr1D → Attr2D × Attr1D → Attr1D
nextRandom env _ = λ _ → suc (env zero)
feedback-coalg : (Attr2D × Attr1D) → StreamF ((Attr2D × Attr1D) × ℕ) (Attr2D × Attr1D)
feedback-coalg (s , r) =
  let s' = nextSelf s (s , r)
      r' = nextRandom r (s , r)
  in (((s , r) , 0) , (s' , r'))
feedbackStream : Stream ((Attr2D × Attr1D) × ℕ)
feedbackStream = ana feedback-coalg (initSelf , initRandom)
feedback-essence-const : Always (λ x → proj₂ x ≡ 0) feedbackStream
feedback-essence-const = helper (initSelf , initRandom)
  where
    helper : ∀ state → Always (λ x → proj₂ x ≡ 0) (ana feedback-coalg state)
    helper state .Always.head = refl
    helper state .Always.tail = helper (proj₂ (feedback-coalg state))
feedbackProcess : Process (Attr2D × Attr1D) ℕ
feedbackProcess = mkProc
  (initSelf , initRandom)
  0
  feedbackStream
  feedback-essence-const
  refl
nextRandom' : Attr1D → Attr2D × Attr1D → Attr1D
nextRandom' _ (self , _) = λ _ → suc (self zero)
nextSelf-bidir : Attr2D → Attr2D × Attr1D → Attr2D
nextSelf-bidir self _ = self
bidirectional-coalg : (Attr2D × Attr1D) → StreamF ((Attr2D × Attr1D) × ℕ) (Attr2D × Attr1D)
bidirectional-coalg (s , r) =
  let s' = nextSelf-bidir s (s , r)
      r' = nextRandom' r (s , r)
  in (((s , r) , 0) , (s' , r'))
bidirectionalStream : Stream ((Attr2D × Attr1D) × ℕ)
bidirectionalStream = ana bidirectional-coalg (initSelf , initRandom)
bidirectional-essence-const : Always (λ x → proj₂ x ≡ 0) bidirectionalStream
bidirectional-essence-const = helper (initSelf , initRandom)
  where
    helper : ∀ state → Always (λ x → proj₂ x ≡ 0) (ana bidirectional-coalg state)
    helper state .Always.head = refl
    helper state .Always.tail = helper (proj₂ (bidirectional-coalg state))
bidirectionalProcess : Process (Attr2D × Attr1D) ℕ
bidirectionalProcess = mkProc
  (initSelf , initRandom)
  0
  bidirectionalStream
  bidirectional-essence-const
  refl
bidirPairAt : ℕ → Attr2D × Attr1D
bidirPairAt n = proj₁ (head (stream-tail-n bidirectionalStream n))
bidirSelfAt : ℕ → Attr2D
bidirSelfAt n = proj₁ (bidirPairAt n)
bidirRandAt : ℕ → Attr1D
bidirRandAt n = proj₂ (bidirPairAt n)
bidirSelfAt-const : ∀ n → bidirSelfAt n ≡ initSelf
bidirSelfAt-const n = helper (initSelf , initRandom) n
  where
    helper : ∀ state n → proj₁ (proj₁ (head (stream-tail-n (ana bidirectional-coalg state) n))) ≡ proj₁ state
    helper state zero = refl
    helper state (suc n) =
      let next-state = proj₂ (bidirectional-coalg state)
          next-state-preserves-self : proj₁ next-state ≡ proj₁ state
          next-state-preserves-self = refl
      in trans (helper next-state n) next-state-preserves-self
bidirRandAt-follows-self : ∀ n → bidirRandAt (suc n) zero ≡ suc (initSelf zero)
bidirRandAt-follows-self n = helper (initSelf , initRandom) n
  where
    helper : ∀ state n → proj₂ (proj₁ (head (stream-tail-n (ana bidirectional-coalg state) (suc n)))) zero ≡ suc (proj₁ state zero)
    helper state zero = refl
    helper state (suc n) =
      let next-state = proj₂ (bidirectional-coalg state)
          next-state-preserves-self : proj₁ next-state ≡ proj₁ state
          next-state-preserves-self = refl
      in trans (helper next-state n) (cong (λ x → suc (x zero)) next-state-preserves-self)
feedbackRandAt-strictly-increasing : ∀ n → proj₂ (proj₁ (head (stream-tail-n feedbackStream (suc n)))) zero ≡ suc (proj₂ (proj₁ (head (stream-tail-n feedbackStream n))) zero)
feedbackRandAt-strictly-increasing n = helper (initSelf , initRandom) n
  where
    helper : ∀ state n → proj₂ (proj₁ (head (stream-tail-n (ana feedback-coalg state) (suc n)))) zero ≡ suc (proj₂ (proj₁ (head (stream-tail-n (ana feedback-coalg state) n))) zero)
    helper state zero = refl
    helper state (suc n) = helper (proj₂ (feedback-coalg state)) n
