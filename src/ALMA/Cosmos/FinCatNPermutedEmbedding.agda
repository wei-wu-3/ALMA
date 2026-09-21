------------------------------------------------------------------------
-- Permuted embedding: refuting the extended criterion C
-- 置换嵌入：反驳扩展后的判据 C
--
-- For every f : Fin n → Fin n with a left inverse f⁻¹, constructs a
-- tower-specific embedding whose layer-k F₀ maps z to
-- liftF k f (x.F₀ (proj₁ z)), and a liftAt at layer k applying
-- invPow k f f⁻¹ to cancel the accumulated f. These are packaged as
-- PermutedPathWitness, which captures the liftAt portion of a
-- LiftedLimitStructure (without the mediate fields)
-- When f has a non-fixed point, the embedding does not preserve F₀ at
-- layer 0, while liftAt 0 is the identity and hence injective. This
-- refutes the extended criterion C: feasibility does not imply
-- preservation of input F₀
-- The witness is unconditional: swap01 (defined via splitAt/join to
-- avoid UnsupportedIndexedMatch) supplies a concrete non-trivial
-- permutation on Fin n, using fsuc-fzero≠fzero from FinCatNWitness
-- The parameter m encodes n = suc (suc m), so n ≥ 2 holds definitionally
-- 对每个带左逆 f⁻¹ 的 f : Fin n → Fin n，构造塔特定的嵌入，其第 k 层
-- F₀ 将 z 映为 liftF k f (x.F₀ (proj₁ z))，以及第 k 层 liftAt 施加
-- invPow k f f⁻¹ 以抵消累积的 f。二者打包为 PermutedPathWitness，
-- 它捕捉 LiftedLimitStructure 的 liftAt 部分（不含 mediate 系列）
-- 当 f 有非不动点时，该嵌入在层 0 不保持 F₀，而 liftAt 0 为恒等，
-- 故单射。这反驳了扩展后的判据 C：可行性不蕴含输入 F₀ 的保持
-- 见证是无条件的：swap01（经 splitAt/join 定义以避免
-- UnsupportedIndexedMatch）给出 Fin n 上的具体非平凡置换，
-- 用 FinCatNWitness 的 fsuc-fzero≠fzero。
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCatNPermutedEmbedding where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (cong; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂; Σ; _,_)
open import Data.Fin.Base using (Fin; splitAt; join; opposite) renaming (zero to fzero)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Fin.Properties using (join-splitAt; splitAt-join; opposite-involutive)
open import Data.Unit.Polymorphic.Base using (tt)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.Unfolding using (Unfolding)
open import ALMA.Cosmos using (Cosmos; out)
open import ALMA.Cosmos.Terminal using (_≈C_)
open import ALMA.Cosmos.CumulativeHierarchy using (EmbeddingData; UniformEmbeddingFamily)
open import ALMA.Cosmos.StrictLift using (StrictLayer)
open import ALMA.Cosmos.CumulativeHierarchyLimit using (Tower)
open import ALMA.Cosmos.FinCatNWitness
open import ALMA.Cosmos.FinCatNTowerLemmas
open import ALMA.Cosmos.FinCatNDefaultUnif

module FinCatNPermutedEmbedding (m : ℕ) where

  open FinCatN m
  open FinCatNTowerLemmas m
  open FinCatNDefaultUnif m using (default-unif)

  -- invPow k f f⁻¹ applies f⁻¹ k times; the defining property is
  -- invPow (suc k) f f⁻¹ (f a) ≡ invPow k f f⁻¹ a whenever f⁻¹ (f a) ≡ a
  -- invPow k f f⁻¹ 将 f⁻¹ 施加 k 次；其定义性质为
  -- 当 f⁻¹ (f a) ≡ a 时，invPow (suc k) f f⁻¹ (f a) ≡ invPow k f f⁻¹ a
  invPow : (k : ℕ) (f f⁻¹ : Fin n → Fin n) → Fin n → Fin n
  invPow zero    f f⁻¹ a = a
  invPow (suc k) f f⁻¹ a = invPow k f f⁻¹ (f⁻¹ a)

  -- Shape types at every layer are constant in the object
  -- 每层的形状类型关于对象是常值
  ShapeOf-const : ∀ k (X Y : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
                → ShapeOf (StrictLayer.FC (Tower.layer nTower k)) X
                ≡ ShapeOf (StrictLayer.FC (Tower.layer nTower k)) Y
  ShapeOf-const zero    X Y = refl
  ShapeOf-const (suc k) (X , _) (Y , _) =
    cong (λ T → Lift _ T) (ShapeOf-const k X Y)

  -- Canonical shape at every tower layer, independent of the input object
  -- 每层塔上的典范形状，与输入对象无关
  canonicalShape : ∀ k (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
                → ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A
  canonicalShape zero    A       = lift tt
  canonicalShape (suc k) (A , _) = lift (canonicalShape k A)

  -- liftF k f acts on the outermost Fin n component and resets the shape
  -- component to canonicalShape, which is the unique choice at every layer
  -- liftF k f 作用在最外层 Fin n 分量，并将形状分量重置为 canonicalShape，
  -- 后者在每一层是唯一选择
  liftF : ∀ k → (f : Fin n → Fin n)
        → Category.Obj (StrictLayer.C (Tower.layer nTower k))
        → Category.Obj (StrictLayer.C (Tower.layer nTower k))
  liftF zero    f A       = f A
  liftF (suc k) f (A , _) = (liftF k f A , canonicalShape k (liftF k f A))

  -- F₁ for liftF: identity, because FinCatN hom-sets are ⊤
  -- liftF 的 F₁：恒等，因 FinCatN 的 hom 集为 ⊤
  liftF-F₁ : ∀ k f {A B}
            (g : Category._⇒_ (StrictLayer.C (Tower.layer nTower k)) A B)
          → Category._⇒_ (StrictLayer.C (Tower.layer nTower k))
                      (liftF k f A) (liftF k f B)
  liftF-F₁ zero    f g       = g
  liftF-F₁ (suc k) f (g , _) =
    ( liftF-F₁ k f g
    , shape-singleton-at k _ _ _ )

  -- proj-obj k commutes with liftF: it reads the outer Fin n component
  -- after liftF acts on it
  -- proj-obj k 与 liftF 交换：它读取 liftF 作用后的外层 Fin n 分量
  proj-obj-liftF
    : ∀ k (f : Fin n → Fin n)
      (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    → proj-obj k (liftF k f A) ≡ f (proj-obj k A)
  proj-obj-liftF zero    f A       = refl
  proj-obj-liftF (suc k) f (A , s) = proj-obj-liftF k f A

  -- permuted-F₀: the first component is liftF k f applied to x.F₀ (proj₁ z);
  -- the second component is the canonical shape
  -- permuted-F₀：第一分量为 liftF k f 作用于 x.F₀ (proj₁ z)，
  -- 第二分量为典范形状
  permuted-F₀
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
    → Category.Obj (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Category.Obj (StrictLayer.C (Tower.layer nTower (suc k)))
  permuted-F₀ k f x z =
    ( liftF k f (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))
    , canonicalShape k
        (liftF k f (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))) )

  -- permuted-F₁: the first component is liftF-F₁ applied to x.F₁ (proj₁ fmap);
  -- the second component is the shape-level equation, discharged by
  -- shape-singleton-at
  -- permuted-F₁：第一分量为 liftF-F₁ 作用于 x.F₁ (proj₁ fmap)，
  -- 第二分量为形状层等式，由 shape-singleton-at 消解
  permuted-F₁
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
    → {u v : Category.Obj (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))}
    → Category._⇒_ (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k)))) u v
    → Category._⇒_ (StrictLayer.C (Tower.layer nTower (suc k)))
        (permuted-F₀ k f x u) (permuted-F₀ k f x v)
  permuted-F₁ k f x {u} {v} fmap =
    ( liftF-F₁ k f (Unfolding.unfoldFunctor (out x) .Functor.F₁ (proj₁ fmap))
    , shape-singleton-at k _ _ _ )

  -- permuted-embed: same shape as dep-embed with permuted F₀ and F₁
  -- Functor laws are discharged by nTower-collapsible; pos-to-shape reads
  -- canonicalShape; pos-actS-compat is discharged by shape-singleton-at
  -- permuted-embed：与 dep-embed 结构相同，但 F₀ 与 F₁ 被置换
  -- 函子律由 nTower-collapsible 消解；pos-to-shape 读取 canonicalShape；
  -- pos-actS-compat 由 shape-singleton-at 消解
  permuted-embed
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
    → EmbeddingData x
    → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
             (StrictLayer.FC (Tower.layer nTower (suc k)))
  permuted-embed k f x ed .out =
    let
      C'  = StrictLayer.C (Tower.layer nTower (suc k))
      FC' = StrictLayer.FC (Tower.layer nTower (suc k))
      SC' = ShapeCat C' FC'
      id-SC' = Category.id SC'
      id-C'  = Category.id C'
      pf₁ = permuted-F₁ k f x
    in record
    { unfoldFunctor = record
        { F₀           = permuted-F₀ k f x
        ; F₁           = pf₁
        ; identity = λ {X} →
            nTower-collapsible (suc k)
              (permuted-F₁ k f x (Category.id SC' {A = X}))
              (Category.id C' {A = permuted-F₀ k f x X})
        ; homomorphism = λ {X Y Z f₁ g₁} →
            nTower-collapsible (suc k)
              (pf₁ (Category._∘_ SC' g₁ f₁))
              (Category._∘_ C' (pf₁ g₁) (pf₁ f₁))
        ; F-resp-≈     = λ {X Y f₁ g₁} _ →
            nTower-collapsible (suc k) (pf₁ f₁) (pf₁ g₁)
        }
    ; unfold-next = λ { {A} s →
        permuted-embed k f
          (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
          (EmbeddingData.next ed {A = proj₁ A} (proj₂ A)) }
    ; pos-to-shape = λ { {A} s _ →
        canonicalShape (suc k) (permuted-F₀ k f x (A , s)) }
    ; pos-actS-compat = λ { {A} {B} {s} {t} g eq p →
        shape-singleton-at (suc k)
          (permuted-F₀ k f x (B , t)) _ _ }
    }

  -- permuted-liftAt 0 = id; permuted-liftAt (suc k) x .F₀(A,s) reads the
  -- outermost Fin n component of x.F₀ at the canonical embed-pair and
  -- applies invPow (suc k) f f⁻¹
  -- permuted-liftAt 0 = id；在第 suc k 层，读取 x.F₀ 在典范 embed-pair 处
  -- 的最外层 Fin n 分量并施加 invPow (suc k) f f⁻¹
  permuted-liftAt
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → ∀ k
    → Cosmos (StrictLayer.C (Tower.layer nTower k))
             (StrictLayer.FC (Tower.layer nTower k))
    → Cosmos FinCatN TrivialFCN
  permuted-liftAt f f⁻¹ f⁻¹∘f zero    x = x
  permuted-liftAt f f⁻¹ f⁻¹∘f (suc k) x .out = record
    { unfoldFunctor = record
        { F₀ = λ { (A , _) →
            invPow (suc k) f f⁻¹
              (proj-obj (suc k)
                (Unfolding.unfoldFunctor (out x) .Functor.F₀
                  (embed-obj (suc k) A ,
                   embed-shape (suc k) (embed-obj (suc k) A)))) }
        ; F₁ = λ _ → tt
        ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ _ → refl
        }
    ; unfold-next = λ { {A = A} _ →
        permuted-liftAt f f⁻¹ f⁻¹∘f (suc k)
          (Unfolding.unfold-next (out x)
            {A = embed-obj (suc k) A}
            (embed-shape (suc k) (embed-obj (suc k) A))) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- proj-obj (suc k) ∘ permuted-F₀ k f x = f ∘ proj-obj k ∘ x.F₀ ∘ proj₁
  -- proj-obj (suc k) ∘ permuted-F₀ k f x = f ∘ proj-obj k ∘ x.F₀ ∘ proj₁
  proj-obj-permuted-F₀
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
      (z : Category.Obj (ShapeCat
              (StrictLayer.C (Tower.layer nTower (suc k)))
              (StrictLayer.FC (Tower.layer nTower (suc k)))))
    → proj-obj (suc k) (permuted-F₀ k f x z)
      ≡ f (proj-obj k (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))
  proj-obj-permuted-F₀ k f x z =
    proj-obj-liftF k f
      (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))

  -- permuted-liftAt-step: the F₀ component cancels via
  --   invPow (suc k) (proj-obj (suc k) ((permuted-embed x).F₀ (embed-pair k A)))
  --   = invPow (suc k) (f (proj-obj k (x.F₀ (embed-pair k A))))   [proj-obj-liftF]
  --   = invPow k (f⁻¹ (f (proj-obj k (x.F₀ (embed-pair k A)))))   [invPow definition]
  --   = invPow k (proj-obj k (x.F₀ (embed-pair k A)))             [f⁻¹∘f]
  -- permuted-liftAt-step：F₀ 分量经如下链抵消：
  --   invPow (suc k) (proj-obj (suc k) ((permuted-embed x).F₀ (embed-pair k A)))
  --   = invPow (suc k) (f (proj-obj k (x.F₀ (embed-pair k A))))   [proj-obj-liftF]
  --   = invPow k (f⁻¹ (f (proj-obj k (x.F₀ (embed-pair k A)))))   [invPow 定义]
  --   = invPow k (proj-obj k (x.F₀ (embed-pair k A)))             [f⁻¹∘f]
  permuted-liftAt-step
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → ∀ k
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
      (ed : EmbeddingData x)
    → permuted-liftAt f f⁻¹ f⁻¹∘f (suc k) (permuted-embed k f x ed)
      ≈C permuted-liftAt f f⁻¹ f⁻¹∘f k x
  permuted-liftAt-step f f⁻¹ f⁻¹∘f zero x ed
    ._≈C_.unfoldFunctor₀-eq {A} s =
    let z = embed-obj 1 A , embed-shape 1 (embed-obj 1 A)
    in begin
      invPow 1 f f⁻¹ (proj-obj 1
        (Unfolding.unfoldFunctor (out (permuted-embed zero f x ed))
          .Functor.F₀ z))
        ≡⟨ refl ⟩
      invPow 1 f f⁻¹ (proj-obj 1 (permuted-F₀ zero f x z))
        ≡⟨ cong (invPow 1 f f⁻¹) (proj-obj-permuted-F₀ zero f x z) ⟩
      invPow 1 f f⁻¹ (f (proj-obj zero
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))))
        ≡⟨ refl ⟩
      invPow 0 f f⁻¹ (f⁻¹ (f (proj-obj zero
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))))
        ≡⟨ cong (invPow 0 f f⁻¹) (f⁻¹∘f (proj-obj zero
             (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))) ⟩
      invPow 0 f f⁻¹ (proj-obj zero
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))
        ∎
  permuted-liftAt-step f f⁻¹ f⁻¹∘f zero x ed ._≈C_.pos-to-shape-eq s p = refl
  permuted-liftAt-step f f⁻¹ f⁻¹∘f zero x ed ._≈C_.unfold-next-eq {A} s =
    permuted-liftAt-step f f⁻¹ f⁻¹∘f zero
      (Unfolding.unfold-next (out x) {A = A} s)
      (EmbeddingData.next ed {A = A} s)
  permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m) x ed
    ._≈C_.unfoldFunctor₀-eq {A} s =
    let z = embed-obj (suc (suc m)) A ,
              embed-shape (suc (suc m)) (embed-obj (suc (suc m)) A)
    in begin
      invPow (suc (suc m)) f f⁻¹ (proj-obj (suc (suc m))
        (Unfolding.unfoldFunctor (out (permuted-embed (suc m) f x ed))
          .Functor.F₀ z))
        ≡⟨ refl ⟩
      invPow (suc (suc m)) f f⁻¹ (proj-obj (suc (suc m))
        (permuted-F₀ (suc m) f x z))
        ≡⟨ cong (invPow (suc (suc m)) f f⁻¹)
             (proj-obj-permuted-F₀ (suc m) f x z) ⟩
      invPow (suc (suc m)) f f⁻¹ (f (proj-obj (suc m)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))))
        ≡⟨ refl ⟩
      invPow (suc m) f f⁻¹ (f⁻¹ (f (proj-obj (suc m)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))))
        ≡⟨ cong (invPow (suc m) f f⁻¹) (f⁻¹∘f (proj-obj (suc m)
             (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))) ⟩
      invPow (suc m) f f⁻¹ (proj-obj (suc m)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))
        ∎
  permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m) x ed
    ._≈C_.pos-to-shape-eq s p = refl
  permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m) x ed
    ._≈C_.unfold-next-eq {A} s =
    permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m)
      (Unfolding.unfold-next (out x)
        {A = embed-obj (suc m) A}
        (embed-shape (suc m) (embed-obj (suc m) A)))
      (EmbeddingData.next ed
        {A = embed-obj (suc m) A}
        (embed-shape (suc m) (embed-obj (suc m) A)))

  -- permuted-liftAt preserves _≈C_
  -- permuted-liftAt 保持 _≈C_
  permuted-liftAt-resp
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → ∀ k {x y : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k))}
    → _≈C_ {C = StrictLayer.C (Tower.layer nTower k)}
           {FC = StrictLayer.FC (Tower.layer nTower k)} x y
    → _≈C_ {C = FinCatN} {FC = TrivialFCN}
           (permuted-liftAt f f⁻¹ f⁻¹∘f k x)
           (permuted-liftAt f f⁻¹ f⁻¹∘f k y)
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f zero    eq = eq
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k) {x} {y} eq
    ._≈C_.unfoldFunctor₀-eq {A} s =
      let a  = embed-obj (suc k) A
          sh = embed-shape (suc k) a
      in cong (λ b → invPow (suc k) f f⁻¹ (proj-obj (suc k) b))
           (eq ._≈C_.unfoldFunctor₀-eq {A = a} sh)
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k) eq
    ._≈C_.pos-to-shape-eq s p = refl
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k) {x} {y} eq
    ._≈C_.unfold-next-eq {A} s =
      permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k)
        (eq ._≈C_.unfold-next-eq
              {A = embed-obj (suc k) A}
              (embed-shape (suc k) (embed-obj (suc k) A)))

  -- PreservesF₀At k embed: embed preserves the first component of F₀ at
  -- layer k, pointwise in the input cosmos and the lifted shape
  -- PreservesF₀At k embed：embed 在层 k 保持 F₀ 的第一分量，
  -- 对输入宇宙与提升形状逐点成立
  PreservesF₀At
    : (k : ℕ)
    → (embed : ∀ k
               → (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                           (StrictLayer.FC (Tower.layer nTower k)))
               → EmbeddingData x
               → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                        (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Set _
  PreservesF₀At k embed =
    ∀ (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
      (ed : EmbeddingData x)
      (z : Category.Obj (ShapeCat
            (StrictLayer.C (Tower.layer nTower (suc k)))
            (StrictLayer.FC (Tower.layer nTower (suc k)))))
    → proj₁ (Unfolding.unfoldFunctor (out (embed k x ed)) .Functor.F₀ z)
      ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)

  -- permuted-embed does not preserve F₀ at layer 0 whenever f has a
  -- non-fixed point; the witness is the probe point a
  -- 当 f 有非不动点时，permuted-embed 在层 0 不保持 F₀；
  -- 见证为探针点 a
  ¬-preserves-permuted
    : ∀ (f : Fin n → Fin n)
    → Σ (Fin n) (λ a → f a ≢ a)
    → ¬ PreservesF₀At 0 (λ k x ed → permuted-embed k f x ed)
  ¬-preserves-permuted f (a , fa≢a) pres =
    fa≢a (pres x ed z)
    where
      x  = cosmos-idN
      ed = UniformEmbeddingFamily.getData (default-unif 0) x
      z : Category.Obj (ShapeCat
            (StrictLayer.C (Tower.layer nTower 1))
            (StrictLayer.FC (Tower.layer nTower 1)))
      z = (a , lift tt) , lift (lift tt)

  -- Nontrivial permutation: exists at least one non-fixed point
  -- 非平凡置换：至少存在一个非不动点
  NontrivialPerm : (Fin n → Fin n) → Set
  NontrivialPerm f = Σ (Fin n) (λ a → f a ≢ a)

  -- Permuted path witness: the four properties that refute criterion C
  -- This is the seed of nonlinearity: it is a single-layer construction,
  -- but its existence in the sparsest structure (Fin n's permutation
  -- group) is what makes nonlinear behavior in composite chains possible
  -- The name reflects the mechanism (permutation) rather than the
  -- consequence (nonlinearity), since nonlinearity only manifests at the
  -- composite level and is not a property of this record itself
  -- 置换路径见证：反驳判据 C 的四条性质
  -- 这是非线性的种子：它是单层构造，但它在最贫瘠结构
  -- （Fin n 的置换群）中的存在，使复合链上的非线性行为成为可能
  -- 命名反映机制（置换）而非后果（非线性），因非线性只在复合层
  -- 显现，不是本记录自身的性质
  record PermutedPathWitness
      (embed : ∀ k
               → (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                           (StrictLayer.FC (Tower.layer nTower k)))
               → EmbeddingData x
               → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                        (StrictLayer.FC (Tower.layer nTower (suc k))))
    : Setω where
    field
      liftAt        : ∀ k
                    → Cosmos (StrictLayer.C (Tower.layer nTower k))
                             (StrictLayer.FC (Tower.layer nTower k))
                    → Cosmos FinCatN TrivialFCN
      liftAt-step   : ∀ k x ed → liftAt (suc k) (embed k x ed) ≈C liftAt k x
      liftAt-resp   : ∀ k {x y}
                    → _≈C_ {C = StrictLayer.C (Tower.layer nTower k)}
                           {FC = StrictLayer.FC (Tower.layer nTower k)} x y
                    → liftAt k x ≈C liftAt k y
      liftAt-0-inj  : ∀ {x y} → liftAt 0 x ≈C liftAt 0 y → x ≈C y
      not-preserves : ¬ PreservesF₀At 0 embed

  -- Permuted path existence theorem
  -- For any nontrivial permutation f with inverse f⁻¹ satisfying
  -- f⁻¹∘f = id, constructs an embedding (permuted-embed f) and a
  -- liftAt (permuted-liftAt f f⁻¹) such that liftAt-step,
  -- liftAt-resp and liftAt-0-inj hold (feasibility), while
  -- PreservesF₀At fails (the embedding does not preserve F₀ at layer 0)
  -- Together these refute criterion C: feasibility does not imply
  -- preservation of F₀
  -- 置换路径存在性定理
  -- 对任意满足 f⁻¹∘f = id 的非平凡置换 f，构造嵌入
  -- permuted-embed f 与 liftAt permuted-liftAt f f⁻¹，使
  -- liftAt-step、liftAt-resp 与 liftAt-0-inj 成立（可行性），
  -- 而 PreservesF₀At 失败（嵌入在层 0 不保持 F₀）
  -- 合起来反驳判据 C：可行性不蕴含 F₀ 的保持
  permuted-path-exists
    : (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → (nontriv : NontrivialPerm f)
    → PermutedPathWitness (λ k x ed → permuted-embed k f x ed)
  permuted-path-exists f f⁻¹ f⁻¹∘f nontriv = record
    { liftAt        = permuted-liftAt f f⁻¹ f⁻¹∘f
    ; liftAt-step   = λ k x ed → permuted-liftAt-step f f⁻¹ f⁻¹∘f k x ed
    ; liftAt-resp   = λ k {x} {y} eq → permuted-liftAt-resp f f⁻¹ f⁻¹∘f k eq
    ; liftAt-0-inj  = λ eq → eq
    ; not-preserves = ¬-preserves-permuted f nontriv
    }

  -- swapSum exchanges the two elements of Fin 2, leaving Fin m untouched
  -- swapSum 交换 Fin 2 的两个元素，Fin m 不动
  swapSum : Fin 2 ⊎ Fin m → Fin 2 ⊎ Fin m
  swapSum (inj₁ i) = inj₁ (opposite i)
  swapSum (inj₂ k) = inj₂ k

  -- swapSum is an involution, via the standard opposite-involutive
  -- swapSum 是对合，经标准库 opposite-involutive 得证
  swapSum-involutive : ∀ x → swapSum (swapSum x) ≡ x
  swapSum-involutive (inj₁ i) = cong inj₁ (opposite-involutive i)
  swapSum-involutive (inj₂ k) = refl

  -- swap01 exchanges fzero and fsuc fzero, leaving all other elements
  -- fixed. Defined via splitAt/join so that no UnsupportedIndexedMatch
  -- warning arises
  -- swap01 交换 fzero 与 fsuc fzero，其余元素不动。
  -- 经 splitAt/join 定义，避免 UnsupportedIndexedMatch 警告
  swap01 : Fin n → Fin n
  swap01 i = join 2 m (swapSum (splitAt 2 i))

  -- swap01 is an involution
  -- swap01 是对合
  swap01-involutive : ∀ a → swap01 (swap01 a) ≡ a
  swap01-involutive i =
    begin
      swap01 (swap01 i)
        ≡⟨ refl ⟩
      join 2 m (swapSum (splitAt 2 (join 2 m (swapSum (splitAt 2 i)))))
        ≡⟨ cong (join 2 m)
             (cong swapSum (splitAt-join 2 m (swapSum (splitAt 2 i)))) ⟩
      join 2 m (swapSum (swapSum (splitAt 2 i)))
        ≡⟨ cong (join 2 m) (swapSum-involutive (splitAt 2 i)) ⟩
      join 2 m (splitAt 2 i)
        ≡⟨ join-splitAt 2 m i ⟩
      i
      ∎

  -- swap01 has a non-fixed point: fzero maps to fsuc fzero ≠ fzero.
  -- The witness fsuc-fzero≠fzero is imported from FinCatNWitness
  -- swap01 有非不动点：fzero 映到 fsuc fzero ≠ fzero。
  -- 见证 fsuc-fzero≠fzero 由 FinCatNWitness 导入
  swap01-nontrivial : NontrivialPerm swap01
  swap01-nontrivial = fzero , fsuc-fzero≠fzero

  -- Unconditional existence of a permuted path, specialised to swap01
  -- 置换路径的无条件存在性，特化到 swap01
  nontrivial-path-exists
    : PermutedPathWitness (λ k x ed → permuted-embed k swap01 x ed)
  nontrivial-path-exists =
    permuted-path-exists swap01 swap01 swap01-involutive swap01-nontrivial
