------------------------------------------------------------------------
-- Proof-relevant relations compose as a proarrow equipment, not as a
-- plain 1-category.
--
-- A type-valued relation R : I → J → Set r carries its witnesses; the
-- composite (R ∘ S) x z is the Sigma of a *middle* index y together
-- with the two edge witnesses. Identity is propositional equality.
-- Unit and associativity therefore hold only up to canonical Sigma
-- reassociation bijections (the equipment 2-cells); these bijections
-- keep every witness and need no UIP.
--
-- A plain 1-category instead has one fixed hom per pair of objects, so
-- its composite must be independent of the middle: the hom is a subset,
-- i.e. a proposition (at most one witness per edge). Two obstructions:
--
--   * Diamond. When two *distinct* middle indices fill the same edge,
--     the Sigma composite has two distinguishable witnesses. Demanding
--     they are propositionally equal yields a direct contradiction
--     (the two middle indices are forced equal): strict-1cat-diamond→⊥.
--
--   * Parallel witnesses. With a unique middle but several edge
--     witnesses, demanding a propositional composite forces the edge
--     fibre to be a proposition (strict-1cat→fibre-prop), i.e. UIP for
--     an arbitrary fibre type.
--
-- Under --safe --cubical-compatible general UIP is not derivable
-- (proof-irrelevance/K is off) and an internal refutation would need a
-- provably non-UIP fibre (a cubical HIT), which is absent. The strict
-- 1-category is therefore conditional on fibre propositionality, an
-- assumption that is not logically necessary. The cost-free object is
-- the equipment: for PushSimˢ the 2-cells are push-comp (composition)
-- and push-map (rescoping), and MCorrSetoidPushCat restricts to
-- deterministic index functions precisely so that the middle is fixed
-- by composition and a plain category results.
--
-- 证明相关（类型值）关系复合为 proarrow equipment，而非普通 1-范畴。
--
-- 类型值关系 R : I → J → Set r 携带见证；复合 (R ∘ S) x z 是*中间*索引
-- y 与两条边见证的 Σ。恒等为命题相等。故单位与结合只在典范 Σ-重结合双射
-- （equipment 的 2-胞腔）意义下成立；这些双射保留全部见证，无需 UIP。
--
-- 普通 1-范畴对每对对象只有一个固定 hom，其复合必须与中项无关：hom 是
-- 子集即命题（每条边至多一个见证）。两条障碍：
--
--   * 菱形。当两个*不同*的中间索引填补同一条边时，Σ 复合有两个可区分
--     见证；要求它们命题相等直接矛盾（两个中项被强制相等），见
--     strict-1cat-diamond→⊥。
--
--   * 平行见证。中项唯一但边见证有多条时，要求复合命题化迫使边纤维为
--     命题（strict-1cat→fibre-prop），即任意纤维类型的 UIP。
--
-- 在 --safe --cubical-compatible 下一般 UIP 不可导（证明无关/K 关闭），
-- 内部证伪还需可证非 UIP 的纤维（cubical HIT），此处不具备。故严格
-- 1-范畴以纤维命题化为条件，该条件并非逻辑必然。零成本对象是 equipment：
-- 对 PushSimˢ，2-胞腔即 push-comp（复合）与 push-map（重定域），而
-- MCorrSetoidPushCat 恰因限定为确定性索引函数、使中项由复合唯一固定，
-- 才得到普通范畴。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.RelEquipment where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁; proj₂; _×_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

------------------------------------------------------------------------
-- Identity relation and Sigma composition through a middle.
-- 恒等关系与经中项的 Σ 复合。

IdR : ∀ {i : Level} {I : Set i} → I → I → Set i
IdR x y = x ≡ y

infixr 9 _∘ᵣ_
_∘ᵣ_ : ∀ {i j k ℓr ℓs : Level}
         {I : Set i} {J : Set j} {K : Set k}
       (R : I → J → Set ℓr) (S : J → K → Set ℓs)
     → I → K → Set (j ⊔ ℓr ⊔ ℓs)
_∘ᵣ_ {J = J} R S x z = Σ J λ y → R x y × S y z

------------------------------------------------------------------------
-- The equipment 2-cells: unit and associator are canonical Sigma
-- reassociation bijections with definitional round-trips. They retain
-- the witnesses and never identify two of them.
-- equipment 的 2-胞腔：单位与结合子是典范 Σ-重结合双射，往返定义性
-- 成立；它们保留见证，绝不把两个见证等同。

module _ {i j ℓr : Level} {I : Set i} {J : Set j}
         (R : I → J → Set ℓr) where

  unit-l-fwd : ∀ {x z} → (IdR ∘ᵣ R) x z → R x z
  unit-l-fwd (x , refl , r) = r
  unit-l-bwd : ∀ {x z} → R x z → (IdR ∘ᵣ R) x z
  unit-l-bwd r = _ , refl , r

  unit-r-fwd : ∀ {x z} → (R ∘ᵣ IdR) x z → R x z
  unit-r-fwd (z , r , refl) = r
  unit-r-bwd : ∀ {z : J} {x} → R x z → (R ∘ᵣ IdR) x z
  unit-r-bwd {z = z} r = z , r , refl

  unit-l-fwd∘bwd : ∀ {x z} (r : R x z) → unit-l-fwd (unit-l-bwd r) ≡ r
  unit-l-fwd∘bwd r = refl
  unit-r-fwd∘bwd : ∀ {x z} (r : R x z) → unit-r-fwd (unit-r-bwd r) ≡ r
  unit-r-fwd∘bwd r = refl

module _ {i ℓr ℓs ℓt : Level}
         {I J K L : Set i}
         (R : I → J → Set ℓr)
         (S : J → K → Set ℓs)
         (T : K → L → Set ℓt) where

  assoc-fwd : ∀ {x w} → ((R ∘ᵣ S) ∘ᵣ T) x w → (R ∘ᵣ (S ∘ᵣ T)) x w
  assoc-fwd (z , (y , r , s) , t) = y , r , (z , s , t)
  assoc-bwd : ∀ {x w} → (R ∘ᵣ (S ∘ᵣ T)) x w → ((R ∘ᵣ S) ∘ᵣ T) x w
  assoc-bwd (y , r , (z , s , t)) = z , (y , r , s) , t

  assoc-fwd∘bwd : ∀ {x w} (q : (R ∘ᵣ (S ∘ᵣ T)) x w)
                → assoc-fwd (assoc-bwd q) ≡ q
  assoc-fwd∘bwd (y , r , (z , s , t)) = refl
  assoc-bwd∘fwd : ∀ {x w} (p : ((R ∘ᵣ S) ∘ᵣ T) x w)
                → assoc-bwd (assoc-fwd p) ≡ p
  assoc-bwd∘fwd (z , (y , r , s) , t) = refl

------------------------------------------------------------------------
-- A proposition has at most one inhabitant; this is what a subset hom
-- demands of every edge fibre.
-- 命题至多一个居民；子集 hom 对每条边纤维的正在于此。

IsProp : ∀ {ℓ : Level} → Set ℓ → Set ℓ
IsProp X = ∀ (x y : X) → x ≡ y

------------------------------------------------------------------------
-- Diamond obstruction: two distinct middle indices fill the same edge
-- 0 ─→ 3. A propositional composite would identify the two Sigma
-- witnesses, forcing 1 ≡ 2, which is absurd. Unconditional, no UIP.
-- 菱形障碍：两个不同中项填补同一条边 0 ─→ 3。命题化复合会等同两个 Σ
-- 见证，迫使 1 ≡ 2，矛盾。无条件，无需 UIP。

private
  -- Four-node shape 0 ─→ 1 ─→ 3 and 0 ─→ 2 ─→ 3.
  -- 四节点形状 0 ─→ 1 ─→ 3 与 0 ─→ 2 ─→ 3。
  data D4 : Set where
    n0 n1 n2 n3 : D4

  R◇ : D4 → D4 → Set lzero
  R◇ n0 n0 = ⊥
  R◇ n0 n1 = ⊤
  R◇ n0 n2 = ⊤
  R◇ n0 n3 = ⊥
  R◇ n1 _  = ⊥
  R◇ n2 _  = ⊥
  R◇ n3 _  = ⊥

  S◇ : D4 → D4 → Set lzero
  S◇ n0 _  = ⊥
  S◇ n1 n0 = ⊥
  S◇ n1 n1 = ⊥
  S◇ n1 n2 = ⊥
  S◇ n1 n3 = ⊤
  S◇ n2 n0 = ⊥
  S◇ n2 n1 = ⊥
  S◇ n2 n2 = ⊥
  S◇ n2 n3 = ⊤
  S◇ n3 _  = ⊥

  w◇₁ : (R◇ ∘ᵣ S◇) n0 n3
  w◇₁ = n1 , tt , tt
  w◇₂ : (R◇ ∘ᵣ S◇) n0 n3
  w◇₂ = n2 , tt , tt

  ¬1≡2 : ¬ (n1 ≡ n2)
  ¬1≡2 ()

-- If the composite edge fibre were a proposition, the two distinct
-- middles would coincide, a contradiction.
-- 若复合边纤维为命题，两个不同中项将重合，矛盾。
strict-1cat-diamond→⊥ : IsProp ((R◇ ∘ᵣ S◇) n0 n3) → ⊥
strict-1cat-diamond→⊥ prop =
  ¬1≡2 (cong proj₁ (prop w◇₁ w◇₂))

------------------------------------------------------------------------
-- Parallel-witness obstruction: with a single object (hence a unique
-- middle) and an arbitrary edge fibre P, a propositional composite
-- P × P forces any two inhabitants of P to coincide, i.e. UIP for P.
-- 平行见证障碍：单一对象（故中项唯一）而边纤维为任意 P 时，命题化复合
-- P × P 迫使 P 的任意两个居民重合，即 P 的 UIP。

module _ {ℓ : Level} (P : Set ℓ) where

  private
    RP : ⊤ {ℓ} → ⊤ {ℓ} → Set ℓ
    RP tt tt = P

    wP : P → P → (RP ∘ᵣ RP) tt tt
    wP p q = tt , p , q

  strict-1cat→fibre-prop
    : IsProp ((RP ∘ᵣ RP) tt tt) → IsProp P
  strict-1cat→fibre-prop prop a b =
    cong proj₂ (cong proj₂ (prop (wP a a) (wP a b)))
