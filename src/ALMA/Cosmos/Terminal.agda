------------------------------------------------------------------------
-- Terminal Coalgebra of CosmosF
-- CosmosF 的终余代数
--
-- Defines general F-coalgebras, the anamorphism (unfold) into Cosmos,
-- a bisimulation relation _≈C_ on Cosmos, and establishes the universal
-- property: Cosmos is the terminal coalgebra of the polynomial functor CosmosF
-- 定义一般 F-余代数、到 Cosmos 的 anamorphism（展开）、Cosmos 上的互模拟关系 _≈C_，
-- 并证明泛性质：Cosmos 是多项式函子 CosmosF 的终余代数
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.Terminal where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (∃; _,_; _×_)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning; subst-subst; subst-sym-subst)
open ≡-Reasoning
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.Unfolding using (Unfolding; mapUnfolding)
open import ALMA.Cosmos
  using (Cosmos; CosmosF; out; unfoldingCore; module CosmosMap)
open CosmosMap using (mapCosmosF)

-- Parameterised module: fixes a base category C and a container-valued
-- functor FC : C → ContCat; all constructions below are relative to these
-- 参数化模块：固定基范畴 C 与容器值函子 FC : C → ContCat；
-- 以下所有构造均相对于这些参数
module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    -- Overall level of objects in this module
    -- 本模块中对象的总层级
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

  -- A general F-coalgebra: a carrier set and a structure map into CosmosF
  -- 一般 F-余代数：一个载体集与到 CosmosF 的结构映射
  record Coalgebra : Set (lsuc L) where
    field
      -- Carrier set of the coalgebra
      -- 余代数的载体集
      Carrier : Set L
      -- Structure map α : Carrier → F Carrier
      -- 结构映射 α : Carrier → F Carrier
      α       : Carrier → CosmosF C FC Carrier

  -- A homomorphism between coalgebras: a map commuting with the structure maps
  -- 余代数之间的同态：使结构映射交换的映射
  record CoalgHom (X Y : Coalgebra) : Set L where
    private module X = Coalgebra X; module Y = Coalgebra Y
    field
      -- Underlying function between carriers
      -- 载体之间的底层函数
      f       : X.Carrier → Y.Carrier
      -- Commutation with the structure maps
      -- 与结构映射的交换性
      commute : ∀ x → mapCosmosF f (X.α x) ≡ Y.α (f x)

  -- The canonical coalgebra structure on Cosmos itself, given by out
  -- Cosmos 自身上的典范余代数结构，由 out 给出
  cosmosCoalg : Coalgebra
  cosmosCoalg = record { Carrier = Cosmos C FC ; α = out }

  -- Anamorphism (unfold): given any coalgebra (X, α), construct a map
  -- X → Cosmos by recursively unfolding the next seeds
  -- anamorphism（展开）：给定任意余代数 (X, α)，
  -- 通过递归展开下一层种子构造映射 X → Cosmos
  ana : (X : Coalgebra) → Coalgebra.Carrier X → Cosmos C FC
  ana X x .out = record
    { unfoldingCore = record
        { unfoldFunctor   = u₀.unfoldFunctor
        ; unfold-next     = λ s → ana X (u₀.unfold-next s)
        ; pos-to-shape    = u₀.pos-to-shape
        ; pos-actS-compat = u₀.pos-actS-compat
        }
    }
    where
      u₀ = unfoldingCore (Coalgebra.α X x)
      module u₀ = Unfolding u₀

  -- The anamorphism is a coalgebra homomorphism from X to Cosmos
  -- anamorphism 是从 X 到 Cosmos 的余代数同态
  ana-hom : (X : Coalgebra) → CoalgHom X cosmosCoalg
  ana-hom X = record { f = ana X ; commute = λ _ → refl }

  -- Bisimulation relation on Cosmos: two Cosmos values are equivalent if
  -- their unfolding functors agree and next seeds are coinductively equivalent
  -- Cosmos 上的互模拟关系：两个 Cosmos 对象等价当且仅当其展开函子一致，
  -- 且下一层种子余归纳地等价
  record _≈C_ (F G : Cosmos C FC) : Set L where
    coinductive
    module UF = Unfolding (unfoldingCore (out F))
    module UG = Unfolding (unfoldingCore (out G))
    field
      -- Unfolding functors are propositionally equal
      -- 展开函子命题相等
      unfoldFunctor-eq : UF.unfoldFunctor ≡ UG.unfoldFunctor
      -- Position-to-shape maps agree after transport along the above equality
      -- 位置到形状映射沿上述等式输送后一致
      pos-to-shape-eq  : ∀ {A} (s : ShapeOf FC A) (p : PosOf FC s)
                       → subst (λ G → ShapeOf FC (Functor.₀ G (A , s)))
                                unfoldFunctor-eq
                                (UF.pos-to-shape s p)
                       ≡ UG.pos-to-shape s p
      -- Next seeds are coinductively equivalent
      -- 下一层种子余归纳地等价
      unfold-next-eq   : ∀ {A} (s : ShapeOf FC A)
                       → UF.unfold-next s ≈C UG.unfold-next s

  open _≈C_ public

  -- Reflexivity of the bisimulation relation
  -- 互模拟关系的自反性
  ≈C-refl : ∀ {F} → F ≈C F
  ≈C-refl .unfoldFunctor-eq = refl
  ≈C-refl .pos-to-shape-eq _ _ = refl
  ≈C-refl .unfold-next-eq _ = ≈C-refl

  -- Symmetry of the bisimulation relation
  -- 互模拟关系的对称性
  ≈C-sym : ∀ {F G} → F ≈C G → G ≈C F
  ≈C-sym {F} {G} eq .unfoldFunctor-eq = sym (eq .unfoldFunctor-eq)
  ≈C-sym {F} {G} eq .pos-to-shape-eq {A} s p =
    let module UF' = Unfolding (unfoldingCore (out F))
        module UG' = Unfolding (unfoldingCore (out G))
        P = λ G → ShapeOf FC (Functor.₀ G (A , s))
        u = eq .unfoldFunctor-eq
    in begin
      subst P (sym u) (UG'.pos-to-shape s p)
        ≡⟨ cong (subst P (sym u)) (sym (eq .pos-to-shape-eq s p)) ⟩
      subst P (sym u) (subst P u (UF'.pos-to-shape s p))
        ≡⟨ subst-sym-subst u ⟩
      UF'.pos-to-shape s p
    ∎
  ≈C-sym eq .unfold-next-eq s = ≈C-sym (eq .unfold-next-eq s)

  -- Transitivity of the bisimulation relation
  -- 互模拟关系的传递性
  ≈C-trans : ∀ {F G H} → F ≈C G → G ≈C H → F ≈C H
  ≈C-trans {F} {G} {H} e1 e2 .unfoldFunctor-eq =
    trans (e1 .unfoldFunctor-eq) (e2 .unfoldFunctor-eq)
  ≈C-trans {F} {G} {H} e1 e2 .pos-to-shape-eq {A} s p =
    let module UF' = Unfolding (unfoldingCore (out F))
        module UG' = Unfolding (unfoldingCore (out G))
        module UH' = Unfolding (unfoldingCore (out H))
        P = λ G → ShapeOf FC (Functor.₀ G (A , s))
        p₁ = e1 .unfoldFunctor-eq
        p₂ = e2 .unfoldFunctor-eq
        uf = UF'.pos-to-shape s p
        ug = UG'.pos-to-shape s p
        uh = UH'.pos-to-shape s p
    in begin
      subst P (trans p₁ p₂) uf
        ≡⟨ sym (subst-subst p₁ {y≡z = p₂}) ⟩
      subst P p₂ (subst P p₁ uf)
        ≡⟨ cong (subst P p₂) (e1 .pos-to-shape-eq s p) ⟩
      subst P p₂ ug
        ≡⟨ e2 .pos-to-shape-eq s p ⟩
      uh
    ∎
  ≈C-trans e1 e2 .unfold-next-eq s =
    ≈C-trans (e1 .unfold-next-eq s) (e2 .unfold-next-eq s)

  -- The setoid of Cosmos objects under bisimulation equivalence
  -- 互模拟等价下的 Cosmos 对象构成的 Setoid
  cosmosSetoid : Setoid L L
  cosmosSetoid = record
    { Carrier       = Cosmos C FC
    ; _≈_           = _≈C_
    ; isEquivalence = record
      { refl  = ≈C-refl ; sym = ≈C-sym ; trans = ≈C-trans }
    }

  -- Uniqueness of the anamorphism: any coalgebra homomorphism to Cosmos
  -- is bisimilar to the canonical unfold
  -- anamorphism 的唯一性：任何到 Cosmos 的余代数同态均与典范展开互模拟
  unique-ana : (X : Coalgebra) (fhom : CoalgHom X cosmosCoalg)
             → ∀ x → CoalgHom.f fhom x ≈C ana X x
  unique-ana X fhom = λ x → helper x refl refl
    where
      module X  = Coalgebra X
      module fh = CoalgHom fhom
      open _≈C_
      open Unfolding using (unfoldFunctor; unfold-next; pos-to-shape)

      -- Lemma: position-to-shape maps agree after transport, given
      -- equalities of unfolding cores
      -- 引理：给定展开核的等式，位置到形状映射在输送后一致
      pts-eq-lemma : ∀ {A : Set L} {u v : Unfolding FC (Cosmos C FC)} {u₀ : Unfolding FC A}
                       (f g : A → Cosmos C FC) {B}
                   → (eq-u : u ≡ mapUnfolding f u₀)
                   → (eq-v : v ≡ mapUnfolding g u₀)
                   → (s : ShapeOf FC B) (p : PosOf FC s)
                   → subst (λ G → ShapeOf FC (Functor.₀ G (B , s)))
                            (trans (cong unfoldFunctor eq-u)
                                   (sym (cong unfoldFunctor eq-v)))
                            (pos-to-shape u s p)
                     ≡ pos-to-shape v s p
      pts-eq-lemma _ _ eq-u eq-v s p rewrite eq-u | eq-v = refl

      -- Core helper: given x and equalities a ≡ fhom f x and b ≡ ana X x,
      -- prove a ≈C b by coinduction
      -- 核心辅助：给定 x 及等式 a ≡ fhom f x 与 b ≡ ana X x，
      -- 通过余归纳证明 a ≈C b
      helper : ∀ {a b : Cosmos C FC} (x : X.Carrier)
            → (a≡fx : a ≡ fh.f x) (b≡anax : b ≡ ana X x)
            → a ≈C b
      helper {a} {b} x a≡fx b≡anax = go
        where
          u₀ = unfoldingCore (X.α x)

          eq-UF : unfoldingCore (out a) ≡ mapUnfolding fh.f u₀
          eq-UF = begin
            unfoldingCore (out a)
              ≡⟨ cong unfoldingCore (cong out a≡fx) ⟩
            unfoldingCore (out (fh.f x))
              ≡⟨ sym (cong unfoldingCore (fh.commute x)) ⟩
            mapUnfolding fh.f u₀
            ∎

          eq-UG : unfoldingCore (out b) ≡ mapUnfolding (ana X) u₀
          eq-UG = begin
            unfoldingCore (out b)
              ≡⟨ cong unfoldingCore (cong out b≡anax) ⟩
            unfoldingCore (out (ana X x))
              ≡⟨ refl ⟩
            mapUnfolding (ana X) u₀
            ∎

          go : a ≈C b
          go .unfoldFunctor-eq = trans (cong unfoldFunctor eq-UF) (sym (cong unfoldFunctor eq-UG))
          go .pos-to-shape-eq = pts-eq-lemma fh.f (ana X) eq-UF eq-UG
          go .unfold-next-eq {A} s =
            let seed = unfold-next u₀ s
                a'≡ = cong (λ u → unfold-next u s) eq-UF
                b'≡ = cong (λ u → unfold-next u s) eq-UG
            in helper seed a'≡ b'≡

  -- Terminality: Cosmos is a terminal coalgebra: existence of anamorphism
  -- and uniqueness up to bisimulation
  -- 终余代数性：Cosmos 是终余代数——anamorphism 的存在性以及在互模拟意义下的唯一性
  terminality : ∀ (X : Coalgebra)
              → ∃ λ (f : Coalgebra.Carrier X → Cosmos C FC) →
                  (∀ x → mapCosmosF f (Coalgebra.α X x) ≡ out (f x))
                × (∀ g → (∀ x → mapCosmosF g (Coalgebra.α X x) ≡ out (g x))
                        → ∀ x → f x ≈C g x)
  terminality X =
    ( ana X
    , (λ _ → refl)
    , λ g gcomm x → ≈C-sym (unique-ana X (record { f = g ; commute = gcomm }) x)
    )
