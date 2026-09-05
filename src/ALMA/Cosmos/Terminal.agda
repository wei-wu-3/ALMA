------------------------------------------------------------------------
-- Terminal Coalgebra of CosmosF (Setoid carrier + ≡ commute)
-- CosmosF 的终余代数（Setoid 载体 + ≡ 交换条件）
--
-- Defines general F-coalgebras with Setoid carriers and Func structure maps,
-- the anamorphism (unfold) into Cosmos, a bisimulation relation _≈C_ on Cosmos,
-- and establishes the universal property: Cosmos is the terminal coalgebra of
-- the polynomial functor CosmosF (up to bisimulation).
-- 定义具有 Setoid 载体与 Func 结构映射的一般 F-余代数、到 Cosmos 的 anamorphism（展开）、
-- Cosmos 上的互模拟关系 _≈C_，并证明泛性质：Cosmos 是多项式函子 CosmosF 的
-- （互模拟意义下的）终余代数。
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
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.Unfolding
  using (Unfolding; mapUnfolding; module UnfoldingSetoid)
open import ALMA.Cosmos
  using (Cosmos; out; unfoldingCore; module CosmosMap; module CosmosFFunctor )
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

    module CFF = CosmosFFunctor
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {u = L} {C = C} {F = FC}

  -- Coalgebra: Setoid carrier, Func structure map, ≡ commute
  -- 余代数：Setoid 载体，Func 结构映射，≡ 交换条件
  record Coalgebra : Set (lsuc L) where
    field
      -- Carrier setoid of the coalgebra
      -- 余代数的载体 Setoid
      Carrier : Setoid L L
      -- Structure map α : Carrier → CosmosF Carrier, preserving setoid equivalence
      -- 结构映射 α : Carrier → CosmosF Carrier，保持 setoid 等价
      α       : Func Carrier (CFF.CosmosFSetoid L Carrier)

  -- A homomorphism between coalgebras: a map commuting with the structure maps
  -- 余代数之间的同态：与结构映射交换的映射
  record CoalgHom (X Y : Coalgebra) : Set L where
    private module X = Coalgebra X; module Y = Coalgebra Y
    field
      -- Underlying setoid morphism between carriers
      -- 载体之间的底层 setoid 态射
      f       : Func X.Carrier Y.Carrier
      -- Commutation with the structure maps
      -- 与结构映射的交换性
      commute : ∀ x → mapCosmosF (Func.to f) (Func.to X.α x)
                     ≡ Func.to Y.α (Func.to f x)

  -- Bisimulation _≈C_ on Cosmos and cosmosSetoid
  -- Cosmos 上的互模拟 _≈C_ 及 cosmosSetoid
  record _≈C_ (F G : Cosmos C FC) : Set L where
    coinductive
    module UF = Unfolding (unfoldingCore (out F))
    module UG = Unfolding (unfoldingCore (out G))
    field
      -- Unfolding functors are pointwise equal on objects
      -- 展开函子在对象上逐点命题相等
      unfoldFunctor₀-eq : ∀ {A} (s : ShapeOf FC A)
                        → Functor.₀ UF.unfoldFunctor (A , s) ≡ Functor.₀ UG.unfoldFunctor (A , s)
      -- Position-to-shape maps agree after transport along the above equality
      -- 位置到形状映射沿上述等式传输后一致
      pos-to-shape-eq  : ∀ {A} (s : ShapeOf FC A) (p : PosOf FC s)
                       → subst (λ x → ShapeOf FC x) (unfoldFunctor₀-eq s)
                                (UF.pos-to-shape s p)
                       ≡ UG.pos-to-shape s p
      -- Next seeds are coinductively equivalent
      -- 下一层种子余归纳地等价
      unfold-next-eq   : ∀ {A} (s : ShapeOf FC A)
                       → UF.unfold-next s ≈C UG.unfold-next s
  open _≈C_

  -- Reflexivity of the bisimulation relation
  -- 互模拟关系的自反性
  ≈C-refl : ∀ {F} → F ≈C F
  ≈C-refl .unfoldFunctor₀-eq = λ _ → refl
  ≈C-refl .pos-to-shape-eq _ _ = refl
  ≈C-refl .unfold-next-eq _ = ≈C-refl

  -- Symmetry of the bisimulation relation
  -- 互模拟关系的对称性
  ≈C-sym : ∀ {F G} → F ≈C G → G ≈C F
  ≈C-sym {F} {G} eq .unfoldFunctor₀-eq = λ s → sym (eq .unfoldFunctor₀-eq s)
  ≈C-sym {F} {G} eq .pos-to-shape-eq {A} s p =
    let module UF' = Unfolding (unfoldingCore (out F))
        module UG' = Unfolding (unfoldingCore (out G))
        u = eq .unfoldFunctor₀-eq s
    in begin
      subst (λ x → ShapeOf FC x) (sym u) (UG'.pos-to-shape s p)
        ≡⟨ cong (subst (λ x → ShapeOf FC x) (sym u)) (sym (eq .pos-to-shape-eq s p)) ⟩
      subst (λ x → ShapeOf FC x) (sym u)
            (subst (λ x → ShapeOf FC x) u (UF'.pos-to-shape s p))
        ≡⟨ subst-sym-subst u ⟩
      UF'.pos-to-shape s p
    ∎
  ≈C-sym eq .unfold-next-eq s = ≈C-sym (eq .unfold-next-eq s)

  -- Transitivity of the bisimulation relation
  -- 互模拟关系的传递性
  ≈C-trans : ∀ {F G H} → F ≈C G → G ≈C H → F ≈C H
  ≈C-trans {F} {G} {H} e1 e2 .unfoldFunctor₀-eq = λ s → trans (e1 .unfoldFunctor₀-eq s) (e2 .unfoldFunctor₀-eq s)
  ≈C-trans {F} {G} {H} e1 e2 .pos-to-shape-eq {A} s p =
    let module UF' = Unfolding (unfoldingCore (out F))
        module UG' = Unfolding (unfoldingCore (out G))
        module UH' = Unfolding (unfoldingCore (out H))
        p₁ = e1 .unfoldFunctor₀-eq s
        p₂ = e2 .unfoldFunctor₀-eq s
        uf = UF'.pos-to-shape s p
        ug = UG'.pos-to-shape s p
        uh = UH'.pos-to-shape s p
    in begin
      subst (λ x → ShapeOf FC x) (trans p₁ p₂) uf
        ≡⟨ sym (subst-subst p₁ {y≡z = p₂}) ⟩
      subst (λ x → ShapeOf FC x) p₂ (subst (λ x → ShapeOf FC x) p₁ uf)
        ≡⟨ cong (subst (λ x → ShapeOf FC x) p₂) (e1 .pos-to-shape-eq s p) ⟩
      subst (λ x → ShapeOf FC x) p₂ ug
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

  -- Canonical coalgebra structure on Cosmos
  -- α.cong maps ≈C to ≈F via ≈C→≈U
  -- Cosmos 上的典范余代数结构
  -- α.cong 通过 ≈C→≈U 将 ≈C 映射为 ≈F
  cosmosCoalg : Coalgebra
  cosmosCoalg = record
    { Carrier = cosmosSetoid
    ; α       = record
        { to   = out
        ; cong = λ {F} {G} eq → record
            { contEquiv-eq = refl
            ; unfolding-eq  = ≈C→≈U eq
            }
        }
    }
    where
      ≈C→≈U : ∀ {F G} → F ≈C G
             → US._≈U_ {X = cosmosSetoid}
                 (unfoldingCore (out F)) (unfoldingCore (out G))
      ≈C→≈U eq = record
        { unfoldFunctor₀-eq = eq .unfoldFunctor₀-eq
        ; pos-to-shape-eq  = eq .pos-to-shape-eq
        ; unfold-next-eq   = eq .unfold-next-eq
        }

  -- Existence: anamorphism
  -- 存在性：anamorphism
  ana-to : (X : Coalgebra) → Setoid.Carrier (Coalgebra.Carrier X) → Cosmos C FC
  ana-to X x .out = record
    { unfoldingCore = record
        { unfoldFunctor   = u₀.unfoldFunctor
        ; unfold-next     = λ s → ana-to X (u₀.unfold-next s)
        ; pos-to-shape    = u₀.pos-to-shape
        ; pos-actS-compat = u₀.pos-actS-compat
        }
    }
    where
      u₀ = unfoldingCore (Func.to (Coalgebra.α X) x)
      module u₀ = Unfolding u₀

  -- Congruence of ana-to with respect to carrier equivalence
  -- ana-to 关于载体等价的兼容性
  ana-cong : (X : Coalgebra)
           → ∀ {x y} → Setoid._≈_ (Coalgebra.Carrier X) x y
           → ana-to X x ≈C ana-to X y
  ana-cong X {x} {y} x≈y .unfoldFunctor₀-eq =
    US._≈U_.unfoldFunctor₀-eq
      (CFF._≈F_.unfolding-eq (Func.cong (Coalgebra.α X) x≈y))
  ana-cong X {x} {y} x≈y .pos-to-shape-eq =
    US._≈U_.pos-to-shape-eq
      (CFF._≈F_.unfolding-eq (Func.cong (Coalgebra.α X) x≈y))
  ana-cong X {x} {y} x≈y .unfold-next-eq {A} s =
    ana-cong X (US._≈U_.unfold-next-eq
      (CFF._≈F_.unfolding-eq (Func.cong (Coalgebra.α X) x≈y)) s)

  -- The anamorphism as a Setoid morphism
  -- anamorphism 作为 Setoid 态射
  ana : (X : Coalgebra) → Func (Coalgebra.Carrier X) cosmosSetoid
  ana X = record { to = ana-to X ; cong = ana-cong X }

  -- The anamorphism is a coalgebra homomorphism from X to Cosmos
  -- anamorphism 是从 X 到 Cosmos 的余代数同态
  ana-hom : (X : Coalgebra) → CoalgHom X cosmosCoalg
  ana-hom X = record { f = ana X ; commute = λ _ → refl }

  -- Uniqueness
  -- 唯一性
  unique-ana : (X : Coalgebra) (fhom : CoalgHom X cosmosCoalg)
             → ∀ x → Func.to (CoalgHom.f fhom) x ≈C ana-to X x
  unique-ana X fhom = λ x → helper x refl refl
    where
      module X  = Coalgebra X
      module fh = CoalgHom fhom
      open _≈C_
      open Unfolding using (unfoldFunctor; unfold-next; pos-to-shape)

      -- Core helper: given x and equalities a ≡ fhom f x and b ≡ ana X x,
      -- prove a ≈C b by coinduction
      -- 核心辅助：给定 x 及等式 a ≡ fhom f x 与 b ≡ ana X x，
      -- 通过余归纳证明 a ≈C b
      helper : ∀ {a b : Cosmos C FC} (x : Setoid.Carrier X.Carrier)
             → (a≡fx : a ≡ Func.to fh.f x)
             → (b≡anax : b ≡ ana-to X x)
             → a ≈C b
      helper {a} {b} x a≡fx b≡anax = go
        where
          u₀ = unfoldingCore (Func.to X.α x)

          eq-UF : unfoldingCore (out a) ≡ mapUnfolding (Func.to fh.f) u₀
          eq-UF = begin
            unfoldingCore (out a)
              ≡⟨ cong unfoldingCore (cong out a≡fx) ⟩
            unfoldingCore (out (Func.to fh.f x))
              ≡⟨ sym (cong unfoldingCore (fh.commute x)) ⟩
            mapUnfolding (Func.to fh.f) u₀
            ∎

          eq-UG : unfoldingCore (out b) ≡ mapUnfolding (ana-to X) u₀
          eq-UG = begin
            unfoldingCore (out b)
              ≡⟨ cong unfoldingCore (cong out b≡anax) ⟩
            unfoldingCore (out (ana-to X x))
              ≡⟨ refl ⟩
            mapUnfolding (ana-to X) u₀
            ∎

          unfoldFunctor₀-eq-lem : ∀ {A} (s : ShapeOf FC A)
                                → Functor.₀ (unfoldFunctor (unfoldingCore (out a))) (A , s)
                                  ≡ Functor.₀ (unfoldFunctor (unfoldingCore (out b))) (A , s)
          unfoldFunctor₀-eq-lem {A} s =
            trans
              (cong (λ u → Functor.₀ (unfoldFunctor u) (A , s)) eq-UF)
              (sym (cong (λ u → Functor.₀ (unfoldFunctor u) (A , s)) eq-UG))

          pos-to-shape-eq-lem : ∀ {A} (s : ShapeOf FC A) (p : PosOf FC s)
                              → subst (λ x → ShapeOf FC x) (unfoldFunctor₀-eq-lem s)
                                       (pos-to-shape (unfoldingCore (out a)) s p)
                                ≡ pos-to-shape (unfoldingCore (out b)) s p
          pos-to-shape-eq-lem {A} s p
            rewrite eq-UF | eq-UG = refl

          go : a ≈C b
          go .unfoldFunctor₀-eq = unfoldFunctor₀-eq-lem
          go .pos-to-shape-eq   = pos-to-shape-eq-lem
          go .unfold-next-eq {A} s =
            let seed = unfold-next u₀ s
                a'≡ = cong (λ u → unfold-next u s) eq-UF
                b'≡ = cong (λ u → unfold-next u s) eq-UG
            in helper seed a'≡ b'≡

  -- Terminality (Func morphism, ≡ commute condition)
  -- 终余代数性（Func 态射，≡ 交换条件）
  terminality : ∀ (X : Coalgebra)
              → ∃ λ (f : Func (Coalgebra.Carrier X) cosmosSetoid) →
                  (∀ x → mapCosmosF (Func.to f) (Func.to (Coalgebra.α X) x)
                         ≡ out (Func.to f x))
                × (∀ (g : Func (Coalgebra.Carrier X) cosmosSetoid)
                    → (∀ x → mapCosmosF (Func.to g) (Func.to (Coalgebra.α X) x)
                           ≡ out (Func.to g x))
                    → ∀ x → Func.to f x ≈C Func.to g x)
  terminality X =
    ( ana X
    , (λ _ → refl)
    , λ g gcomm x → ≈C-sym
        (unique-ana X (record { f = g ; commute = gcomm }) x)
    )
