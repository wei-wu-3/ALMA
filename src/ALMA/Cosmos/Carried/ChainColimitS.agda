------------------------------------------------------------------------
-- Standard colimit of an arbitrary forward ω-chain in SameIndexCatS.
--
-- A chain is a family of stage objects X m together with identity-index
-- forward arrows e m : X m ⇒ X (suc m).  Every arrow keeps the global id
-- and the deterministic dynamics d, so labels move between stages purely
-- by function passing.
--
-- The direct-limit fibre is a forward compatible family Fam: a choice at
-- every stage whose successive choices are related by the forward map in
-- the stage setoid.  Its equality is the pointwise stage setoid, so the
-- construction needs no Fin alignment, no transport, no K and no
-- function extensionality, and the stage fibres may carry arbitrary
-- setoids (not only propositional ones).  A family is determined by a
-- stage-0 seed along the deterministic forward orbit; embedding a later
-- stage element needs a root, the forward analogue of a total ray.
--
-- SameIndexCatS 中任意前向 ω-链的标准余极限。
--
-- 链由一族阶段对象 X m 与索引恒等的前向箭头 e m : X m ⇒ X (suc m)
-- 组成。每条箭头保持全局 id 与确定性动力 d，标签跨阶段纯由函数传递。
--
-- 直接极限纤维是前向相容族 Fam：在每个阶段取一个元素，相邻选择由前向
-- 映射在阶段 setoid 中相关。其相等为逐点阶段 setoid，故构造无需 Fin
-- 对齐、无传输、不用 K、不用函数外延性，且阶段纤维可带任意 setoid（不
-- 限于命题纤维）。一个族由阶段 0 的种子沿确定性前向轨道决定；嵌入更晚
-- 阶段的元素需要一个根，即全总射线的前向对偶。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.ChainColimitS where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; _≈Mˢ_)
open SysEq
open import ALMA.Cosmos.Carried.SameIndexCatS
  using (LabelSys; dsys; Idx⇒; idxi; compi; _≈i_; SameIndexCat; ≈i-refl
        ; ≈i-sym; ≈i-trans; ∘-resp-≈i; pointwise-i)

open import ALMA.Cosmos.Carried.SeqColimitCat using (Chain⇒; stop; step; ωCat; _∘ch_)
import ALMA.Cosmos.Carried.SeqColimitCat as SQC

module _ (d : ℕ → ℕ) {ℓ : Level} where

  ----------------------------------------------------------------------
  -- A forward ω-chain: stage objects and identity-index forward arrows.
  -- 前向 ω-链：阶段对象与索引恒等的前向箭头。
  record ChainS : Set (lsuc ℓ) where
    field
      X₀ : ℕ → LabelSys ℓ
      e  : (m : ℕ) → Idx⇒ d (X₀ m) (X₀ (suc m))

  module Build (C : ChainS) where

    open ChainS C

    private
      s   = d
      sYS = dsys s

    -- Stage fibres and their setoids.
    -- 阶段纤维及其 setoid。
    fibre : (m v : ℕ) → Set ℓ
    fibre m v = LabelSys.A₀ (X₀ m) v

    ≈fibre : (m v : ℕ) → EqOn (fibre m v)
    ≈fibre m v = LabelSys.≈A₀ (X₀ m) v

    -- One-step forward label map and its setoid compatibility.
    -- 一步前向标签映射及其 setoid 同余。
    fwd : (m v : ℕ) → fibre m v → fibre (suc m) v
    fwd m v = Idx⇒.shape (e m) v

    fwd-cong : (m v : ℕ) {a a' : fibre m v}
             → EqOn._≈_ (≈fibre m v) a a'
             → EqOn._≈_ (≈fibre (suc m) v) (fwd m v a) (fwd m v a')
    fwd-cong m v = Idx⇒.shape-cong (e m) {v = v}

    -- Stage reached after n forward steps from m; the zero case is m
    -- definitionally, so iteration types need no arithmetic transport.
    -- 从 m 经 n 步前向到达的阶段；零步定义性为 m，故迭代类型无需算术传输。
    iter-stage : (n m : ℕ) → ℕ
    iter-stage zero    m = m
    iter-stage (suc n) m = iter-stage n (suc m)

    -- n-step forward iteration, from stage m to iter-stage n m.
    -- n 步前向迭代，从阶段 m 到 iter-stage n m。
    fwd^ : (n m v : ℕ) → fibre m v → fibre (iter-stage n m) v
    fwd^ zero    m v a = a
    fwd^ (suc n) m v a = fwd^ n (suc m) v (fwd m v a)

    -- Iteration respects the stage setoid at every step.
    -- 迭代在每一步保持阶段 setoid。
    fwd^-cong : (n m v : ℕ) {a a' : fibre m v}
              → EqOn._≈_ (≈fibre m v) a a'
              → EqOn._≈_ (≈fibre (iter-stage n m) v)
                          (fwd^ n m v a) (fwd^ n m v a')
    fwd^-cong zero    m v eq = eq
    fwd^-cong (suc n) m v eq =
      fwd^-cong n (suc m) v (fwd-cong m v eq)

    --------------------------------------------------------------------
    -- Direct-limit element as a forward compatible family: a choice at
    -- every stage with successive choices related by fwd.
    -- 直接极限元素作为前向相容族：每阶段一个选择，相邻选择由 fwd 相关。
    record Fam (v : ℕ) : Set ℓ where
      coinductive
      field
        at  : (m : ℕ) → fibre m v
        coh : (m : ℕ)
            → EqOn._≈_ (≈fibre (suc m) v) (fwd m v (at m)) (at (suc m))
    open Fam public

    -- Pointwise stage setoid on families; equality is data at every
    -- stage, so no function extensionality is required.
    -- 族上的逐点阶段 setoid；相等是每阶段的数据，无需函数外延性。
    _≈Fam_ : {v : ℕ} → Fam v → Fam v → Set ℓ
    _≈Fam_ {v} τ υ =
      (m : ℕ) → EqOn._≈_ (≈fibre m v) (at τ m) (at υ m)

    -- Pointwise lifting of the stage setoid; the element is named
    -- explicitly so the coinductive projection at τ m does not block
    -- inference.
    -- 阶段 setoid 的逐点提升；元素显式命名，以免共归纳投影 at τ m 阻塞推断。
    private
      refl-at : (v m : ℕ) (τ : Fam v)
              → EqOn._≈_ (≈fibre m v) (at τ m) (at τ m)
      refl-at v m τ = EqOn.refl (≈fibre m v)

      sym-at : (v m : ℕ) (τ υ : Fam v)
             → EqOn._≈_ (≈fibre m v) (at τ m) (at υ m)
             → EqOn._≈_ (≈fibre m v) (at υ m) (at τ m)
      sym-at v m τ υ h = EqOn.sym (≈fibre m v) h

      trans-at : (v m : ℕ) (τ υ ω : Fam v)
               → EqOn._≈_ (≈fibre m v) (at τ m) (at υ m)
               → EqOn._≈_ (≈fibre m v) (at υ m) (at ω m)
               → EqOn._≈_ (≈fibre m v) (at τ m) (at ω m)
      trans-at v m τ υ ω h₁ h₂ = EqOn.trans (≈fibre m v) h₁ h₂

    ≈Fam : (v : ℕ) → EqOn (Fam v)
    ≈Fam v = record
      { _≈_           = _≈Fam_
      ; isEquivalence = record
        { refl  = λ {x} m → refl-at v m x
        ; sym   = λ {x y} h m → sym-at v m x y (h m)
        ; trans = λ {x y z} h₁ h₂ m →
                    trans-at v m x y z (h₁ m) (h₂ m)
        }
      }

    -- Forward orbit of a stage-0 seed, indexed by the target stage; the
    -- recursion is on the target stage, so no stage arithmetic appears in
    -- the types.
    -- 阶段 0 种子的前向轨道，按目标阶段索引；递归作用于目标阶段，类型中
    -- 因而不出现阶段算术。
    orbit0 : (m v : ℕ) → fibre 0 v → fibre m v
    orbit0 zero    v a = a
    orbit0 (suc m) v a = fwd m v (orbit0 m v a)

    -- The forward orbit of a stage-0 seed is a compatible family; the
    -- coherence holds definitionally.
    -- 阶段 0 种子的前向轨道是相容族；相干定义性成立。
    fam-of : (v : ℕ) → fibre 0 v → Fam v
    fam-of v a .at m    = orbit0 m v a
    fam-of v a .coh m   = EqOn.refl (≈fibre (suc m) v)

    -- orbit0 respects the stage setoid.
    -- orbit0 保持阶段 setoid。
    orbit0-cong : (m v : ℕ) {a a' : fibre 0 v}
                → EqOn._≈_ (≈fibre 0 v) a a'
                → EqOn._≈_ (≈fibre m v) (orbit0 m v a) (orbit0 m v a')
    orbit0-cong zero    v eq = eq
    orbit0-cong (suc m) v eq = fwd-cong m v (orbit0-cong m v eq)

    --------------------------------------------------------------------
    -- The chain as a functor ω → SameIndexCat.  Paths are folded into
    -- composites of the forward arrows; no hypothesis on the fibres is
    -- needed at this stage.
    -- 链作为 ω → SameIndexCat 函子。路径折叠为前向箭头的复合；此阶段不
    -- 对纤维作任何假设。
    private
      cat : Category (lsuc ℓ) ℓ ℓ
      cat = SameIndexCat s {ℓ = ℓ}

      reflc : {X Y : LabelSys ℓ} {f : Idx⇒ s X Y} → _≈i_ s f f
      reflc {f = f} = ≈i-refl s {ℓ = ℓ} f

      symc : {X Y : LabelSys ℓ} {f g : Idx⇒ s X Y}
           → _≈i_ s f g → _≈i_ s g f
      symc {f = f} {g = g} p = ≈i-sym s {ℓ = ℓ} {f = f} {g = g} p

      transc : {X Y : LabelSys ℓ} {f g h : Idx⇒ s X Y}
             → _≈i_ s f g → _≈i_ s g h → _≈i_ s f h
      transc {f = f} {g = g} {h = h} p q =
        ≈i-trans s {ℓ = ℓ} {f = f} {g = g} {h = h} p q

      respc : {X Y Z : LabelSys ℓ}
                {F₁ F₂ : Idx⇒ s X Y} {G₁ G₂ : Idx⇒ s Y Z}
            → _≈i_ s F₁ F₂ → _≈i_ s G₁ G₂
            → _≈i_ s (compi s G₁ F₁) (compi s G₂ F₂)
      respc {X = X} {Y = Y} {Z = Z}
            {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q =
        ∘-resp-≈i s {ℓ = ℓ} {X = X} {Y = Y} {Z = Z}
                    {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q

    fold-emb : ∀ {m n : ℕ} → Chain⇒ m n
             → Idx⇒ s (X₀ m) (X₀ n)
    fold-emb SQC.stop            = idxi s (X₀ _)
    fold-emb (SQC.step {n = n} p) = compi s (e n) (fold-emb p)

    fold-hom : ∀ {m y n : ℕ} (g : Chain⇒ y n) (f : Chain⇒ m y)
             → _≈i_ s (fold-emb (g ∘ch f))
                       (compi s (fold-emb g) (fold-emb f))
    fold-hom {m} {y} {.y} SQC.stop f =
      symc {X = X₀ m} {Y = X₀ y}
           {f = compi s (idxi s (X₀ y)) (fold-emb f)}
           {g = fold-emb f}
           (reflc {f = compi s (idxi s (X₀ y)) (fold-emb f)})
    fold-hom {m} {y} {.(suc t)} (SQC.step {n = t} g) f =
      transc {X = X₀ m} {Y = X₀ (suc t)}
        {f = compi s (e t) (fold-emb (g ∘ch f))}
        {g = compi s (e t) (compi s (fold-emb g) (fold-emb f))}
        {h = compi s (compi s (e t) (fold-emb g)) (fold-emb f)}
        (respc {X = X₀ m} {Y = X₀ t} {Z = X₀ (suc t)}
           {F₁ = fold-emb (g ∘ch f)}
           {F₂ = compi s (fold-emb g) (fold-emb f)}
           {G₁ = e t} {G₂ = e t}
           (fold-hom g f) (reflc {f = e t}))
        (reflc {f = compi s (e t)
                  (compi s (fold-emb g) (fold-emb f))})

    fold-resp-i : ∀ {m n : ℕ} {p q : Chain⇒ m n}
                → p ≡ q → _≈i_ s (fold-emb p) (fold-emb q)
    fold-resp-i {p = p} refl = reflc {f = fold-emb p}

    chainFun : Functor ωCat cat
    chainFun = record
      { F₀          = X₀
      ; F₁          = fold-emb
      ; identity    = λ {m} → reflc {f = fold-emb {m = m} SQC.stop}
      ; homomorphism = λ {m y n f g} → fold-hom g f
      ; F-resp-≈    = λ {m n p q} eq → fold-resp-i {p = p} {q = q} eq
      }

    --------------------------------------------------------------------
    -- Colimit apex: the label system of compatible families, with its
    -- pointwise setoid.
    -- 余极限顶点：相容族构成的标签系统，带逐点 setoid。
    apexLS : LabelSys ℓ
    apexLS = record { A₀ = Fam ; ≈A₀ = ≈Fam }

    -- A family's stage-n choice equals the forward orbit of its stage-0
    -- choice, by iterating the coherence.
    -- 族的阶段 n 选择等于其阶段 0 选择的前向轨道（逐次使用相干）。
    fam-orbit : (n v : ℕ) (τ : Fam v)
              → EqOn._≈_ (≈fibre n v) (orbit0 n v (at τ 0)) (at τ n)
    fam-orbit zero    v τ = EqOn.refl (≈fibre 0 v)
    fam-orbit (suc n) v τ =
      EqOn.trans (≈fibre (suc n) v)
        (fwd-cong n v (fam-orbit n v τ))
        (coh τ n)

    -- Canonical leg: project a family to its stage-m choice.
    -- 规范腿：把族投影到其阶段 m 选择。
    legIdx : (m : ℕ) → Idx⇒ s apexLS (X₀ m)
    legIdx m = record
      { shape      = λ v τ → at τ m
      ; shape-cong = λ eq → eq m
      }

    -- One-step cocone coherence: e m after leg m is leg (suc m).
    -- 一步余锥相干：e m 接 leg m 等于 leg (suc m)。
    leg-coh : (m : ℕ)
            → _≈i_ s (compi s (e m) (legIdx m)) (legIdx (suc m))
    leg-coh m =
      pointwise-i s {ℓ = ℓ} {X = apexLS} {Y = X₀ (suc m)}
        (compi s (e m) (legIdx m)) (legIdx (suc m))
        (λ v τ → coh τ m)

    -- Path-level cocone coherence: fold p after leg m is leg n.
    -- 路径级余锥相干：fold p 接 leg m 等于 leg n。
    legPath : {m n : ℕ} (p : Chain⇒ m n)
            → _≈i_ s (compi s (fold-emb p) (legIdx m)) (legIdx n)
    legPath SQC.stop =
      reflc {X = apexLS} {Y = X₀ _}
            {f = compi s (idxi s (X₀ _)) (legIdx _)}
    legPath (SQC.step {n = k} p) =
      transc {X = apexLS} {Y = X₀ (suc k)}
        {f = compi s (compi s (e k) (fold-emb p)) (legIdx _)}
        {g = compi s (e k) (compi s (fold-emb p) (legIdx _))}
        {h = legIdx (suc k)}
        (reflc {f = compi s (compi s (e k) (fold-emb p)) (legIdx _)})
        (transc {X = apexLS} {Y = X₀ (suc k)}
          {f = compi s (e k) (compi s (fold-emb p) (legIdx _))}
          {g = compi s (e k) (legIdx k)}
          {h = legIdx (suc k)}
          (respc {X = apexLS} {Y = X₀ k} {Z = X₀ (suc k)}
                 {F₁ = compi s (fold-emb p) (legIdx _)}
                 {F₂ = legIdx k}
                 {G₁ = e k} {G₂ = e k}
                 (legPath p) (reflc {f = e k}))
          (leg-coh k))

    open import Categories.Diagram.Cone chainFun

    -- Compatible families form the canonical cone over the forward chain
    -- (projections apex → stage, commuting with e): a born-at-0 family is
    -- determined by projecting to every stage.  The colimit cocone with
    -- stage → apex injections is a separate construction and needs a root
    -- for every later-stage element (stage isomorphisms).
    -- 相容族构成前向链的规范锥（顶点 → 阶段的投影，与 e 交换）：诞生于 0
    -- 的族由到各阶段的投影确定。带“阶段 → 顶点”注入的余极限余锥是另一构
    -- 造，需要每个晚诞生元素的根（阶段同构）。
    famCone : Cone
    famCone = record
      { apex = record { ψ = legIdx ; commute = λ {m n} p → legPath p } }

    --------------------------------------------------------------------
    -- Colimit branch.  Stage → apex injections exist when every forward
    -- arrow is a setoid isomorphism: a backward map r m with both
    -- round-trip laws gives every later-stage element a canonical root at
    -- stage 0, so its forward orbit recovers the element (no transport).
    --
    -- 余极限支。当每条前向箭头是 setoid 同构时存在“阶段 → 顶点”注入：
    -- 双向收缩 r m 的两条往返律给每个晚诞生元素一个规范的阶段 0 根，其前向
    -- 轨道恢复该元素（无传输）。
    module BuildIso
      (r     : (m : ℕ) → Idx⇒ s (X₀ (suc m)) (X₀ m))
      (res-emb : (m v : ℕ) (a : fibre m v)
               → EqOn._≈_ (≈fibre m v)
                           (Idx⇒.shape (r m) v (fwd m v a)) a)
      (emb-res : (m v : ℕ) (b : fibre (suc m) v)
               → EqOn._≈_ (≈fibre (suc m) v)
                           (fwd m v (Idx⇒.shape (r m) v b)) b)
      where

      back : (m v : ℕ) → fibre (suc m) v → fibre m v
      back m v = Idx⇒.shape (r m) v

      back-cong : (m v : ℕ) {b b' : fibre (suc m) v}
                → EqOn._≈_ (≈fibre (suc m) v) b b'
                → EqOn._≈_ (≈fibre m v) (back m v b) (back m v b')
      back-cong m v = Idx⇒.shape-cong (r m) {v = v}

      -- Canonical stage-0 root of a stage-m element.
      -- 阶段 m 元素的规范阶段 0 根。
      root : (m v : ℕ) → fibre m v → fibre 0 v
      root zero    v a = a
      root (suc m) v a = root m v (back m v a)

      root-cong : (m v : ℕ) {a a' : fibre m v}
                → EqOn._≈_ (≈fibre m v) a a'
                → EqOn._≈_ (≈fibre 0 v) (root m v a) (root m v a')
      root-cong zero    v eq = eq
      root-cong (suc m) v eq = root-cong m v (back-cong m v eq)

      -- Forward orbit of the root recovers the element (e ∘ r round trip).
      -- 根的前向轨道恢复该元素（e ∘ r 往返）。
      fwd-root : (m v : ℕ) (a : fibre m v)
               → EqOn._≈_ (≈fibre m v) (orbit0 m v (root m v a)) a
      fwd-root zero    v a = EqOn.refl (≈fibre 0 v)
      fwd-root (suc m) v a =
        EqOn.trans (≈fibre (suc m) v)
          (fwd-cong m v (fwd-root m v (back m v a)))
          (emb-res m v a)

      -- Injection: take the root and follow its forward orbit.
      -- 注入：取根并沿其前向轨道。
      inj : (m : ℕ) → Idx⇒ s (X₀ m) apexLS
      inj m = record
        { shape      = λ v a → fam-of v (root m v a)
        ; shape-cong = λ {v = v} {a} {a'} eq k →
                         orbit0-cong k v (root-cong m v eq)
        }

      -- One-step cocone coherence: inj (suc m) ∘ e m ≈ inj m.
      -- 一步余锥相干：inj (suc m) ∘ e m ≈ inj m。
      inj-coh : (m : ℕ)
              → _≈i_ s (compi s (inj (suc m)) (e m)) (inj m)
      inj-coh m =
        pointwise-i s {ℓ = ℓ} {X = X₀ m} {Y = apexLS}
          (compi s (inj (suc m)) (e m)) (inj m)
          (λ v a k →
             orbit0-cong k v
               (root-cong m v (res-emb m v a)))

      -- Path-level cocone coherence: inj n ∘ fold p ≈ inj m.
      -- 路径级余锥相干：inj n ∘ fold p ≈ inj m。
      injPath : {m n : ℕ} (p : Chain⇒ m n)
              → _≈i_ s (compi s (inj n) (fold-emb p)) (inj m)
      injPath SQC.stop =
        reflc {X = X₀ _} {Y = apexLS}
              {f = compi s (inj _) (idxi s (X₀ _))}
      injPath (SQC.step {n = k} p) =
        transc {X = X₀ _} {Y = apexLS}
          {f = compi s (inj (suc k))
                  (compi s (e k) (fold-emb p))}
          {g = compi s (inj k) (fold-emb p)}
          {h = inj _}
          (transc {X = X₀ _} {Y = apexLS}
            {f = compi s (inj (suc k))
                    (compi s (e k) (fold-emb p))}
            {g = compi s (compi s (inj (suc k)) (e k)) (fold-emb p)}
            {h = compi s (inj k) (fold-emb p)}
            (reflc {f = compi s (inj (suc k))
                      (compi s (e k) (fold-emb p))})
            (respc {X = X₀ _} {Y = X₀ k} {Z = apexLS}
                   {F₁ = fold-emb p} {F₂ = fold-emb p}
                   {G₁ = compi s (inj (suc k)) (e k)}
                   {G₂ = inj k}
                   (reflc {f = fold-emb p}) (inj-coh k)))
          (injPath p)

      open import Categories.Diagram.Cocone chainFun

      -- The canonical colimit cocone under the isomorphism hypothesis.
      -- 同构假设下的规范余极限余锥。
      nColimCocone : Cocone
      nColimCocone = record
        { coapex = record { ψ = inj ; commute = λ {m n} p → injPath p } }

      ------------------------------------------------------------------
      -- Pointwise cocones and the mediating functor.  A competing
      -- cocone is a coapex Z with legs ψ m : X m ⇒ Z and one-step
      -- coherence ψ (suc m) (e m a) ≈ ψ m a, all in the fibre setoids.
      -- The mediator reads the stage-0 value; uniqueness is pointwise,
      -- so neither function extensionality nor transport is used.
      --
      -- 逐点余锥与 mediate 函子。竞争余锥由余顶点 Z、腿 ψ m : X m ⇒ Z
      -- 与一步相干 ψ (suc m)(e m a) ≈ ψ m a 组成，均在纤维 setoid 中。
      -- mediate 读取阶段 0 的值；唯一性为逐点，故不用函数外延性与传输。
      record PFCocone (Z : LabelSys ℓ) : Set (lsuc ℓ) where
        field
          ψc  : (m : ℕ) → Idx⇒ s (X₀ m) Z
          coh : (m v : ℕ) (a : fibre m v)
              → EqOn._≈_ (LabelSys.≈A₀ Z v)
                          (Idx⇒.shape (ψc (suc m)) v (fwd m v a))
                          (Idx⇒.shape (ψc m) v a)
      open PFCocone

      -- ψ m applied to the forward orbit of a stage-0 seed is ψ 0.
      -- ψ m 作用于阶段 0 种子的前向轨道等于 ψ 0。
      k-fwd : {Z : LabelSys ℓ} (K : PFCocone Z)
              (m v : ℕ) (x : fibre 0 v)
            → EqOn._≈_ (LabelSys.≈A₀ Z v)
                        (Idx⇒.shape (ψc K m) v (orbit0 m v x))
                        (Idx⇒.shape (ψc K 0) v x)
      k-fwd {Z = Z} K zero    v x = EqOn.refl (LabelSys.≈A₀ Z v)
      k-fwd {Z = Z} K (suc m) v x =
        EqOn.trans (LabelSys.≈A₀ Z v)
          (coh K m v (orbit0 m v x))
          (k-fwd K m v x)

      -- The mediator: project the family to stage 0 and apply ψ 0.
      -- mediate：把族投影到阶段 0 再作用 ψ 0。
      mediate : {Z : LabelSys ℓ} (K : PFCocone Z)
              → Idx⇒ s apexLS Z
      mediate K = record
        { shape      = λ v τ → Idx⇒.shape (ψc K 0) v (at τ 0)
        ; shape-cong = λ eq → Idx⇒.shape-cong (ψc K 0) (eq 0)
        }

      -- Factorisation: mediate ∘ inj m ≈h ψ m.
      -- 因子分解：mediate ∘ inj m 逐点等于 ψ m。
      triangle : {Z : LabelSys ℓ} (K : PFCocone Z) (m v : ℕ)
                   (a : fibre m v)
               → EqOn._≈_ (LabelSys.≈A₀ Z v)
                           (Idx⇒.shape (ψc K 0) v (root m v a))
                           (Idx⇒.shape (ψc K m) v a)
      triangle {Z = Z} K m v a =
        EqOn.trans (LabelSys.≈A₀ Z v)
          (EqOn.sym (LabelSys.≈A₀ Z v) (k-fwd K m v (root m v a)))
          (Idx⇒.shape-cong (ψc K m) (fwd-root m v a))

      -- Any other factorising mediator is pointwise equal to mediate.
      -- 任何其他可因子分解的 mediate 与本 mediate 逐点相等。
      unique : {Z : LabelSys ℓ} (h : Idx⇒ s apexLS Z) (K : PFCocone Z)
             → ((m v : ℕ) (a : fibre m v)
                → EqOn._≈_ (LabelSys.≈A₀ Z v)
                            (Idx⇒.shape h v (fam-of v (root m v a)))
                            (Idx⇒.shape (ψc K m) v a))
             → (v : ℕ) (τ : Fam v)
             → EqOn._≈_ (LabelSys.≈A₀ Z v)
                         (Idx⇒.shape h v τ)
                         (Idx⇒.shape (ψc K 0) v (at τ 0))
      unique {Z = Z} h K ht v τ =
        EqOn.trans (LabelSys.≈A₀ Z v)
          (EqOn.sym (LabelSys.≈A₀ Z v)
             (Idx⇒.shape-cong h (λ m → fam-orbit m v τ)))
          (ht 0 v (at τ 0))

      ------------------------------------------------------------------
      -- Standard colimit, conditionally.  A bisimulation cocone whose
      -- every stage object carries a total label-tree at each label,
      -- rooted at that label in the stage setoid, admits a unique
      -- Cocone⇒ out of the canonical colimit cocone.  The tree is used
      -- only to read the pointwise head coherence off the bisimulation
      -- commute; factorisation and uniqueness then lift by pointwise-i.
      --
      -- 条件性标准余极限。若余锥的每个阶段对象在每个标签处带一棵以该标签
      -- 为根（阶段 setoid 中）的全总标签树，则存在从规范余极限余锥出发的
      -- 唯一 Cocone⇒。树仅用于从双模拟 commute 读出逐点头部相干；因子分解
      -- 与唯一性随后由 pointwise-i 提升。
      module StandardColimit where

        private
          succ-arrow : ∀ {m} → Chain⇒ m (suc m)
          succ-arrow = SQC.step SQC.stop

        module _ (K : Cocone)
                 (tree : (m v : ℕ) (a : fibre m v)
                       → M (A (sYS (X₀ m))) (E (sYS (X₀ m))) v)
                 (tree-here : (m v : ℕ) (a : fibre m v)
                            → EqOn._≈_ (≈fibre m v)
                                        (M.here (tree m v a)) a)
          where

          private
            Zk  = Cocone.N K
            ψk  = Cocone.ψ K

            -- Move a head equation from the tree root M.here to the
            -- prescribed label a, in the coapex setoid, using the two
            -- morphisms' congruence and the root setoid equation.
            -- 利用两个态射的同余与根 setoid 等式，把头部等式从树根
            -- M.here 搬到余顶点 setoid 中的指定标签 a。
            relocate : (m v : ℕ)
                       (F G : Idx⇒ s (X₀ m) Zk)
                       (a : fibre m v)
                     → EqOn._≈_ (LabelSys.≈A₀ Zk v)
                                 (Idx⇒.shape F v (M.here (tree m v a)))
                                 (Idx⇒.shape G v (M.here (tree m v a)))
                     → EqOn._≈_ (LabelSys.≈A₀ Zk v)
                                 (Idx⇒.shape F v a)
                                 (Idx⇒.shape G v a)
            relocate m v F G a h0 =
              EqOn.trans (LabelSys.≈A₀ Zk v)
                (EqOn.sym (LabelSys.≈A₀ Zk v)
                   (Idx⇒.shape-cong F (tree-here m v a)))
                (EqOn.trans (LabelSys.≈A₀ Zk v)
                   h0
                   (Idx⇒.shape-cong G (tree-here m v a)))

            -- Read the forward cocone coherence as a head equation.
            -- 将前向余锥相干读为头部等式。
            kcoh : (m v : ℕ) (a : fibre m v)
                 → EqOn._≈_ (LabelSys.≈A₀ Zk v)
                     (Idx⇒.shape (ψk (suc m)) v (fwd m v a))
                     (Idx⇒.shape (ψk m) v a)
            kcoh m v a =
              relocate m v
                (compi s (ψk (suc m)) (e m)) (ψk m) a
                (_≈Mˢ_.here-eq
                  (Cocone.commute K {X = m} {Y = suc m} succ-arrow
                                v (tree m v a)))

            Kpf : PFCocone Zk
            Kpf = record { ψc = ψk ; coh = kcoh }

          -- The unique mediator and its cocone factorisation.
          -- 唯一 mediate 及其余锥因子分解。
          mediate-i : Idx⇒ s apexLS Zk
          mediate-i = mediate Kpf

          !K : Cocone⇒ nColimCocone K
          !K = record
            { arr     = mediate-i
            ; commute = λ {m} →
                          pointwise-i s
                            (compi s mediate-i (inj m)) (ψk m)
                            (triangle Kpf m)
            }

          -- Any other mediator is bisimulation-equal to mediate-i.
          -- 任何其他 mediate 与 mediate-i 互模拟相等。
          !K-unique : (h : Cocone⇒ nColimCocone K)
                    → _≈i_ s (Cocone⇒.arr h) mediate-i
          !K-unique h =
            pointwise-i s (Cocone⇒.arr h) mediate-i
              (unique (Cocone⇒.arr h) Kpf
                (λ m v a →
                  relocate m v
                    (compi s (Cocone⇒.arr h) (inj m)) (ψk m) a
                    (_≈Mˢ_.here-eq
                      (Cocone⇒.commute h {X = m} v (tree m v a)))))
