------------------------------------------------------------------------
-- Nontrivial-fibre Fin push tower, kernel.
-- The trivial-fibre tower (LimitSystemS / FinPushColimitS) uses
-- TrivDetˢ, whose label fibre is ⊤. Here the deterministic Fin position
-- dynamics is kept (positions extended by inject₁, one deterministic
-- child per node) but labels are indexed by the STABLE GLOBAL ID ℕ, not
-- by the dependent Fin position. A stage-m label at position x is
-- L m (toℕ x); the forward label map l-emb m v stays at the same global
-- id v, so its type mentions no Fin. The apex label Thread v is a
-- stage-tagged element of L _ v; forward iteration changes only the
-- stage, never a Fin index. Consequently labels cross stages purely by
-- function passing: no Fin alignment, no transport, no K, no retraction.
--
-- 非平凡纤维 Fin push 塔内核。
-- 平凡纤维塔（LimitSystemS / FinPushColimitS）采用 TrivDetˢ，标签纤维为
-- ⊤。此处保留确定性 Fin 位置动力（位置经 inject₁ 扩张，每节点一个确定
-- 性子节点），但标签按稳定全局 id ℕ 索引，而非依赖的 Fin 位置。阶段 m
-- 位置 x 处的标签为 L m (toℕ x)；前向标签映射 l-emb m v 停留在同一全局
-- id v，故其类型不涉及 Fin。顶点标签 Thread v 是 L _ v 的阶段标签化元素；
-- 前向迭代只改阶段，不改 Fin 索引。因此标签跨阶段纯由函数传递：无 Fin
-- 对齐、无传输、不用 K、无需收缩。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.NontrivialPushTowerS where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin.Base using (Fin; zero; suc; inject₁; toℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid
  using (SysEq; EqOn; propEqOn; _≈Mˢ_; idAdjˢ)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)
open import ALMA.Base.MCorrSetoidCat
  using (FMapˢ; FMˢ; compFMˢ; _≈FM_)
open import ALMA.Cosmos.Carried.SeqColimitS
  using (Chainˢ; Coconeˢ; Limitˢ)
open import ALMA.Cosmos.Carried.LimitSystemS using (n-at)
import ALMA.Cosmos.Carried.LimitSystemS as LS

open SysEq

------------------------------------------------------------------------
-- One-position extension with definitional toℕ preservation.
--
-- stdlib's inject₁ is defined via inject≥, so toℕ (inject₁ x) is only
-- propositionally toℕ x. The stage embedding below recurses directly on
-- Fin, giving toℕ (up x) = toℕ x definitionally; labels indexed by global
-- id then align across stages with no index transport. up is
-- propositionally inject₁.
--
-- 保持 toℕ 定义性不变的单位置扩张。
-- 标准库 inject₁ 经 inject≥ 定义，toℕ (inject₁ x) 仅命题性等于 toℕ x。
-- 下面的阶段嵌入直接对 Fin 递归，使 toℕ (up x) 定义性等于 toℕ x；按全局
-- id 索引的标签因而跨阶段对齐，无需索引传输。up 命题性等于 inject₁。

up : ∀ {n} → Fin n → Fin (suc n)
up zero    = zero
up (suc i) = suc (up i)

up-toℕ : ∀ {n} (x : Fin n) → toℕ (up x) ≡ toℕ x
up-toℕ zero    = refl
up-toℕ (suc x) = cong suc (up-toℕ x)

up-inject₁ : ∀ {n} (x : Fin n) → up x ≡ inject₁ x
up-inject₁ zero    = refl
up-inject₁ (suc x) = cong suc (up-inject₁ x)

------------------------------------------------------------------------
-- A deterministic Fin tower with labels indexed by global id.
--
-- t is the deterministic position transition; embed-compat is its
-- compatibility with the one-position extension inject₁. L m v is the
-- label at global id v as present at stage m (total over v; labels at
-- not-yet-born positions are free). l-emb carries a label at global id v
-- from stage m to stage m+1 at the SAME v.
--
-- 标签按全局 id 索引的确定性 Fin 塔。
-- t 为确定性位置转移；embed-compat 是其与单位置扩张 inject₁ 的相容性。
-- L m v 是全局 id v 在阶段 m 的标签（对 v 全；未诞生位置的标签自由）。
-- l-emb 把全局 id v 的标签从阶段 m 携带到阶段 m+1，v 不变。

record LabeledFinTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    t        : (m : ℕ) → Fin (n-at m) → Fin (n-at m)
    L        : (m : ℕ) → ℕ → Set ℓ
    l-emb    : (m v : ℕ) → L m v → L (suc m) v
    embed-compat :
      (m : ℕ) (x : Fin (n-at m))
      → t (suc m) (inject₁ x) ≡ inject₁ (t m x)

module Tower {ℓ : Level} (T : LabeledFinTower ℓ) where

  open LabeledFinTower T
  open LS.LimitSystemS t embed-compat using (s∞; read-coh)

  ----------------------------------------------------------------------
  -- Stage systems. Labels are pulled from the global-id family via toℕ;
  -- the edge fibre is the singleton proof y ≡ t m x (one child).
  -- 阶段系统。标签经 toℕ 取自全局 id 族；边纤维为单点证明 y ≡ t m x
  -- （唯一子节点）。

  LStage : (m : ℕ) → SysEq lzero ℓ lzero ℓ lzero
  LStage m = record
    { I  = Fin (n-at m)
    ; A  = λ x → L m (toℕ x)
    ; E  = λ x _ y → Σ (⊤ {lzero}) λ _ → y ≡ t m x
    ; ≈A = λ x → propEqOn (L m (toℕ x))
    ; ≈E = λ x _ y → propEqOn (Σ (⊤ {lzero}) λ _ → y ≡ t m x)
    }

  -- Deterministic orbit under a global labelling (lab by global id).
  -- 全局标签族（按全局 id）下的确定性轨道。
  orbit : (m : ℕ) (x : Fin (n-at m)) (lab : ∀ v → L m v)
        → M (A (LStage m)) (E (LStage m)) x
  orbit m x lab .M.here      = lab (toℕ x)
  orbit m x lab .M.below y _ = orbit m y lab

  ----------------------------------------------------------------------
  -- One-step index embedding and the graph label correspondence.
  -- 一步索引嵌入与图标签对应。

  -- Compatibility of t with up, derived from embed-compat for inject₁.
  -- t 与 up 的相容性，由 inject₁ 的 embed-compat 导出。
  up-compat : (m : ℕ) (x : Fin (n-at m))
            → t (suc m) (up x) ≡ up (t m x)
  up-compat m x =
    trans (cong (t (suc m)) (up-inject₁ x))
    (trans (embed-compat m x) (sym (up-inject₁ (t m x))))

  R-emb : (m : ℕ) → Fin (n-at m) → Fin (n-at (suc m)) → Set lzero
  R-emb m x y = up x ≡ y

  -- At y = up x the two positions share global id toℕ x definitionally,
  -- so the label correspondence is the graph of l-emb m (toℕ x): no Fin
  -- in its type, no transport.
  -- 在 y = up x 处两位置定义性共享全局 id toℕ x，故标签对应即
  -- l-emb m (toℕ x) 的图：类型中无 Fin，无传输。
  H-emb : (m : ℕ) (x : Fin (n-at m)) (y : Fin (n-at (suc m)))
        → R-emb m x y
        → A (LStage m) x → A (LStage (suc m)) y → Set ℓ
  H-emb m x .(up x) refl a b rewrite up-toℕ x =
    l-emb m (toℕ x) a ≡ b

  -- The embedding as a forward simulation. lab₁ is the next-stage
  -- global labelling, coherent with lab under l-emb.
  -- 嵌入作为前向模拟。lab₁ 是下一阶段全局标签族，与 lab 经 l-emb 相干。
  emb-sim : (m : ℕ) (lab : ∀ v → L m v) (lab₁ : ∀ v → L (suc m) v)
          → (coh : ∀ v → l-emb m v (lab v) ≡ lab₁ v)
          → (x : Fin (n-at m))
          → PushSimˢ (LStage m) (LStage (suc m)) (R-emb m) (H-emb m)
                      refl (orbit m x lab) (orbit (suc m) (up x) lab₁)
  emb-sim m lab lab₁ coh x .PushSimˢ.here-eq rewrite up-toℕ x =
    coh (toℕ x)
  emb-sim m lab lab₁ coh x .PushSimˢ.push y (_ , eq) =
    up y , ((tt , edge) , (refl , emb-sim m lab lab₁ coh y))
    where
      edge : up y ≡ t (suc m) (up x)
      edge = trans (cong up eq) (sym (up-compat m x))

  ----------------------------------------------------------------------
  -- Eventual label at global id v: a stage-tagged element of L _ v.
  -- There is no Fin position in the carrier; extend changes only the
  -- stage and applies l-emb at the fixed v.
  -- 全局 id v 处的最终标签：L _ v 的阶段标签化元素。载体内无 Fin 位置；
  -- extend 只改阶段并在固定 v 上应用 l-emb。

  record Thread (v : ℕ) : Set ℓ where
    inductive
    constructor mk
    field
      stage  : ℕ
      tlabel : L stage v
  open Thread public

  extend : ∀ {v} → Thread v → Thread v
  extend {v} (mk m a) = mk (suc m) (l-emb m v a)

  extend^ : ∀ {v} → ℕ → Thread v → Thread v
  extend^ zero    t = t
  extend^ (suc n) t = extend (extend^ n t)

  thread-at : (v : ℕ) (m : ℕ) → L m v → Thread v
  thread-at v m a = mk m a

  ----------------------------------------------------------------------
  -- Finest carried equivalence: two threads are the same ray when some
  -- forward iterates coincide as full records. Built from ℕ iteration
  -- arithmetic and cong only; labels always live in L _ v at the same v.
  -- 最细携带等价：当某前向迭代作为整条记录重合时，两线程为同一射线。
  -- 仅由 ℕ 迭代算术与 cong 构造；标签始终处于同一 v 的 L _ v 中。

  record _≈Thread_ {v : ℕ} (t u : Thread v) : Set ℓ where
    field
      dl   : ℕ
      dr   : ℕ
      same : extend^ dl t ≡ extend^ dr u
  open _≈Thread_

  extend^-comp : ∀ {v} (a b : ℕ) (t : Thread v)
               → extend^ a (extend^ b t) ≡ extend^ (a + b) t
  extend^-comp zero    b t = refl
  extend^-comp (suc a) b t = cong extend (extend^-comp a b t)

  iter-add-comm : ∀ {v} (a b : ℕ) (t : Thread v)
                → extend^ (a + b) t ≡ extend^ (b + a) t
  iter-add-comm a b t rewrite +-comm a b = refl

  ≈Thread-refl : ∀ {v} {t : Thread v} → t ≈Thread t
  ≈Thread-refl = record { dl = zero ; dr = zero ; same = refl }

  ≈Thread-sym : ∀ {v} {t u : Thread v} → t ≈Thread u → u ≈Thread t
  ≈Thread-sym p = record { dl = dr p ; dr = dl p ; same = sym (same p) }

  ≈Thread-trans : ∀ {v} {t u w : Thread v}
                → t ≈Thread u → u ≈Thread w → t ≈Thread w
  ≈Thread-trans {u = u} p q = record
    { dl = c + a
    ; dr = b + d
    ; same =
        trans (sym (extend^-comp c a _))
        (trans (cong (extend^ c) (same p))
        (trans (extend^-comp c b u)
        (trans (iter-add-comm c b u)
        (trans (sym (extend^-comp b c u))
        (trans (cong (extend^ b) (same q))
               (extend^-comp b d _))))))
    }
    where
    a = dl p ; b = dr p ; c = dl q ; d = dr q

  ≈A∞ : (v : ℕ) → EqOn {ℓ = ℓ} (Thread v)
  ≈A∞ v = record
    { _≈_ = _≈Thread_
    ; isEquivalence = record
      { refl  = ≈Thread-refl
      ; sym   = ≈Thread-sym
      ; trans = ≈Thread-trans
      }
    }

  ----------------------------------------------------------------------
  -- Apex system: ℕ index, deterministic dynamics s∞, Thread labels,
  -- singleton deterministic edges.
  -- 顶点系统：ℕ 索引、确定性动力 s∞、Thread 标签、单点确定性边。

  -- Shared singleton-edge system over the fixed dynamics s∞. Every
  -- stage and the apex differ only in the label fibre and its EqOn; the
  -- index, edge fibre and edge EqOn are definitionally shared, so an
  -- identity-index carried functor reuses the source fibre adjunction in
  -- its map congruence with no edge transport.
  -- 固定动力 s∞ 上共享单点边的系统。各阶段与顶点仅标签纤维及其 EqOn 不同；
  -- 索引、边纤维与边 EqOn 定义性共享，故索引恒等的携带函子可在其 map 同余
  -- 中直接复用源纤维伴随，无边传输。
  nsys : (A₀ : ℕ → Set ℓ) → ((v : ℕ) → EqOn {ℓ = ℓ} (A₀ v))
       → SysEq lzero ℓ lzero ℓ lzero
  nsys A₀ ≈A₀ = record
    { I  = ℕ
    ; A  = A₀
    ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ s∞ v
    ; ≈A = ≈A₀
    ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v)
    }

  L∞ : SysEq lzero ℓ lzero ℓ lzero
  L∞ = nsys Thread ≈A∞

  ----------------------------------------------------------------------
  -- ℕ-indexed stage chain on which the colimit universal property lives.
  --
  -- Every stage shares the fixed apex dynamics s∞ and differs only in its
  -- label fibre L m. The stage embedding is identity on the global id
  -- (R = propositional equality, always refl), so labels across stages
  -- share a fibre definitionally: no Fin, no toℕ, no transport. The Fin
  -- tower above is one way to PRODUCE such a chain.
  --
  -- 余极限泛性质所在的 ℕ 索引阶段链。
  -- 每个阶段共享固定顶点动力 s∞，仅标签纤维 L m 不同。阶段嵌入在全局 id
  -- 上恒等（R 为命题相等，恒取 refl），故跨阶段标签定义性共享纤维：无
  -- Fin、无 toℕ、无传输。上面的 Fin 塔是产生这种链的一种方式。

  NStage : (m : ℕ) → SysEq lzero ℓ lzero ℓ lzero
  NStage m = nsys (L m) (λ v → propEqOn (L m v))

  -- Identity-index layer relation between consecutive stages.
  -- 相邻阶段间索引恒等的层关系。
  Rn : ℕ → ℕ → Set lzero
  Rn v w = v ≡ w

  -- Label correspondence at the refl layer: the graph of l-emb at the
  -- same global id.
  -- refl 层处的标签对应：同一全局 id 上 l-emb 的图。
  Hn : (m v w : ℕ) → Rn v w → L m v → L (suc m) w → Set ℓ
  Hn m v .v refl a b = l-emb m v a ≡ b

  -- Identity-index layer relation from a stage to the apex.
  -- 阶段到顶点的索引恒等层关系。
  Rl : ℕ → ℕ → Set lzero
  Rl v w = v ≡ w

  Hl : (m v w : ℕ) → Rl v w → L m v → Thread w → Set ℓ
  Hl m v .v refl a τ = τ ≈Thread mk m a

  ----------------------------------------------------------------------
  -- Identity-index deterministic carried functor between two nsys
  -- systems. u is the identity; the canonical source child of w is w;
  -- the fibre adjunction is the identity. The edge EqOn of any two nsys
  -- systems is definitionally the same propEqOn on the singleton edge,
  -- so the map congruence reuses the source bisimulation's adjunction
  -- unchanged: no edge transport.
  -- 两个 nsys 系统间索引恒等的确定性携带函子。u 为恒等；w 的规范源子节点
  -- 即 w；纤维伴随为恒等。任意两 nsys 系统的边 EqOn 定义性同为单点边上的
  -- propEqOn，故 map 同余直接复用源互模拟的伴随：无边传输。

  idxFM : (A₀ : ℕ → Set ℓ) (≈A₀ : (v : ℕ) → EqOn {ℓ = ℓ} (A₀ v))
          (A₁ : ℕ → Set ℓ) (≈A₁ : (v : ℕ) → EqOn {ℓ = ℓ} (A₁ v))
          (sh : (v : ℕ) → A₀ v → A₁ v)
          (shc : ∀ {v : ℕ} {a a' : A₀ v}
               → EqOn._≈_ (≈A₀ v) a a'
               → EqOn._≈_ (≈A₁ v) (sh v a) (sh v a'))
          → FMˢ (nsys A₀ ≈A₀) (nsys A₁ ≈A₁)
  idxFM A₀ ≈A₀ A₁ ≈A₁ sh shc = record
    { mor        = fmor
    ; shape-cong = λ e → shc e
    ; map-cong   = go
    }
    where
    fmor : FMapˢ (nsys A₀ ≈A₀) (nsys A₁ ≈A₁)
    fmor = record
      { u      = λ v → v
      ; shape  = sh
      ; childF = λ v _ w → w , refl
      ; adjFˢ  = λ v a w → idAdjˢ (≈E (nsys A₁ ≈A₁) v (sh v a) w)
      }
    mutual
      go : ∀ {v : ℕ} {t s : M A₀ (E (nsys A₀ ≈A₀)) v}
         → _≈Mˢ_ ≈A₀ (≈E (nsys A₀ ≈A₀)) t s
         → _≈Mˢ_ ≈A₁ (≈E (nsys A₁ ≈A₁))
                  (FMapˢ.mapFˢ fmor v t) (FMapˢ.mapFˢ fmor v s)
      go p ._≈Mˢ_.here-eq = shc (_≈Mˢ_.here-eq p)
      go p ._≈Mˢ_.below-eq w =
        let adj , fs = _≈Mˢ_.below-eq p w
            fwd , bwd = fs
        in adj , ((λ e₁ → go (fwd e₁)) , (λ e₂ → go (bwd e₂)))

  -- Stage embedding FMˢ: identity index, l-emb on labels.
  -- 阶段嵌入 FMˢ：索引恒等，标签经 l-emb。
  embFM : (m : ℕ) → FMˢ (NStage m) (NStage (suc m))
  embFM m =
    idxFM (L m) (λ v → propEqOn (L m v))
          (L (suc m)) (λ v → propEqOn (L (suc m) v))
          (λ v a → l-emb m v a) (λ {v} e → cong (l-emb m v) e)

  -- A propositional label equality maps to the same-ray relation at the
  -- fixed stage.
  -- 命题性标签等式映射为固定阶段处的同一射线关系。
  leg-shc : ∀ {m v : ℕ} {a a' : L m v}
          → a ≡ a' → mk m a ≈Thread mk m a'
  leg-shc refl = ≈Thread-refl

  -- Stage-to-apex leg FMˢ: identity index, label to its stage-m thread.
  -- 阶段到顶点的腿 FMˢ：索引恒等，标签映为其阶段 m 线程。
  legFM : (m : ℕ) → FMˢ (NStage m) L∞
  legFM m =
    idxFM (L m) (λ v → propEqOn (L m v)) Thread ≈A∞
          (λ v a → mk m a) leg-shc

  -- The ℕ-indexed nontrivial-fibre chain.
  -- ℕ 索引非平凡纤维链。
  nchain : Chainˢ lzero ℓ lzero ℓ lzero
  nchain = record { X = NStage ; emb = embFM }

  -- Colimit apex existence data. The stage injection is the identity on
  -- the global id and sends a stage-m label to its stage-m thread; it is
  -- coherent definitionally. Every apex node v is represented at stage v.
  -- 余极限顶点存在性数据。阶段注入在全局 id 上恒等，把阶段 m 标签送到其
  -- 阶段 m 线程；相干性定义性成立。每个顶点节点 v 由阶段 v 代表。
  nlimit : Limitˢ nchain
  nlimit = record
    { L         = L∞
    ; inj-u     = λ _ v → v
    ; inj-shape = λ m v a → mk m a
    ; inj-coh   = λ _ _ → refl
    ; rep       = λ v → v , v , refl
    }

  ----------------------------------------------------------------------
  -- Canonical cocone. Embedding then the stage m+1 leg advances a thread
  -- by one extend over the stage m leg; the two apex labels are the same
  -- ray definitionally, and the singleton child trees agree coinductively.
  -- The equality is behavioural (_≈FM_), never a label transport.
  -- 规范余锥。先嵌入再走阶段 m+1 腿，相对阶段 m 腿只多一次 extend；两个
  -- 顶点标签定义性为同一射线，单子树余归纳一致。相等是行为相等（_≈FM_），
  -- 绝非标签传输。

  -- One extend is the same ray (zero iterations on the left, one on the
  -- right), definitionally.
  -- 一次 extend 即同一射线（左侧零次迭代、右侧一次），定义性成立。
  one-ray : ∀ (m v : ℕ) (a : L m v)
          → mk (suc m) (l-emb m v a) ≈Thread mk m a
  one-ray m v a = record { dl = zero ; dr = suc zero ; same = refl }

  mutual
    coh-go : ∀ (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
           → _≈Mˢ_ (≈A L∞) (≈E L∞)
                    (FMapˢ.mapFˢ (FMˢ.mor
                       (compFMˢ (legFM (suc m)) (embFM m))) v t)
                    (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v t)
    coh-go m v t ._≈Mˢ_.here-eq = one-ray m v (M.here t)
    coh-go m v t ._≈Mˢ_.below-eq w =
        idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
      , ( (λ e₁ → coh-go m w (M.below t w e₁))
        , (λ e₂ → coh-go˘ m w (M.below t w e₂)) )

    coh-go˘ : ∀ (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
            → _≈Mˢ_ (≈A L∞) (≈E L∞)
                     (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v t)
                     (FMapˢ.mapFˢ (FMˢ.mor
                        (compFMˢ (legFM (suc m)) (embFM m))) v t)
    coh-go˘ m v t ._≈Mˢ_.here-eq =
      EqOn.sym (≈A L∞ v) (one-ray m v (M.here t))
    coh-go˘ m v t ._≈Mˢ_.below-eq w =
        idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
      , ( (λ e₁ → coh-go˘ m w (M.below t w e₁))
        , (λ e₂ → coh-go m w (M.below t w e₂)) )

  -- One-step cocone coherence at behavioural equality.
  -- 行为相等下的一步余锥相干性。
  leg-coh-one : (m : ℕ)
              → compFMˢ (legFM (suc m)) (embFM m) ≈FM legFM m
  leg-coh-one m v = refl , coh-go m v

  -- The canonical cocone over nchain with apex L∞.
  -- 以 L∞ 为顶点、nchain 上的规范余锥。
  ncocone : Coconeˢ nchain L∞
  ncocone = record { leg = legFM ; coh = leg-coh-one }

  ----------------------------------------------------------------------
  -- Canonical legs from a coherent global labelling.
  --
  -- lab (suc m) v is the forward image of lab m v under l-emb. The apex
  -- orbit at v carries the thread born at stage v. A leg's push returns
  -- the source child's own global id toℕ y as the target index; read-coh
  -- is used only as the apex edge witness, so every recursive simulation
  -- sits at r = refl with v = toℕ of the source position and labels share
  -- a fibre. No index transport.
  -- 相干全局标签族下的规范腿。
  -- lab (suc m) v 是 lab m v 经 l-emb 的前向像。顶点轨道在 v 处携带阶段
  -- v 诞生的线程。腿的 push 把源子节点自身的全局 id toℕ y 作为目标索引
  -- 返回；read-coh 仅用作顶点边见证，故每个递归模拟都停在 r = refl、
  -- v = 源位置的 toℕ，标签共享纤维。无索引传输。

  module WithLabelling
    (lab     : (m v : ℕ) → L m v)
    (lab-coh : (m v : ℕ) → lab (suc m) v ≡ l-emb m v (lab m v))
    where

    -- Apex orbit: thread at v born at stage v.
    -- 顶点轨道：v 处阶段 v 诞生的线程。
    orbit∞ : (v : ℕ) → M (A L∞) (E L∞) v
    orbit∞ v .M.here      = mk v (lab v v)
    orbit∞ v .M.below w _ = orbit∞ w

    -- Forward iteration of a stage label lands at the coherent label.
    -- 阶段标签的前向迭代落在相干标签上。
    forward-to : (k m v : ℕ)
               → extend^ k (mk m (lab m v)) ≡ mk (k + m) (lab (k + m) v)
    forward-to zero    m v = refl
    forward-to (suc k) m v =
      trans (cong extend (forward-to k m v))
            (cong (mk (suc (k + m))) (sym (lab-coh (k + m) v)))

    -- The thread born at stage v and the stage-m label at v are the same
    -- ray: extend both to the common stage m + v.
    -- 阶段 v 诞生的线程与 v 处阶段 m 标签是同一射线：二者都前向到共同
    -- 阶段 m + v。
    leg-here : (m v : ℕ) → mk v (lab v v) ≈Thread mk m (lab m v)
    leg-here m v = record { dl = m ; dr = v ; same = goal }
      where
        mk-eq : mk (m + v) (lab (m + v) v) ≡ mk (v + m) (lab (v + m) v)
        mk-eq rewrite +-comm m v = refl
        goal : extend^ m (mk v (lab v v)) ≡ extend^ v (mk m (lab m v))
        goal = trans (forward-to m v v)
                     (trans mk-eq (sym (forward-to v m v)))

    -- Layer relation: the apex node is the source global id.
    -- 层关系：顶点节点即源全局 id。
    Rₘ : (m : ℕ) → Fin (n-at m) → ℕ → Set lzero
    Rₘ m x v = toℕ x ≡ v

    -- Label correspondence at the refl layer witness: the apex thread
    -- and the stage-m label are the same ray.
    -- refl 层见证处的标签对应：顶点线程与阶段 m 标签是同一射线。
    Hₘ : (m : ℕ) (x : Fin (n-at m)) (v : ℕ) → Rₘ m x v
       → A (LStage m) x → Thread v → Set ℓ
    Hₘ m x .(toℕ x) refl a τ = τ ≈Thread mk m a

    -- The canonical leg at position x; every push stays at refl by
    -- targeting the child's own global id.
    -- 位置 x 处的规范腿；每次 push 以子节点自身全局 id 为目标，停在 refl。
    legₘ : (m : ℕ) (x : Fin (n-at m))
         → PushSimˢ (LStage m) L∞ (Rₘ m) (Hₘ m) refl
                     (orbit m x (lab m)) (orbit∞ (toℕ x))
    legₘ m x .PushSimˢ.here-eq = leg-here m (toℕ x)
    legₘ m x .PushSimˢ.push y (_ , eq) =
      toℕ y , ((tt , edge) , (refl , legₘ m y))
      where
        edge : toℕ y ≡ s∞ (toℕ x)
        edge = trans (cong toℕ eq) (read-coh m x)

    --------------------------------------------------------------------
    -- ℕ-indexed chain: deterministic orbits, the identity-index stage
    -- embedding, and the identity-index leg into the apex.
    -- ℕ 索引链：确定性轨道、索引恒等的阶段嵌入与索引恒等的顶点腿。

    norbit : (m v : ℕ) → M (A (NStage m)) (E (NStage m)) v
    norbit m v .M.here      = lab m v
    norbit m v .M.below w _ = norbit m w

    -- Stage embedding: identity index, l-emb on labels.
    -- 阶段嵌入：索引恒等，标签经 l-emb。
    n-sim : (m v : ℕ)
          → PushSimˢ (NStage m) (NStage (suc m)) Rn (Hn m) refl
                      (norbit m v) (norbit (suc m) v)
    n-sim m v .PushSimˢ.here-eq = sym (lab-coh m v)
    n-sim m v .PushSimˢ.push w (_ , eq) =
      w , ((tt , eq) , (refl , n-sim m w))

    -- Leg into the apex: identity index, same-ray label correspondence.
    -- 顶点腿：索引恒等，标签为同一射线对应。
    nleg : (m v : ℕ)
         → PushSimˢ (NStage m) L∞ Rl (Hl m) refl
                     (norbit m v) (orbit∞ v)
    nleg m v .PushSimˢ.here-eq = leg-here m v
    nleg m v .PushSimˢ.push w (_ , eq) =
      w , ((tt , eq) , (refl , nleg m w))

    --------------------------------------------------------------------
    -- Same-index nontrivial mediating simulation.
    --
    -- A competing cocone over the SAME index and dynamics (identity
    -- trajectory) carries an arbitrary label family ZL with its own
    -- EqOn, together with per-stage evaluation maps zm that are stable
    -- under l-emb. Every layer witness is then refl, so labels pass from
    -- a stage to the target purely by function application at a shared
    -- ℕ index: no fibre transport. The target fibre is non-trivial;
    -- uniqueness is relative to pointwise label agreement (carried
    -- data), never the automatic refl of the ⊤-fibre case.
    --
    -- 同索引非平凡 mediate 模拟。
    -- 同一索引与动力（恒等轨迹）上的竞争余锥携带任意标签族 ZL 及其
    -- EqOn，以及在 l-emb 下稳定的逐阶段求值映射 zm。所有层见证均为
    -- refl，故标签在共享 ℕ 索引上纯由函数作用传递：无纤维传输。目标
    -- 纤维非平凡；唯一性相对逐点标签一致（作为数据携带），绝非 ⊤ 纤维
    -- 情形下自动的 refl。

    module SameIndexMediate
      {z : Level}
      (ZL  : ℕ → Set z)
      (≈ZL : (v : ℕ) → EqOn {ℓ = z} (ZL v))
      (zm  : (m v : ℕ) → L m v → ZL v)
      (zm-coh : (m v : ℕ) (a : L m v)
              → EqOn._≈_ (≈ZL v)
                  (zm (suc m) v (l-emb m v a)) (zm m v a))
      where

      -- Target system: same ℕ index and s∞ dynamics, ZL labels.
      -- 目标系统：同一 ℕ 索引与 s∞ 动力，标签为 ZL。
      Z : SysEq lzero z lzero z lzero
      Z = record
        { I  = ℕ
        ; A  = ZL
        ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ s∞ v
        ; ≈A = ≈ZL
        ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v)
        }

      -- Deterministic orbit induced by a label family.
      -- 标签族诱导的确定性轨道。
      orbit-of : (zl : (v : ℕ) → ZL v) (v : ℕ)
               → M (A Z) (E Z) v
      orbit-of zl v .M.here      = zl v
      orbit-of zl v .M.below w _ = orbit-of zl w

      -- Canonical evaluation of the thread born at v.
      -- v 处诞生线程的规范求值。
      eval∞ : (v : ℕ) → ZL v
      eval∞ v = zm v v (lab v v)

      zorbit : (v : ℕ) → M (A Z) (E Z) v
      zorbit = orbit-of eval∞

      -- Stage-m target orbit and the identity-index label relation.
      -- 阶段 m 目标轨道与索引恒等标签关系。
      zorbit-stage : (m v : ℕ) → M (A Z) (E Z) v
      zorbit-stage m = orbit-of (λ v → zm m v (lab m v))

      Rz : ℕ → ℕ → Set lzero
      Rz v w = v ≡ w

      Hz : (m v w : ℕ) → Rz v w → L m v → ZL w → Set z
      Hz m v .v refl a b = EqOn._≈_ (≈ZL v) b (zm m v a)

      -- Each stage leg as a forward simulation into Z.
      -- 每条阶段腿作为到 Z 的前向模拟。
      zleg : (m v : ℕ)
           → PushSimˢ (NStage m) Z Rz (Hz m) refl
                       (norbit m v) (zorbit-stage m v)
      zleg m v .PushSimˢ.here-eq = EqOn.refl (≈ZL v)
      zleg m v .PushSimˢ.push w (_ , eq) =
        w , ((tt , eq) , (refl , zleg m w))

      -- Evaluation of an arbitrary stage-tagged thread at its own index.
      -- 任意阶段标签化线程在其自身索引处的求值。
      eval-ray : ∀ {v : ℕ} → Thread v → ZL v
      eval-ray {v} (mk m a) = zm m v a

      H∞ : (v w : ℕ) → Rz v w → Thread v → ZL w → Set z
      H∞ v .v refl τ b = EqOn._≈_ (≈ZL v) b (eval-ray τ)

      -- The mediating simulation from the apex to Z.
      -- 从顶点到 Z 的 mediate 模拟。
      zmed : (v : ℕ)
           → PushSimˢ L∞ Z Rz H∞ refl (orbit∞ v) (zorbit v)
      zmed v .PushSimˢ.here-eq = EqOn.refl (≈ZL v)
      zmed v .PushSimˢ.push w (_ , eq) =
        w , ((tt , eq) , (refl , zmed w))

      -- Relative uniqueness: pointwise label agreement (explicit data)
      -- between two deterministic orbit families gives a bisimulation.
      -- This is not automatic: for a non-trivial fibre the agreement
      -- must be supplied at every node.
      -- 相对唯一性：两个确定性轨道族逐点标签一致（显式数据）即给出互
      -- 模拟。它不是自动的：非平凡纤维下，一致必须在每个节点显式给出。
      mutual
        orb-bisim : (zl₁ zl₂ : (v : ℕ) → ZL v)
                  → (he : (v : ℕ) → EqOn._≈_ (≈ZL v) (zl₁ v) (zl₂ v))
                  → (v : ℕ)
                  → _≈Mˢ_ (≈A Z) (≈E Z)
                           (orbit-of zl₁ v) (orbit-of zl₂ v)
        orb-bisim zl₁ zl₂ he v ._≈Mˢ_.here-eq = he v
        orb-bisim zl₁ zl₂ he v ._≈Mˢ_.below-eq w =
            idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
          , ( (λ _ → orb-bisim zl₁ zl₂ he w)
            , (λ _ → orb-bisim˘ zl₁ zl₂ he w) )

        orb-bisim˘ : (zl₁ zl₂ : (v : ℕ) → ZL v)
                   → (he : (v : ℕ) → EqOn._≈_ (≈ZL v) (zl₁ v) (zl₂ v))
                   → (v : ℕ)
                   → _≈Mˢ_ (≈A Z) (≈E Z)
                            (orbit-of zl₂ v) (orbit-of zl₁ v)
        orb-bisim˘ zl₁ zl₂ he v ._≈Mˢ_.here-eq =
          EqOn.sym (≈ZL v) (he v)
        orb-bisim˘ zl₁ zl₂ he v ._≈Mˢ_.below-eq w =
            idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
          , ( (λ _ → orb-bisim˘ zl₁ zl₂ he w)
            , (λ _ → orb-bisim zl₁ zl₂ he w) )

      -- Any competing label family pointwise equal to the canonical
      -- evaluation induces the same target tree up to _≈Mˢ_.
      -- 任何与规范求值逐点相等的竞争标签族诱导 _≈Mˢ_ 意义下相同的
      -- 目标树。
      mediate-unique : (zl : (v : ℕ) → ZL v)
                     → (he : (v : ℕ) → EqOn._≈_ (≈ZL v) (zl v) (eval∞ v))
                     → (v : ℕ)
                     → _≈Mˢ_ (≈A Z) (≈E Z)
                              (orbit-of zl v) (zorbit v)
      mediate-unique zl he v = orb-bisim zl eval∞ he v
