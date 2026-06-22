{-
ALMA 无限无界动态自指涉宇宙数学模型
--
可能的拓展方向 MorphLift Bisim EvalH EvalV mapEvalH mapEvalV DynamicsStep 与各种引理
-}
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module ALMA.Cosmos.Properties where
open import ALMA.Cosmos public
record MorphLift {ℓ} (C : Cosmos ℓ) : Set (lsuc (lsuc ℓ)) where
  coinductive
  private
    module C = Cosmos C
  field
    morphLift  : {A B : C.Obj} (f : C.Hom A B) (s : C.Shape A) → C.unfold s ⇒ℱ C.unfold (C.actS f s)
    morphLift-id : ∀ {A : C.Obj} (s : C.Shape A)
                 → morphLift C.idHom s 
                 ≃⇒ℱ subst (λ X → C.unfold s ⇒ℱ C.unfold X) 
                           (sym (C.actS-id s)) 
                           id⇒ℱ
    morphLift-comp : ∀ {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) (s : C.Shape A)
                   → morphLift (C.comp f g) s 
                   ≃⇒ℱ subst (λ X → C.unfold s ⇒ℱ C.unfold X) 
                             (sym (C.actS-comp f g s)) 
                             (morphLift g (C.actS f s) ∘⇒ℱ morphLift f s)
open MorphLift public
UnitCosmosMorphLift : ∀ {ℓ} → MorphLift (UnitCosmos {ℓ})
UnitCosmosMorphLift .morphLift _ _ = id⇒ℱ
UnitCosmosMorphLift .morphLift-id _ = refl-≃⇒ℱ
UnitCosmosMorphLift .morphLift-comp _ _ _ = sym-≃⇒ℱ (id-left-unit id⇒ℱ)
record Bisim {ℓ : Level} {F : Cosmos ℓ} (ml : MorphLift F) {A B : Obj F} (f g : Hom F A B) : Set (lsuc ℓ) where
  coinductive
  private
    module F = Cosmos F
    module ML = MorphLift ml
  field
    shape-eq    : (s : F.Shape A) → F.actS f s ≡ F.actS g s
    pos-eq      : (s : F.Shape A) (p : F.Pos (F.actS f s))
                → F.actP f s p ≡ F.actP g s (subst F.Pos (shape-eq s) p)
    morph-bisim : ∀ (s : F.Shape A)
                → let liftF = ML.morphLift {A} {B} f s
                      liftG = ML.morphLift {A} {B} g s
                      liftG' = subst (λ X → F.unfold s ⇒ℱ F.unfold X) (sym (shape-eq s)) liftG
                  in liftF ≃⇒ℱ liftG'
    unfold-bisim : (s : F.Shape A)
                → let chF = F.unfold-hom f s
                      chG = F.unfold-hom g s
                      chG' = subst (λ X → F.Hom (F.unfold-obj s) (F.unfold-obj X)) (sym (shape-eq s)) chG
                  in Bisim ml {A = F.unfold-obj s} {B = F.unfold-obj (F.actS f s)} chF chG'
open Bisim public
module _ {ℓ} {F : Cosmos ℓ} {ml : MorphLift F} where
  refl-bisim : ∀ {A B : Obj F} (f : Hom F A B) → Bisim ml f f
  refl-bisim {A} {B} f = go A B f
    where
    go : ∀ A B (f : Hom F A B) → Bisim ml f f
    go A B f .Bisim.shape-eq s = refl
    go A B f .Bisim.pos-eq s p = refl
    go A B f .Bisim.morph-bisim s = refl-≃⇒ℱ
    go A B f .Bisim.unfold-bisim s =
      go (unfold-obj F s)
         (unfold-obj F (actS F f s))
         (unfold-hom F f s)
  ≡→bisim : ∀ {A B : Obj F} {f g : Hom F A B} → f ≡ g → Bisim ml f g
  ≡→bisim refl = refl-bisim _
  subst-≃⇒ℱ-shape : ∀ {X : Obj F} {s1 s2 : Shape F X}
                    → (eq : s1 ≡ s2)
                    → {C : Cosmos ℓ}
                    → {m1 m2 : C ⇒ℱ unfold F s1}
                    → m1 ≃⇒ℱ m2
                    → subst (λ s' → C ⇒ℱ unfold F s') eq m1
                      ≃⇒ℱ
                      subst (λ s' → C ⇒ℱ unfold F s') eq m2
  subst-≃⇒ℱ-shape refl h = h
  sym-bisim : ∀ {A B} {f g : Hom F A B} → Bisim ml f g → Bisim ml g f
  sym-bisim {A} {B} {f} {g} b = go A B f g b
    where
    mutual
      go : ∀ Aₒ Bₒ (f g : Hom F Aₒ Bₒ) → Bisim ml f g → Bisim ml g f
      go Aₒ Bₒ f g b .Bisim.shape-eq s = sym (Bisim.shape-eq b s)
      go Aₒ Bₒ f g b .Bisim.pos-eq s p =
        let eqS  = Bisim.shape-eq b s
            p'   = subst (Pos F) (sym eqS) p
            orig = Bisim.pos-eq b s p'
            cancel : subst (Pos F) eqS p' ≡ p
            cancel = subst-inv' (Pos F) eqS {b = p}
        in sym (trans orig (cong (actP F g s) cancel))
      go Aₒ Bₒ f g b .Bisim.morph-bisim s =
        let eqS      = Bisim.shape-eq b s
            P : Shape F Bₒ → Set (lsuc ℓ)
            P X       = unfold F s ⇒ℱ unfold F X
            liftF     = morphLift ml f s
            liftG     = morphLift ml g s
            orig      = Bisim.morph-bisim b s
            symOrig   : subst P (sym eqS) liftG ≃⇒ℱ liftF
            symOrig   = sym-≃⇒ℱ orig
            substSym  : subst P eqS (subst P (sym eqS) liftG) ≃⇒ℱ subst P eqS liftF
            substSym  = subst-≃⇒ℱ-shape eqS symOrig
            cancel    : subst P eqS (subst P (sym eqS) liftG) ≡ liftG
            cancel    = subst-inv' P eqS {b = liftG}
            eq1       : liftG ≃⇒ℱ subst P eqS liftF
            eq1       = ≡-left-≃⇒ℱ (sym cancel) substSym
            eq2       : liftG ≃⇒ℱ subst P (sym (sym eqS)) liftF
            eq2       = ≡-right-≃⇒ℱ eq1 (cong (λ e → subst P e liftF) (sym-sym eqS))
        in eq2
      go Aₒ Bₒ f g b .Bisim.unfold-bisim s =
        let eqS  = Bisim.shape-eq b s
            f'   = unfold-hom F f s
            g'   = unfold-hom F g s
            orig = Bisim.unfold-bisim b s
        in aux Aₒ Bₒ s (actS F f s) (actS F g s) eqS f' g' orig
      aux : ∀ (A' B' : Obj F) (s : Shape F A') (X Y : Shape F B') (eq : X ≡ Y)
            (u : Hom F (unfold-obj F s) (unfold-obj F X))
            (v : Hom F (unfold-obj F s) (unfold-obj F Y))
          → Bisim ml u (subst (λ Z → Hom F (unfold-obj F s) (unfold-obj F Z)) (sym eq) v)
          → Bisim ml v (subst (λ Z → Hom F (unfold-obj F s) (unfold-obj F Z)) (sym (sym eq)) u)
      aux A' B' s X .X refl u v h = go (unfold-obj F s) (unfold-obj F X) u v h
  trans-bisim : ∀ {A B} {f g h : Hom F A B}
              → Bisim ml f g → Bisim ml g h → Bisim ml f h
  trans-bisim {A} {B} {f} {g} {h} b1 b2 = go A B f g h b1 b2
    where
    mutual
      go : ∀ Aₒ Bₒ (f g h : Hom F Aₒ Bₒ)
         → Bisim ml f g → Bisim ml g h → Bisim ml f h
      go Aₒ Bₒ f g h b1 b2 .Bisim.shape-eq s =
        trans (Bisim.shape-eq b1 s) (Bisim.shape-eq b2 s)
      go Aₒ Bₒ f g h b1 b2 .Bisim.pos-eq s p =
        let
          eq1 = Bisim.shape-eq b1 s
          eq2 = Bisim.shape-eq b2 s
          eq  = trans eq1 eq2
          pos1 = Bisim.pos-eq b1 s p
          pos2 = Bisim.pos-eq b2 s (subst (Pos F) eq1 p)
          step = trans pos1 pos2
          comp = subst-comp eq1 eq2 {b = p}
        in trans step (cong (actP F h s) comp)
      go Aₒ Bₒ f g h b1 b2 .Bisim.morph-bisim s =
        let
          eq1 = Bisim.shape-eq b1 s
          eq2 = Bisim.shape-eq b2 s
          eq  = trans eq1 eq2
          P : Shape F Bₒ → Set (lsuc ℓ)
          P X = unfold F s ⇒ℱ unfold F X
          liftF = morphLift ml f s
          liftG = morphLift ml g s
          liftH = morphLift ml h s
          mor1 = Bisim.morph-bisim b1 s
          mor2 = Bisim.morph-bisim b2 s
          mor2' = subst-≃⇒ℱ-shape (sym eq1) mor2
          step = trans-≃⇒ℱ mor1 mor2'
          comp : subst P (sym eq1) (subst P (sym eq2) liftH)
               ≡ subst P (sym eq) liftH
          comp =
            trans
              (subst-comp (sym eq2) (sym eq1) {b = liftH})
              (cong (λ e → subst P e liftH) (sym (sym-trans eq1 eq2)))
        in ≡-right-≃⇒ℱ step comp
      go Aₒ Bₒ f g h b1 b2 .Bisim.unfold-bisim s =
        let
          eq1 = Bisim.shape-eq b1 s
          eq2 = Bisim.shape-eq b2 s
          f' = unfold-hom F f s
          g' = unfold-hom F g s
          h' = unfold-hom F h s
          orig1 = Bisim.unfold-bisim b1 s
          orig2 = Bisim.unfold-bisim b2 s
        in aux Aₒ Bₒ s (actS F f s) (actS F g s) (actS F h s)
               eq1 eq2 f' g' h' orig1 orig2
      aux : ∀ (A' B' : Obj F) (s : Shape F A')
            (X Y Z : Shape F B')
            (eq1 : X ≡ Y) (eq2 : Y ≡ Z)
            (u : Hom F (unfold-obj F s) (unfold-obj F X))
            (v : Hom F (unfold-obj F s) (unfold-obj F Y))
            (w : Hom F (unfold-obj F s) (unfold-obj F Z))
          → Bisim ml u (subst (λ Q → Hom F (unfold-obj F s) (unfold-obj F Q)) (sym eq1) v)
          → Bisim ml v (subst (λ Q → Hom F (unfold-obj F s) (unfold-obj F Q)) (sym eq2) w)
          → Bisim ml u (subst (λ Q → Hom F (unfold-obj F s) (unfold-obj F Q)) (sym (trans eq1 eq2)) w)
      aux A' B' s X .X .X refl refl u v w h1 h2 =
        go (unfold-obj F s) (unfold-obj F X) u v w h1 h2
record EvalH {ℓ} (F : Cosmos ℓ) {A : Obj F} (s : Shape F A) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    valH : (X : Obj F) → Set (lsuc ℓ)
    subH : (p : Pos F s) → EvalH F (pos-to-shape F s p)
record EvalV {ℓ} (F : Cosmos ℓ) {A : Obj F} (s : Shape F A) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    valV : ∀ {B : Obj F} → Hom F A B → Set (lsuc ℓ)
    subV : (p : Pos F s) → EvalV F (pos-to-shape F s p)
open EvalH public
open EvalV public
mapEvalH : {ℓ : Level} {F G : Cosmos ℓ} (m : F ⇒ℱ G)
         → {A : Obj F} {s : Shape F A}
         → EvalH G (onShape m s)
         → EvalH F s
mapEvalH {ℓ} {F} {G} m {A} {s} e .valH X = valH e (onObj m X)
mapEvalH {ℓ} {F} {G} m {A} {s} e .subH p = 
  let eqB = onunfold-obj m s
      eqT = onPos-to-shape m p
      eqT' : subst (Shape G) (sym eqB) (pos-to-shape G (onShape m s) (onPos m p)) ≡ onShape m (pos-to-shape F s p)
      eqT' = trans (cong (subst (Shape G) (sym eqB)) (sym eqT)) (subst-inv eqB)
      P : (B : Obj G) → Shape G B → Set (lsuc (lsuc ℓ))
      P B t = EvalH G {B} t
      e' = dsubst₂ P (sym eqB) eqT' (subH e (onPos m p))
  in mapEvalH m e'
mapEvalV : {ℓ : Level} {F G : Cosmos ℓ} (m : F ⇒ℱ G)
         → {A : Obj F} {s : Shape F A}
         → EvalV G (onShape m s)
         → EvalV F s
mapEvalV {ℓ} {F} {G} m {A} {s} e .valV f = valV e (onHom m f)
mapEvalV {ℓ} {F} {G} m {A} {s} e .subV p = 
  let eqB = onunfold-obj m s
      eqT = onPos-to-shape m p
      eqT' : subst (Shape G) (sym eqB) (pos-to-shape G (onShape m s) (onPos m p))
             ≡ onShape m (pos-to-shape F s p)
      eqT' = trans (cong (subst (Shape G) (sym eqB)) (sym eqT)) (subst-inv eqB)
      P : (B : Obj G) → Shape G B → Set (lsuc (lsuc ℓ))
      P B t = EvalV G {B} t
      e' = dsubst₂ P (sym eqB) eqT' (subV e (onPos m p))
  in mapEvalV m e'
cast-EvalH : {ℓ : Level} (C : Cosmos ℓ) {X : Obj C} {s1 s2 : Shape C X}
           → s1 ≡ s2 → EvalH C s1 → EvalH C s2
cast-EvalH C refl e .valH X = valH e X
cast-EvalH C refl e .subH p = subH e p
cast-EvalV : {ℓ : Level} (C : Cosmos ℓ) {X : Obj C} {s1 s2 : Shape C X}
           → s1 ≡ s2 → EvalV C s1 → EvalV C s2
cast-EvalV C refl e .valV f = valV e f
cast-EvalV C refl e .subV p = subV e p
evolveH : {ℓ : Level} (C : Cosmos ℓ)
        → {A B : Obj C} (τ : Hom C A B) {s : Shape C A}
        → EvalH C s → EvalH C (actS C τ s)
evolveH C τ {s} old .valH X = valH old X
evolveH C τ {s} old .subH p rewrite pos-actS-compat C τ s p =
  evolveH C (unfold-hom C τ s) (subH old (actP C τ s p))
evolveV : {ℓ : Level} (C : Cosmos ℓ)
        → {A B : Obj C} (τ : Hom C A B) {s : Shape C A}
        → EvalV C s → EvalV C (actS C τ s)
evolveV C τ {s} old .valV f = valV old (comp C τ f)
evolveV C τ {s} old .subV p rewrite pos-actS-compat C τ s p =
  evolveV C (unfold-hom C τ s) (subV old (actP C τ s p))
bisim-preserves-evolveH : {ℓ : Level} {C : Cosmos ℓ} {ml : MorphLift C}
                        → {A B : Obj C} {f g : Hom C A B}
                        → Bisim ml f g
                        → ∀ {s : Shape C A} (e : EvalH C s)
                        → EvalH C (actS C f s) ≡ EvalH C (actS C g s)
bisim-preserves-evolveH {C = C} bisim {s} e =
  cong (λ x → EvalH C x) (shape-eq bisim s)
bisim-preserves-evolveV : {ℓ : Level} {C : Cosmos ℓ} {ml : MorphLift C}
                        → {A B : Obj C} {f g : Hom C A B}
                        → Bisim ml f g
                        → ∀ {s : Shape C A} (e : EvalV C s)
                        → EvalV C (actS C f s) ≡ EvalV C (actS C g s)
bisim-preserves-evolveV {C = C} bisim {s} e =
  cong (λ x → EvalV C x) (shape-eq bisim s)
record DynamicsStep {ℓ : Level} (C : Cosmos ℓ) {A B : Obj C} (τ : Hom C A B) (s : Shape C A) : Set (lsuc (lsuc ℓ)) where
  coinductive
  private
    module C = Cosmos C
  field
    curr : EvalH C s × EvalV C s
    next : EvalH C (C.actS τ s) × EvalV C (C.actS τ s)
    eqH : evolveH C τ (curr .proj₁) ≡ (next .proj₁)
    eqV : evolveV C τ (curr .proj₂) ≡ (next .proj₂)
-- 基本的同伦等式
unfold-hom-id' : ∀ {ℓ} (C : Cosmos ℓ) {A : Obj C} {s : Shape C A}
               → subst (λ X → Hom C (unfold-obj C s) (unfold-obj C X)) 
                       (actS-id C {A = A} s) 
                       (unfold-hom C (idHom C) s)
               ≡ idHom C {A = unfold-obj C s}
unfold-hom-id' C {A} {s} = 
  let
    P : _
    P X = Hom C (unfold-obj C s) (unfold-obj C X)
    eq = actS-id C {A = A} s
    idH = idHom C {A = unfold-obj C s}
  in
  trans
    (cong (subst P eq) (unfold-hom-id C {A = A} s))
    (subst-inv' P eq {b = idH})
unfold-hom-comp' : ∀ {ℓ} (C : Cosmos ℓ) {A B D : Obj C} 
                 → (f : Hom C A B) (g : Hom C B D) {s : Shape C A}
                 → subst (λ X → Hom C (unfold-obj C s) (unfold-obj C X)) 
                         (actS-comp C f g s) 
                         (unfold-hom C (comp C f g) s) 
                 ≡ comp C (unfold-hom C f s) (unfold-hom C g (actS C f s))
unfold-hom-comp' C f g {s} = 
  let
    P : _
    P X = Hom C (unfold-obj C s) (unfold-obj C X)
    eq = actS-comp C f g s
    compH = comp C (unfold-hom C f s) (unfold-hom C g (actS C f s))
  in
  trans
    (cong (subst P eq) (unfold-hom-comp C f g s))
    (subst-inv' P eq {b = compH})
-- subst 在 ⇒ℱ 上的性质
subst-⇒ℱ-onObj : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F)
                → onObj (subst (λ C → F ⇒ℱ C) eq m) X ≡ subst (λ Y → Obj Y) eq (onObj m X)
subst-⇒ℱ-onObj _ _ _ _ refl _ _ = refl
subst-⇒ℱ-onShape : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) (t : Shape F X)
                  → onShape (subst (λ C' → F ⇒ℱ C') eq m) t 
                  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Obj C')) → Shape (p .proj₁) (p .proj₂)) 
                          (Σ-≡ eq (sym (subst-⇒ℱ-onObj ℓ F C D eq m X))) 
                          (onShape m t)
subst-⇒ℱ-onShape _ _ _ _ refl _ _ _ = refl
subst-⇒ℱ-onObjShape : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) (t : Shape F X)
  → subst (λ C' → Σ (Obj C') (λ o → Shape C' o)) eq (onObj m X , onShape m t)
    ≡ ( onObj (subst (λ C' → F ⇒ℱ C') eq m) X
      , onShape (subst (λ C' → F ⇒ℱ C') eq m) t )
subst-⇒ℱ-onObjShape ℓ F C D refl m X t = refl
subst-⇒ℱ-onObj2 : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X Y : Obj F)
  → subst (λ C' → Obj C' × Obj C') eq (onObj m X , onObj m Y)
    ≡ ( onObj (subst (λ C' → F ⇒ℱ C') eq m) X
      , onObj (subst (λ C' → F ⇒ℱ C') eq m) Y )
subst-⇒ℱ-onObj2 ℓ F C D refl m X Y = refl
subst-⇒ℱ-onHom : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X Y : Obj F) (f : Hom F X Y)
  → onHom (subst (λ C' → F ⇒ℱ C') eq m) f 
  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Obj C' × Obj C')) 
            → Hom (p .proj₁) (p .proj₂ .proj₁) (p .proj₂ .proj₂)) 
          (Σ-≡ eq (subst-⇒ℱ-onObj2 ℓ F C D eq m X Y)) 
          (onHom m f)
subst-⇒ℱ-onHom ℓ F C D refl m X Y f = refl
subst-⇒ℱ-onPos : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) {t : Shape F X} (p : Pos F t)
  → onPos (subst (λ C' → F ⇒ℱ C') eq m) p 
  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Σ (Obj C') (λ o → Shape C' o))) 
            → Pos (p .proj₁) (p .proj₂ .proj₂)) 
          (Σ-≡ eq (subst-⇒ℱ-onObjShape ℓ F C D eq m X t)) 
          (onPos m p)
subst-⇒ℱ-onPos ℓ F C D refl m X {t} p = refl
subst-⇒ℱ-onunfold : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) (t : Shape F X)
  → onunfold (subst (λ C' → F ⇒ℱ C') eq m) t 
  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Σ (Obj C') (λ o → Shape C' o))) 
            → unfold F t ⇒ℱ unfold (p .proj₁) (p .proj₂ .proj₂)) 
          (Σ-≡ eq (subst-⇒ℱ-onObjShape ℓ F C D eq m X t)) 
          (onunfold m t)
subst-⇒ℱ-onunfold ℓ F C D refl m X t = refl
-- subst 与组合的 ≃⇒ℱ 相容性
subst-comp-⇒ℱ-both : ∀ {ℓ} {A B B' C : Cosmos ℓ} (p : B ≡ B')
  → (f : A ⇒ℱ B) (g : B ⇒ℱ C)
  → subst (λ D → D ⇒ℱ C) p g ∘⇒ℱ subst (λ D → A ⇒ℱ D) p f
    ≃⇒ℱ
    g ∘⇒ℱ f
subst-comp-⇒ℱ-both refl f g = refl-≃⇒ℱ
-- subst 与 ≃⇒ℱ 的消去/引入
subst-left-cancel-≃⇒ℱ' : ∀ {ℓ} {F : Cosmos ℓ} {C D : Cosmos ℓ} (eq : C ≡ D)
                        → {m : F ⇒ℱ C} {n : F ⇒ℱ D}
                        → n ≃⇒ℱ subst (λ X → F ⇒ℱ X) eq m
                        → subst (λ X → F ⇒ℱ X) (sym eq) n ≃⇒ℱ m
subst-left-cancel-≃⇒ℱ' refl h = h
-- 辅助类型别名与等式构造器
ObjShape : (ℓ : Level) (C : Cosmos ℓ) → Set (lsuc ℓ)
ObjShape ℓ C = Σ (Obj C) (Shape C)
ObjPair : (ℓ : Level) (C : Cosmos ℓ) → Set (lsuc ℓ)
ObjPair ℓ C = Obj C × Obj C
ObjSubst : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) → C₁ ≡ C₂ → Obj C₁ → Obj C₂
ObjSubst ℓ C₁ C₂ eq o = subst (λ Y → Obj Y) eq o
ShapeSubstP : (ℓ : Level) → Σ (Cosmos ℓ) (λ Y → Obj Y) → Set (lsuc ℓ)
ShapeSubstP ℓ p = Shape (p .proj₁) (p .proj₂)
PosSubstP : (ℓ : Level) (C : Cosmos ℓ) → ObjShape ℓ C → Set (lsuc ℓ)
PosSubstP ℓ C (o , s) = Pos C s
HomSubstP : (ℓ : Level) (C : Cosmos ℓ) → ObjPair ℓ C → Set (lsuc ℓ)
HomSubstP ℓ C (o1 , o2) = Hom C o1 o2
ShapeEq : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) (o : Obj C₁)
        → _≡_ {A = Σ (Cosmos ℓ) (λ Y → Obj Y)}
            (C₁ , o)
            (C₂ , ObjSubst ℓ C₁ C₂ eq o)
ShapeEq ℓ C₁ .C₁ refl o = refl
HomEq : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) (o1 o2 : Obj C₁)
      → _≡_ {A = Σ (Cosmos ℓ) (λ Y → Obj Y × Obj Y)}
          (C₁ , (o1 , o2))
          (C₂ , (ObjSubst ℓ C₁ C₂ eq o1 , ObjSubst ℓ C₁ C₂ eq o2))
HomEq ℓ C₁ .C₁ refl o1 o2 = refl
PosEq : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) (o : Obj C₁) (s : Shape C₁ o)
      → _≡_ {A = Σ (Cosmos ℓ) (λ Y → Σ (Obj Y) (Shape Y))}
          (C₁ , (o , s))
          (C₂ , (ObjSubst ℓ C₁ C₂ eq o , subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o) s))
PosEq ℓ C₁ .C₁ refl o s = refl
same-C-PosEq : ∀ ℓ (C : Cosmos ℓ) {o1 o2 : Obj C} (eO : o1 ≡ o2) (s2 : Shape C o2)
             → (o1 , subst (Shape C) (sym eO) s2) ≡ (o2 , s2)
same-C-PosEq ℓ C {o1} {.o1} refl s2 = refl
PosAt : (ℓ : Level) (C : Cosmos ℓ) (o : Obj C) → Shape C o → Set (lsuc ℓ)
PosAt ℓ C o s = Pos C {o} s
PosOfShape : (ℓ : Level) (C : Cosmos ℓ) → ObjShape ℓ C → Set (lsuc ℓ)
PosOfShape ℓ C (o , s) = PosAt ℓ C o s
-- 运输 Pos/Hom 及相关引理
transport-Pos : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
              → {o : Obj C₁} {s : Shape C₁ o}
              → Pos C₁ s → Pos C₂ (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o) s)
transport-Pos ℓ C₁ .C₁ refl p = p
transport-Hom : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) {a b : Obj C₁}
              → Hom C₁ a b → Hom C₂ (ObjSubst ℓ C₁ C₂ eq a) (ObjSubst ℓ C₁ C₂ eq b)
transport-Hom ℓ C₁ .C₁ refl f = f
shape-subst-lemma : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
  {o1 o2 : Obj C₁} (eO : o1 ≡ o2)
  (s2 : Shape C₁ o2)
  → subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o1) (subst (Shape C₁) (sym eO) s2)
  ≡ subst (Shape C₂) (sym (cong (ObjSubst ℓ C₁ C₂ eq) eO))
    (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o2) s2)
shape-subst-lemma ℓ C₁ .C₁ refl {o1} {o2} eO s2 =
  begin
    subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₁ refl o1) (subst (Shape C₁) (sym eO) s2)
      ≡⟨ refl ⟩
    subst (Shape C₁) (sym eO) s2
      ≡⟨ cong (λ (eq : o1 ≡ o2) → subst (Shape C₁) (sym eq) s2) 
              (sym (cong-id eO)) ⟩
    subst (Shape C₁) (sym (cong (ObjSubst ℓ C₁ C₁ refl) eO)) s2
      ≡⟨ refl ⟩
    subst (Shape C₁) (sym (cong (ObjSubst ℓ C₁ C₁ refl) eO))
          (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₁ refl o2) s2)
  ∎
pos-subst-lemma :
  ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
  {o1 o2 : Obj C₁} (eO : o1 ≡ o2)
  {s2 : Shape C₁ o2}
  (p2 : Pos C₁ {o2} s2)
  → transport-Pos ℓ C₁ C₂ eq {o1} {subst (Shape C₁) (sym eO) s2}
      (subst {A = ObjShape ℓ C₁} {ℓ = lsuc ℓ} (PosSubstP ℓ C₁)
        (sym (same-C-PosEq ℓ C₁ eO s2)) p2)
  ≡ subst {A = Shape C₂ (ObjSubst ℓ C₁ C₂ eq o1)} {ℓ = lsuc ℓ}
      (Pos C₂ {ObjSubst ℓ C₁ C₂ eq o1})
      (sym (shape-subst-lemma ℓ C₁ C₂ eq eO s2))
      (subst {A = ObjShape ℓ C₂} {ℓ = lsuc ℓ} (PosSubstP ℓ C₂)
        (sym (same-C-PosEq ℓ C₂ 
          (cong (ObjSubst ℓ C₁ C₂ eq) eO) 
          (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o2) s2)))
        (transport-Pos ℓ C₁ C₂ eq {o2} {s2} p2))
pos-subst-lemma ℓ C₁ C₂ eq {o1} {o2} eO {s2} p2 =
  J (λ C₂' eq' →
       transport-Pos ℓ C₁ C₂' eq' {o1} {subst (Shape C₁) (sym eO) s2}
         (subst (PosSubstP ℓ C₁) (sym (same-C-PosEq ℓ C₁ eO s2)) p2)
       ≡ subst (Pos C₂' {ObjSubst ℓ C₁ C₂' eq' o1})
           (sym (shape-subst-lemma ℓ C₁ C₂' eq' eO s2))
           (subst (PosSubstP ℓ C₂')
             (sym (same-C-PosEq ℓ C₂'
               (cong (ObjSubst ℓ C₁ C₂' eq') eO)
               (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂' eq' o2) s2)))
             (transport-Pos ℓ C₁ C₂' eq' {o2} {s2} p2)))
    eq
    ((J (λ o2' eO' → (s2' : Shape C₁ o2') → (p2' : Pos C₁ {o2'} s2') →
           transport-Pos ℓ C₁ C₁ refl {o1} {subst (Shape C₁) (sym eO') s2'}
             (subst (PosSubstP ℓ C₁) (sym (same-C-PosEq ℓ C₁ eO' s2')) p2')
           ≡ subst (Pos C₁ {o1})
               (sym (shape-subst-lemma ℓ C₁ C₁ refl eO' s2'))
               (subst (PosSubstP ℓ C₁)
                 (sym (same-C-PosEq ℓ C₁ (cong (ObjSubst ℓ C₁ C₁ refl) eO')
                   (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₁ refl o2') s2')))
                 (transport-Pos ℓ C₁ C₁ refl {o2'} {s2'} p2')))
        eO
        (λ s2' p2' → refl))
     s2 p2)  
hom-subst-lemma : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
                → {a1 a2 : Obj C₁} {b1 b2 : Obj C₁}
                → (eA : a1 ≡ a2) (eB : b1 ≡ b2)
                → (f2 : Hom C₁ a2 b2)
                → transport-Hom ℓ C₁ C₂ eq (subst₂ (Hom C₁) (sym eA) (sym eB) f2)
                ≡ subst₂ (Hom C₂) (cong (ObjSubst ℓ C₁ C₂ eq) (sym eA))
                                 (cong (ObjSubst ℓ C₁ C₂ eq) (sym eB))
                                 (transport-Hom ℓ C₁ C₂ eq f2)
hom-subst-lemma ℓ C₁ C₂ eq {a1} {a2} {b1} {b2} eA eB f2 =
  J (λ C₂' eq' →
       transport-Hom ℓ C₁ C₂' eq' (subst₂ (Hom C₁) (sym eA) (sym eB) f2)
       ≡ subst₂ (Hom C₂') (cong (ObjSubst ℓ C₁ C₂' eq') (sym eA))
                          (cong (ObjSubst ℓ C₁ C₂' eq') (sym eB))
                          (transport-Hom ℓ C₁ C₂' eq' f2))
    eq
    ( ( J (λ a2' eA' → (b2' : Obj C₁) → (eB' : b1 ≡ b2') → (f2' : Hom C₁ a2' b2') →
               transport-Hom ℓ C₁ C₁ refl (subst₂ (Hom C₁) (sym eA') (sym eB') f2')
               ≡ subst₂ (Hom C₁) (cong (ObjSubst ℓ C₁ C₁ refl) (sym eA'))
                                (cong (ObjSubst ℓ C₁ C₁ refl) (sym eB'))
                                (transport-Hom ℓ C₁ C₁ refl f2'))
          eA
          (λ b2' eB' f2' →
             ( J (λ b2'' eB'' → (f2'' : Hom C₁ a1 b2'') →
                   transport-Hom ℓ C₁ C₁ refl (subst₂ (Hom C₁) (sym refl) (sym eB'') f2'')
                   ≡ subst₂ (Hom C₁) (cong (ObjSubst ℓ C₁ C₁ refl) (sym refl))
                                    (cong (ObjSubst ℓ C₁ C₁ refl) (sym eB''))
                                    (transport-Hom ℓ C₁ C₁ refl f2''))
                 eB'
                 (λ f2'' → refl)
             ) f2'
          )
      )
      b2 eB f2
    )
-- ≃⇒ℱ 相关的形状/位置推理
eqSh-base-simp : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
                → (eqSh' : S1 ≡ subst (Shape G) refl S2')
                → S1 ≡ S2'
eqSh-base-simp {G = G} {O1} {S1} {S2'} eqSh' = 
  trans eqSh' (subst-refl-id (Shape G) S2')
shape-lemma-base-simp : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
                      → (shape-lemma' : S2' ≡ subst (Shape G) refl S1)
                      → S2' ≡ S1
shape-lemma-base-simp {G = G} {O1} {S1} {S2'} shape-lemma' = 
  trans shape-lemma' (subst-refl-id (Shape G) S1)
shape-lemma-eq-base : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
                    → (eqSh' : S1 ≡ subst (Shape G) refl S2')
                    → (shape-lemma' : S2' ≡ subst (Shape G) refl S1)
                    → (shape-lemma-eq : shape-lemma' ≡ sym (trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl)))
                    → sym shape-lemma' ≡ eqSh'
shape-lemma-eq-base {G = G} {O1} {S1} {S2'} eqSh' shape-lemma' shape-lemma-eq =
  let
    step1 : sym shape-lemma' ≡ trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl)
    step1 = trans (cong sym shape-lemma-eq) (sym (sym-sym (trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl))))
    step2 : trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl) ≡ eqSh'
    step2 = J (λ S2'' eqSh'' → trans (cong (subst (Shape G) refl) eqSh'') (subst-inv' (Shape G) refl) ≡ eqSh'')
              eqSh'
              refl
  in
  trans step1 step2
eq2-base-prop : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
              → (eqSh' : S1 ≡ subst (Shape G) refl S2')
              → (shape-lemma' : S2' ≡ subst (Shape G) refl S1)
              → (shape-lemma-eq : shape-lemma' ≡ sym (trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl)))
              → trans (subst-unfold G refl S1) (cong (unfold G {O1}) (sym shape-lemma'))
              ≡ cong (unfold G {O1}) (eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh')
eq2-base-prop {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh' shape-lemma' shape-lemma-eq =
  let
    step1 : trans (subst-unfold G refl S1) (cong (unfold G {O1}) (sym shape-lemma'))
          ≡ cong (unfold G {O1}) (sym shape-lemma')
    step1 = transReflˡ _
    step2 : sym shape-lemma' ≡ eqSh'
    step2 = shape-lemma-eq-base {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh' shape-lemma' shape-lemma-eq
    step3 : eqSh' ≡ eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh'
    step3 = sym (trans-reflʳ eqSh')
    step4 : sym shape-lemma' ≡ eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh'
    step4 = trans step2 step3
    step5 : cong (unfold G {O1}) (sym shape-lemma') ≡ cong (unfold G {O1}) (eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh')
    step5 = cong (cong (unfold G {O1})) step4
  in
  trans step1 step5
sym-sym-eqO : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F}
            → let eqO = onObj-eq e A
              in sym (sym eqO) ≡ eqO
sym-sym-eqO {e = e} {A} = sym (sym-sym (onObj-eq e A))
S-eq-correct : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A}
             → let eqO = onObj-eq e A
                   eqSh = onShape-eq e s
                   S1 = onShape m₁ s
                   S2 = onShape m₂ s
               in subst (Shape G) eqO S1 ≡ S2
S-eq-correct {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} =
  trans (cong (subst (Shape G) (onObj-eq e A)) (onShape-eq e s)) (subst-inv' (Shape G) (onObj-eq e A))
subst-pos-exchange-refl : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2 : Shape G O1}
                           (eqSh : S1 ≡ S2) (P2 : Pos G S2)
                         → subst (Pos G)
                                 (trans (cong (subst (Shape G) refl) eqSh) (subst-inv' (Shape G) refl))
                                 (subst (Pos G) (sym eqSh) P2)
                           ≡ P2
subst-pos-exchange-refl {G = G} {O1 = O1} eqSh P2 =
  subst (λ S → subst (Pos G) S (subst (Pos G) (sym eqSh) P2) ≡ P2)
        (sym (S-eq-base-eq {G = G} {O1 = O1} eqSh))
        (subst-inv' (Pos G) eqSh)
subst-pos-exchange : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos F s}
                   → let eqO = onObj-eq e A
                         eqSh = onShape-eq e s
                         S1 = onShape m₁ s
                         S2 = onShape m₂ s
                         P2 = onPos m₂ p
                         L = subst-pos G eqO S1 (subst (Pos G {onObj m₁ A}) (sym eqSh) (subst-pos G (sym eqO) S2 P2))
                     in subst (Pos G) (S-eq-correct {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}) L ≡ P2
subst-pos-exchange {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p} =
  let
    O1 = onObj m₁ A
    S1 = onShape m₁ s
    eqO = onObj-eq e A
    eqSh = onShape-eq e s
    S2 = onShape m₂ s
    P2 = onPos m₂ p
    P : (O2 : Obj G) → O1 ≡ O2 → Set (lsuc ℓ)
    P O2 eqO' = ∀ (S2 : Shape G O2)
                  (eqSh' : S1 ≡ subst (Shape G) (sym eqO') S2)
                  (P2' : Pos G S2) →
                  subst (Pos G)
                        (trans (cong (subst (Shape G) eqO') eqSh') (subst-inv' (Shape G) eqO'))
                        (subst-pos G eqO' S1
                          (subst (Pos G) (sym eqSh') (subst-pos G (sym eqO') S2 P2')))
                  ≡ P2'
    base : P O1 refl
    base S2' eqSh' P2' = subst-pos-exchange-refl {G = G} {O1 = O1} eqSh' P2'
  in J P eqO base S2 eqSh P2
pos-step1 : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos F s}
          → let eqO = onObj-eq e A
                eqSh = onShape-eq e s
                S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                S1 = onShape m₁ s
                P1 = onPos m₁ p
                P2 = onPos m₂ p
            in subst-pos G eqO S1 P1 ≡ subst (Pos G) (sym S-eq) P2
pos-step1 {G = G} {m₁ = m₁} {m₂ = m₂} {e = e} {A} {s} {p} =
  let
    eqO = onObj-eq e A
    S-eq = trans (cong (subst (Shape G) eqO) (onShape-eq e s)) (subst-inv' (Shape G) eqO)
    step = pos-step1-correct {G = G} {m₁ = m₁} {m₂ = m₂} {e = e} {A} {s} {p}
  in
  subst-sym-swap (Pos G) S-eq step
subst-cancel-pos : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos G (onShape m₂ s)}
                 → let eqO = onObj-eq e A
                       eqSh = onShape-eq e s
                       S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                       shape-lemma = shape-sym-lemma e s
                       subst-shape = subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
                       combined-eq = trans shape-lemma (trans subst-shape S-eq)
                   in subst (Pos G) combined-eq p ≡ p
subst-cancel-pos {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p} =
  let
    eqO = onObj-eq e A
    eqSh = onShape-eq e s
    S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
    shape-lemma = shape-sym-lemma e s
    subst-shape = subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
    shape-lemma-is-sym' : shape-lemma ≡ sym (trans subst-shape S-eq)
    shape-lemma-is-sym' =
      trans (shape-lemma-def {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s})
            (sym (sym-trans subst-shape S-eq))
    combined-eq-is-refl : trans shape-lemma (trans subst-shape S-eq) ≡ refl
    combined-eq-is-refl =
      trans (cong (λ x → trans x (trans subst-shape S-eq)) shape-lemma-is-sym')
            (trans-symˡ (trans subst-shape S-eq))
  in
  cong (λ eq → subst (Pos G) eq p) combined-eq-is-refl
cancel-shape-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos G (onShape m₂ s)}
                → let eqO = onObj-eq e A
                      eqSh = onShape-eq e s
                      S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                      shape-lemma = shape-sym-lemma e s
                      subst-shape = subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
                      correct-combined-eq = trans shape-lemma (trans subst-shape S-eq)
                  in subst (Pos G {onObj m₂ A}) correct-combined-eq p ≡ p
cancel-shape-eq {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p} = 
  subst-cancel-pos {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p}
-- 对称化等式（将 ≃⇒ℱ 的证据反过来）
onShape-eq-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
               → (h : m₁ ≃⇒ℱ m₂) {A : Obj F} (s : Shape F A)
               → onShape m₂ s ≡ subst (Shape G) (onObj-eq h A) (onShape m₁ s)
onShape-eq-sym {G = G} h {A} s =
  let
    eqO = onObj-eq h A
    eqSh = onShape-eq h s
  in
  trans (sym (subst-inv' (Shape G) eqO))
        (cong (subst (Shape G) eqO) (sym eqSh))
onHom-eq-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
             → (h : m₁ ≃⇒ℱ m₂) {A B : Obj F} (f : Hom F A B)
             → onHom m₂ f ≡ subst₂ (Hom G) (onObj-eq h A) (onObj-eq h B) (onHom m₁ f)
onHom-eq-sym {G = G} h {A} {B} f =
  let
    eqOA = onObj-eq h A
    eqOB = onObj-eq h B
    eqH = onHom-eq h f
  in
  trans (sym (subst-inv₂' eqOA eqOB))
        (cong (subst₂ (Hom G) eqOA eqOB) (sym eqH))
onPos-eq-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
             → (h : m₁ ≃⇒ℱ m₂) {A : Obj F} {s : Shape F A} (p : Pos F s)
             → onPos m₂ p ≡ subst (Pos G) (S-eq-correct {e = h} {A} {s})
                                   (subst-pos G (onObj-eq h A) (onShape m₁ s) (onPos m₁ p))
onPos-eq-sym {G = G} h {A} {s} p =
  let
    eqO = onObj-eq h A
    eqSh = onShape-eq h s
    eqP = onPos-eq h p
    S-eq = S-eq-correct {e = h} {A} {s}
  in
  sym (pos-step1-correct {e = h} {A} {s} {p})
-- 组合等式与路径
combine-shape-eqs : ∀ {ℓ} (G : Cosmos ℓ) {O1 O2 O3 : Obj G}
                    {S1 : Shape G O1} {S2 : Shape G O2} {S3 : Shape G O3}
                    {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                    (eqS1 : S1 ≡ subst (Shape G) (sym pO1) S2)
                    (eqS2 : S2 ≡ subst (Shape G) (sym pO2) S3)
                  → S1 ≡ subst (Shape G) (sym (trans pO1 pO2)) S3
combine-shape-eqs G {pO1 = pO1} {pO2 = pO2} eqS1 eqS2 =
  trans eqS1
    (trans (cong (subst (Shape G) (sym pO1)) eqS2)
           (subst-sym-comp pO1 pO2))
combine-pos-eqs : ∀ {ℓ} (G : Cosmos ℓ) {O1 O2 O3 : Obj G}
                  {S1 : Shape G O1} {S2 : Shape G O2} {S3 : Shape G O3}
                  {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                  (eqS1 : S1 ≡ subst (Shape G) (sym pO1) S2)
                  (eqS2 : S2 ≡ subst (Shape G) (sym pO2) S3)
                  (p3 : Pos G S3)
                → subst (Pos G) (sym eqS1)
                    (subst (Pos G) (sym (cong (subst (Shape G) (sym pO1)) eqS2))
                      (subst (Pos G) (sym (subst-sym-comp pO1 pO2))
                        (subst-pos G (sym (trans pO1 pO2)) S3 p3)))
                ≡ subst (Pos G) (sym (combine-shape-eqs G eqS1 eqS2))
                    (subst-pos G (sym (trans pO1 pO2)) S3 p3)
combine-pos-eqs G {pO1 = pO1} {pO2 = pO2} eqS1 eqS2 p3 =
  subst-sym-comp3 eqS1
                  (cong (subst (Shape G) (sym pO1)) eqS2)
                  (subst-sym-comp pO1 pO2)
                  {b = subst-pos G (sym (trans pO1 pO2)) _ p3}
combine-pos-eq-helper : ∀ {ℓ} (G : Cosmos ℓ) {X Y Z : Obj G}
                         (eq1 : X ≡ Y) (eq2 : Y ≡ Z)
                         {S1 : Shape G X} {S2 : Shape G Y} {S3 : Shape G Z}
                         (eqS1 : S1 ≡ subst (Shape G) (sym eq1) S2)
                         (eqS2 : S2 ≡ subst (Shape G) (sym eq2) S3)
                         (p3 : Pos G S3)
                       → subst (Pos G) (sym eqS1)
                           (subst (Pos G) 
                              (sym (cong (subst (Shape G) (sym eq1)) eqS2))
                              (subst (Pos G) 
                                 (sym (subst-sym-comp eq1 eq2))
                                 (subst-pos G (sym (trans eq1 eq2)) S3 p3)))
                       ≡ subst (Pos G) 
                           (sym (trans eqS1 
                                      (trans (cong (subst (Shape G) (sym eq1)) eqS2)
                                             (subst-sym-comp eq1 eq2))))
                           (subst-pos G (sym (trans eq1 eq2)) S3 p3)
combine-pos-eq-helper G eq1 eq2 eqS1 eqS2 p3 = 
  subst-sym-comp3 eqS1 
                  (cong (subst (Shape G) (sym eq1)) eqS2)
                  (subst-sym-comp eq1 eq2)
                  {b = subst-pos G (sym (trans eq1 eq2)) _ p3}
combine-hom-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ m₃ : F ⇒ℱ G}
               → (h1 : m₁ ≃⇒ℱ m₂) (h2 : m₂ ≃⇒ℱ m₃) {A B : Obj F} (f : Hom F A B)
               → onHom m₁ f ≡ subst₂ (Hom G) (sym (trans (onObj-eq h1 A) (onObj-eq h2 A))) 
                                      (sym (trans (onObj-eq h1 B) (onObj-eq h2 B))) 
                                      (onHom m₃ f)
combine-hom-eq {G = G} h1 h2 {A} {B} f =
  let
    pO1A = onObj-eq h1 A
    pO1B = onObj-eq h1 B
    pO2A = onObj-eq h2 A
    pO2B = onObj-eq h2 B
    eqH1 = onHom-eq h1 f
    eqH2 = onHom-eq h2 f
  in
  trans eqH1 (trans (cong (subst₂ (Hom G) (sym pO1A) (sym pO1B)) eqH2) 
                    (subst₂-sym-comp pO1A pO1B pO2A pO2B))
trans-unfold-path : ∀ {ℓ} (G : Cosmos ℓ) (X Y Z : Obj G)
                    (eqO1 : X ≡ Y) (eqO2 : Y ≡ Z)
                    (s1 : Shape G X) (s2 : Shape G Y) (s3 : Shape G Z)
                    (eqS1 : s1 ≡ subst (Shape G) (sym eqO1) s2)
                    (eqS2 : s2 ≡ subst (Shape G) (sym eqO2) s3) →
                    trans (trans (subst-unfold G (sym eqO2) s3) (cong (unfold G) (sym eqS2)))
                          (trans (subst-unfold G (sym eqO1) s2) (cong (unfold G) (sym eqS1)))
                    ≡ trans (subst-unfold G (sym (trans eqO1 eqO2)) s3)
                            (cong (unfold G)
                              (sym (trans eqS1
                                     (trans (cong (subst (Shape G) (sym eqO1)) eqS2)
                                            (trans (subst-comp (sym eqO2) (sym eqO1))
                                                   (cong (λ e → subst (Shape G) e s3)
                                                         (sym (sym-trans eqO1 eqO2))))))))
trans-unfold-path G X .X .X refl refl s1 .s1 .s1 refl refl = refl
-- MorphLift 下的额外性质
unfold-subst-shape-sym : ∀ {ℓ} {C : Cosmos ℓ} {o₁ o₂ : Obj C} (eq : o₁ ≡ o₂) (s : Shape C o₂)
                      → unfold C (subst (Shape C) (sym eq) s) ≡ unfold C s
unfold-subst-shape-sym refl s = refl
actP-subst-shape : ∀ {ℓ} (F : Cosmos ℓ) {B C : Obj F} {s1 s2 : Shape F B}
                  → (g : Hom F B C) (eq : s1 ≡ s2)
                  → (p : Pos F (actS F g s1))
                  → actP F g s2 (subst (Pos F) (cong (actS F g) eq) p)
                    ≡ subst (Pos F) eq (actP F g s1 p)
actP-subst-shape F g refl p = refl
subst-≃⇒ℱ-src : ∀ {ℓ} {A₁ A₂ B : Cosmos ℓ} (eq : A₁ ≡ A₂)
              → (m₁ m₂ : A₁ ⇒ℱ B)
              → m₁ ≃⇒ℱ m₂
              → subst (λ A → A ⇒ℱ B) eq m₁ ≃⇒ℱ subst (λ A → A ⇒ℱ B) eq m₂
subst-≃⇒ℱ-src refl m₁ m₂ h = h
onPos-subst-pos-comm : ∀ {ℓ} {B C : Cosmos ℓ} (g : B ⇒ℱ C) {o1 o2 : Obj B} (eq : o1 ≡ o2) (s : Shape B o1) (p : Pos B s)
                      → subst (Pos C) (onShape-subst-comm g eq s) (onPos g (subst-pos B eq s p))
                        ≡ subst-pos C (cong (onObj g) eq) (onShape g s) (onPos g p)
onPos-subst-pos-comm g refl s p = refl
-- 从 onunfold-eq 导出的直接等价
-- 进一步的辅助引理
eqS-g'-step1 : ∀ (ℓ : Level) (B C : Cosmos ℓ) (g1 : B ⇒ℱ C)
               (O1 O2 : Obj B) (eqO-f : O1 ≡ O2)
               (S1 : Shape B O1) (S2 : Shape B O2)
               (eqS-f : S1 ≡ subst (Shape B) (sym eqO-f) S2)
             → onShape g1 S1 ≡ onShape g1 (subst (Shape B) (sym eqO-f) S2)
eqS-g'-step1 ℓ B C g1 O1 O2 eqO-f S1 S2 eqS-f = cong (onShape g1) eqS-f
eqS-g'-step2 : ∀ (ℓ : Level) (B C : Cosmos ℓ) (g1 : B ⇒ℱ C)
               (O1 O2 : Obj B) (eqO-f : O1 ≡ O2)
               (S2 : Shape B O2)
             → onShape g1 (subst (Shape B) (sym eqO-f) S2)
               ≡ subst (Shape C) (cong (onObj g1) (sym eqO-f)) (onShape g1 S2)
eqS-g'-step2 ℓ B C g1 O1 O2 eqO-f S2 = onShape-subst-comm g1 (sym eqO-f) S2
eqS-g'-step3 : ∀ (ℓ : Level) (B C : Cosmos ℓ) (g1 g2 : B ⇒ℱ C) (g-eq : g1 ≃⇒ℱ g2)
               (O2 : Obj B) (S2 : Shape B O2)
               (eqS-g : onShape g1 S2 ≡ subst (Shape C) (sym (onObj-eq g-eq O2)) (onShape g2 S2))
             → subst (Shape C) (cong (onObj g1) (sym refl)) (onShape g1 S2)
               ≡ subst (Shape C) (cong (onObj g1) (sym refl))
                   (subst (Shape C) (sym (onObj-eq g-eq O2)) (onShape g2 S2))
eqS-g'-step3 ℓ B C g1 g2 g-eq O2 S2 eqS-g =
  cong (subst (Shape C) (cong (onObj g1) (sym refl))) eqS-g
eqS-g'-step4 : ∀ (ℓ : Level) (C : Cosmos ℓ) (X Y Z : Obj C) (S : Shape C X) (eq1 : X ≡ Y) (eq2 : Y ≡ Z)
             → subst (Shape C) eq2 (subst (Shape C) eq1 S) ≡ subst (Shape C) (trans eq1 eq2) S
eqS-g'-step4 ℓ C X .X .X S refl refl = refl
eqS-g'-step5 : ∀ (ℓ : Level) (B C : Cosmos ℓ) (g1 g2 : B ⇒ℱ C) (O1 O2 : Obj B)
               (eqO-f : O1 ≡ O2) (eqO-g : onObj g1 O2 ≡ onObj g2 O2) →
               trans (sym eqO-g) (cong (onObj g1) (sym eqO-f)) ≡
               sym (trans (cong (onObj g1) eqO-f) eqO-g)
eqS-g'-step5 ℓ B C g1 g2 O1 O2 eqO-f eqO-g with eqO-f
... | refl = trans-reflʳ (sym eqO-g)
eqP-g'-step1 : ∀ (ℓ : Level) (B C : Cosmos ℓ) (g1 : B ⇒ℱ C)
                (O1 O2 : Obj B) (S1 : Shape B O1) (S2 : Shape B O2)
                (P1 : Pos B S1) (P2 : Pos B S2)
                (eqO-f : O1 ≡ O2)
                (eqS-f : S1 ≡ subst (Shape B) (sym eqO-f) S2)
                (eqP-f : P1 ≡ subst (Pos B) (sym eqS-f) (subst-pos B (sym eqO-f) S2 P2))
              → onPos g1 P1 ≡ subst (Pos C) (sym (cong (onShape g1) eqS-f))
                                 (onPos g1 (subst-pos B (sym eqO-f) S2 P2))
eqP-g'-step1 ℓ B C g1 O1 O2 S1 S2 P1 P2 eqO-f eqS-f eqP-f
  with eqO-f | eqS-f
... | refl | refl = cong (onPos g1) eqP-f
eqP-g'-step2 : ∀ (ℓ : Level) (B C : Cosmos ℓ) (g1 : B ⇒ℱ C)
               (O1 : Obj B) (S1 S2 : Shape B O1)
               (eqS-f : S1 ≡ subst (Shape B) (sym refl) S2)
               (P : Pos B (subst (Shape B) (sym refl) S2))
               → onPos g1 (subst (Pos B) (sym eqS-f) P)
               ≡ subst (Pos C) (cong (onShape g1) (sym eqS-f)) (onPos g1 P)
eqP-g'-step2 ℓ B C g1 O1 S1 S2 eqS-f P =
  begin
    onPos g1 (subst (Pos B) (sym eqS-f) P)
      ≡⟨ sym (subst-application′ (Pos B) (λ s → onPos g1 {A = O1} {s = s}) (sym eqS-f)) ⟩
    subst (λ s → Pos C (onShape g1 s)) (sym eqS-f) (onPos g1 P)
      ≡⟨ subst-∘ (sym eqS-f) ⟩
    subst (Pos C) (cong (onShape g1) (sym eqS-f)) (onPos g1 P)
  ∎
subst-pos-apply-g-eq : (ℓ : Level) (B C : Cosmos ℓ)
  (g1 g2 : B ⇒ℱ C) (g-eq : g1 ≃⇒ℱ g2)
  {O1 : Obj B} (O2 : Obj B) (eqO : O1 ≡ O2) (S2 : Shape B O2) (P2 : Pos B S2)
  → subst-pos C (cong (onObj g1) (sym eqO)) (onShape g1 S2) (onPos g1 P2)
    ≡ subst (Pos C)
        (sym
          (trans
            (cong (subst (Shape C) (cong (onObj g1) (sym eqO))) (onShape-eq g-eq S2))
            (subst-comp (sym (onObj-eq g-eq O2)) (cong (onObj g1) (sym eqO)))))
        (subst-pos C
          (trans (sym (onObj-eq g-eq O2)) (cong (onObj g1) (sym eqO)))
          (onShape g2 S2) (onPos g2 P2))
subst-pos-apply-g-eq ℓ B C g1 g2 g-eq {O1} O2 eqO S2 P2 =
  begin
    subst-pos C p-obj (onShape g1 S2) (onPos g1 P2)
      ≡⟨ cong (subst-pos C p-obj (onShape g1 S2)) (onPos-eq g-eq P2) ⟩
    subst-pos C p-obj (onShape g1 S2)
      (subst (Pos C) (sym eqS-g)
        (subst-pos C (sym eqO-g) (onShape g2 S2) (onPos g2 P2)))
      ≡⟨ subst-pos-cong C p-obj (sym eqS-g) ⟩
    subst (Pos C) (cong (subst (Shape C) p-obj) (sym eqS-g))
      (subst-pos C p-obj
        (subst (Shape C) (sym eqO-g) (onShape g2 S2))
        (subst-pos C (sym eqO-g) (onShape g2 S2) (onPos g2 P2)))
      ≡⟨ cong (subst (Pos C) (cong (subst (Shape C) p-obj) (sym eqS-g)))
               (subst-pos-trans ℓ C (sym eqO-g) p-obj (onShape g2 S2) (onPos g2 P2)) ⟩
    subst (Pos C) (cong (subst (Shape C) p-obj) (sym eqS-g))
      (subst (Pos C) (sym (subst-comp (sym eqO-g) p-obj))
        (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2)))
      ≡⟨ subst-comp (sym (subst-comp (sym eqO-g) p-obj)) (cong (subst (Shape C) p-obj) (sym eqS-g)) ⟩
    subst (Pos C) (trans
      (sym (subst-comp (sym eqO-g) p-obj))
      (cong (subst (Shape C) p-obj) (sym eqS-g)))
      (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2))
      ≡⟨ cong (λ p → subst (Pos C) p (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2)))
               path-eq-helper ⟩
    subst (Pos C)
      (sym
        (trans
          (cong (subst (Shape C) p-obj) eqS-g)
          (subst-comp (sym eqO-g) p-obj)))
      (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2))
  ∎
  where
    p-obj = cong (onObj g1) (sym eqO)
    eqO-g = onObj-eq g-eq O2
    eqS-g = onShape-eq g-eq S2
    cong-sym-helper : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) {x y : X} (p : x ≡ y)
                    → cong f (sym p) ≡ sym (cong f p)
    cong-sym-helper f refl = refl
    path-eq-helper : trans (sym (subst-comp (sym eqO-g) p-obj)) (cong (subst (Shape C) p-obj) (sym eqS-g))
                   ≡ sym (trans (cong (subst (Shape C) p-obj) eqS-g) (subst-comp (sym eqO-g) p-obj))
    path-eq-helper =
      begin
        trans (sym p2) (cong f (sym p1))
          ≡⟨ cong (trans (sym p2)) (cong-sym-helper f p1) ⟩
        trans (sym p2) (sym (cong f p1))
          ≡⟨ sym (sym-trans (cong f p1) p2) ⟩
        sym (trans (cong f p1) p2)
      ∎
      where
        p1 = eqS-g
        p2 = subst-comp (sym eqO-g) p-obj
        f = subst (Shape C) p-obj




{-
重要提示：
1. 上方代码已通过编译，无需修改无需重复输出直接复用
2. 下方证明要严格复用上方已完成的所有证明所遵循的强制要求
2.1 余归纳证明严格遵循Coinduction风格
2.2 严格遵循形态逐项对齐运输的核心范式
2.3 逐层展开对称对 → 结合律重排消去 → subst 运输对齐的方法论
注意：
以下函数必须严格按照其声明的显式/隐式参数顺序和方向使用，
否则类型检查器无法匹配，导致证明失败。
J : {A : Set a} {x : A} (B : (y : A) → x ≡ y → Set b)
    {y : A} (p : x ≡ y) → B x refl → B y p
J B refl b = b
trans-reflʳ : ∀ {x y : A} (p : x ≡ y) → trans p refl ≡ p
trans-reflʳ refl = refl
trans-assoc : ∀ {x y z u : A} (p : x ≡ y) {q : y ≡ z} {r : z ≡ u} →
  trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl = refl
trans-symˡ : ∀ {x y : A} (p : x ≡ y) → trans (sym p) p ≡ refl
trans-symˡ refl = refl
trans-symʳ : ∀ {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symʳ refl = refl
trans-injectiveˡ : ∀ {x y z : A} {p₁ p₂ : x ≡ y} (q : y ≡ z) →
                   trans p₁ q ≡ trans p₂ q → p₁ ≡ p₂
trans-injectiveˡ refl = subst₂ _≡_ (trans-reflʳ _) (trans-reflʳ _)
trans-injectiveʳ : ∀ {x y z : A} (p : x ≡ y) {q₁ q₂ : y ≡ z} →
                   trans p q₁ ≡ trans p q₂ → q₁ ≡ q₂
trans-injectiveʳ refl eq = eq
cong-id : ∀ {x y : A} (p : x ≡ y) → cong id p ≡ p
cong-id refl = refl
cong-∘ : ∀ {x y : A} {f : B → C} {g : A → B} (p : x ≡ y) →
         cong (f ∘ g) p ≡ cong f (cong g p)
cong-∘ refl = refl
sym-cong : ∀ {x y : A} {f : A → B} (p : x ≡ y) → sym (cong f p) ≡ cong f (sym p)
sym-cong refl = refl
trans-cong : ∀ {x y z : A} {f : A → B} (p : x ≡ y) {q : y ≡ z} →
             trans (cong f p) (cong f q) ≡ cong f (trans p q)
trans-cong refl = refl
cong₂-reflˡ : ∀ {_∙_ : A → B → C} {x u v} → (p : u ≡ v) →
              cong₂ _∙_ refl p ≡ cong (x ∙_) p
cong₂-reflˡ refl = refl
cong₂-reflʳ : ∀ {_∙_ : A → B → C} {x y u} → (p : x ≡ y) →
              cong₂ _∙_ p refl ≡ cong (_∙ u) p
cong₂-reflʳ refl = refl
cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl
cong′ : ∀ {f : A → B} x → f x ≡ f x
cong′ _ = refl
icong : ∀ {f : A → B} {x y} → x ≡ y → f x ≡ f y
icong = cong _
icong′ : ∀ {f : A → B} x → f x ≡ f x
icong′ _ = refl
cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl
cong-app : ∀ {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl
sym : Symmetric {A = A} _≡_
sym refl = refl
trans : Transitive {A = A} _≡_
trans refl eq = eq
subst : Substitutive {A = A} _≡_ ℓ
subst P refl p = p
subst₂ : ∀ (_∼_ : REL A B ℓ) {x y u v} → x ≡ y → u ≡ v → x ∼ u → y ∼ v
subst₂ _ refl refl p = p
-}


