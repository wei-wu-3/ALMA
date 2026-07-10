{-
ALMA Infinite Unbounded Dynamic Self-Referential Universe Mathematical Model
ALMA 无限无界动态自指涉宇宙数学模型

Possible extensions: MorphLift, Bisim, EvalH, EvalV, mapEvalH, mapEvalV, DynamicsStep, and various lemmas
可能的拓展方向： MorphLift Bisim EvalH EvalV mapEvalH mapEvalV DynamicsStep 与各种引理
-}
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.ProofOfConcept.Properties where

open import ALMA.ProofOfConcept.Cosmos public

-- Basic homotopy equations
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

-- Properties of subst on ⇒ℱ
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

-- Compatibility of subst with composition for ≃⇒ℱ
-- subst 与组合的 ≃⇒ℱ 相容性
subst-comp-⇒ℱ-both : ∀ {ℓ} {A B B' C : Cosmos ℓ} (p : B ≡ B')
  → (f : A ⇒ℱ B) (g : B ⇒ℱ C)
  → subst (λ D → D ⇒ℱ C) p g ∘⇒ℱ subst (λ D → A ⇒ℱ D) p f
    ≃⇒ℱ
    g ∘⇒ℱ f
subst-comp-⇒ℱ-both refl f g = refl-≃⇒ℱ

-- Auxiliary type aliases and equality constructors
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

-- Transport of Pos/Hom and related lemmas
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

-- Shape/position reasoning related to ≃⇒ℱ
-- ≃⇒ℱ 相关的形状/位置推理
eqSh-base-simp : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
                → (eqSh' : S1 ≡ subst (Shape G) refl S2')
                → S1 ≡ S2'
eqSh-base-simp {G = G} {O1} {S1} {S2'} eqSh' = 
  trans eqSh' (subst-refl-id (Shape G) S2')
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

-- Symmetrization of equations (reversing the evidence of ≃⇒ℱ)
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

-- Composition equations and paths
-- 组合等式与路径
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

-- Additional properties under MorphLift
-- MorphLift 下的额外性质
actP-subst-shape : ∀ {ℓ} (F : Cosmos ℓ) {B C : Obj F} {s1 s2 : Shape F B}
                  → (g : Hom F B C) (eq : s1 ≡ s2)
                  → (p : Pos F (actS F g s1))
                  → actP F g s2 (subst (Pos F) (cong (actS F g) eq) p)
                    ≡ subst (Pos F) eq (actP F g s1 p)
actP-subst-shape F g refl p = refl

-- Direct equivalences derived from onunfold-eq
-- 从 onunfold-eq 导出的直接等价
unfold-subst-shape : ∀ {ℓ} {C : Cosmos ℓ} {o₁ o₂ : Obj C} (eq : o₁ ≡ o₂) (s : Shape C o₁)
                  → unfold C (subst (Shape C) eq s) ≡ unfold C s
unfold-subst-shape refl s = refl
unfold-onShape-subst : ∀ {ℓ} (B C : Cosmos ℓ) (g : B ⇒ℱ C) {o1 o2 : Obj B} (eq : o1 ≡ o2) (s : Shape B o1)
                    → unfold C (onShape g (subst (Shape B) eq s)) ≡ unfold C (onShape g s)
unfold-onShape-subst B C g eq s =
  trans (cong (unfold C) (onShape-subst-comm g eq s))
        (unfold-subst-shape {C = C} (cong (onObj g) eq) (onShape g s))
onunfold-subst-comm : ∀ {ℓ} (B C : Cosmos ℓ) (g : B ⇒ℱ C) {o1 o2 : Obj B} (eq : o1 ≡ o2) (s : Shape B o1)
                    → onunfold g (subst (Shape B) eq s)
                      ≡ subst₂ (λ A C' → A ⇒ℱ C')
                              (sym (unfold-subst-shape {C = B} eq s))
                              (sym (unfold-onShape-subst B C g eq s))
                              (onunfold g s)
onunfold-subst-comm B C g refl s = refl
subst-∘-comm : ∀ {ℓ : Level} {S M1 M2 T1 T2 : Cosmos ℓ}
  (eqM : M2 ≡ M1) (eqT : T2 ≡ T1)
  (g : M2 ⇒ℱ T2) (f : S ⇒ℱ M2)
  → subst (λ D → M1 ⇒ℱ D) eqT (subst (λ M → M ⇒ℱ T2) eqM g)
    ∘⇒ℱ
    subst (λ D → S ⇒ℱ D) eqM f
    ≡
    subst (λ D → S ⇒ℱ D) eqT (g ∘⇒ℱ f)
subst-∘-comm refl refl g f = refl
transport-onunfold : ∀ {ℓ} {A B : Cosmos ℓ} {m₁ m₂ : A ⇒ℱ B} (m-eq : m₁ ≃⇒ℱ m₂)
                     (X : Obj A) (s : Shape A X)
                   → subst (λ C → unfold A s ⇒ℱ C)
                           (sym (trans (subst-unfold B (sym (onObj-eq m-eq X)) (onShape m₂ s))
                                       (cong (unfold B) (sym (onShape-eq m-eq s)))))
                           (onunfold m₁ s)
                     ≃⇒ℱ
                     onunfold m₂ s
transport-onunfold {ℓ} {A} {B} {m₁} {m₂} m-eq X s =
  let
    P : Cosmos ℓ → Set (lsuc ℓ)
    P C = unfold A s ⇒ℱ C
    thePath : unfold B (onShape m₂ s) ≡ unfold B (onShape m₁ s)
    thePath = trans (subst-unfold B (sym (onObj-eq m-eq X)) (onShape m₂ s))
                    (cong (unfold B) (sym (onShape-eq m-eq s)))
    eq0 : onunfold m₁ s ≃⇒ℱ subst P thePath (onunfold m₂ s)
    eq0 = onunfold-eq m-eq s
    eq1 : subst P (sym thePath) (onunfold m₁ s)
        ≃⇒ℱ subst P (sym thePath) (subst P thePath (onunfold m₂ s))
    eq1 = subst-≃⇒ℱ ℓ (unfold A s) _ _ (sym thePath) eq0
    subst-cancel : subst P (sym thePath) (subst P thePath (onunfold m₂ s))
                 ≡ onunfold m₂ s
    subst-cancel =
      begin
        subst P (sym thePath) (subst P thePath (onunfold m₂ s))
      ≡⟨ subst-comp thePath (sym thePath) ⟩
        subst P (trans thePath (sym thePath)) (onunfold m₂ s)
      ≡⟨ cong (λ e → subst P e (onunfold m₂ s)) (trans-symʳ thePath) ⟩
        subst P refl (onunfold m₂ s)
      ≡⟨ subst-refl-id P (onunfold m₂ s) ⟩
        onunfold m₂ s
      ∎
  in subst (λ n → subst P (sym thePath) (onunfold m₁ s) ≃⇒ℱ n) subst-cancel eq1
subst-≃⇒ℱ-path : ∀ {ℓ} {F C D : Cosmos ℓ} {m : F ⇒ℱ C}
                 {p q : C ≡ D}
               → p ≡ q
               → subst (λ X → F ⇒ℱ X) p m ≃⇒ℱ subst (λ X → F ⇒ℱ X) q m
subst-≃⇒ℱ-path refl = refl-≃⇒ℱ
subst-comp-⇒ℱ-tgt : ∀ {ℓ} {S M T1 T2 : Cosmos ℓ} (p : T1 ≡ T2)
  → (f : S ⇒ℱ M) (g : M ⇒ℱ T1)
  → subst (λ Y → M ⇒ℱ Y) p g ∘⇒ℱ f
    ≃⇒ℱ
    subst (λ Y → S ⇒ℱ Y) p (g ∘⇒ℱ f)
subst-comp-⇒ℱ-tgt refl f g = refl-≃⇒ℱ
subst-right-cancel-≃⇒ℱ : ∀ {ℓ} {F : Cosmos ℓ} {C D : Cosmos ℓ} (eq : C ≡ D)
                       → {m : F ⇒ℱ C} {n : F ⇒ℱ D}
                       → m ≃⇒ℱ subst (λ X → F ⇒ℱ X) (sym eq) n
                       → subst (λ X → F ⇒ℱ X) eq m ≃⇒ℱ n
subst-right-cancel-≃⇒ℱ refl h = h
subst₂-≃⇒ℱ : ∀ {ℓ} {A1 A2 B1 B2 : Cosmos ℓ} (pA : A1 ≡ A2) (pB : B1 ≡ B2)
  → {f g : A1 ⇒ℱ B1} → f ≃⇒ℱ g
  → subst₂ (λ X Y → X ⇒ℱ Y) pA pB f ≃⇒ℱ subst₂ (λ X Y → X ⇒ℱ Y) pA pB g
subst₂-≃⇒ℱ refl refl h = h
onunfold-subst-shape : ∀ {ℓ} {G H : Cosmos ℓ} {g : G ⇒ℱ H}
                       {O : Obj G} {s1 s2 : Shape G O}
                     → (p : s1 ≡ s2)
                     → onunfold g s1
                       ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B)
                                   (sym (cong (unfold G) p))
                                   (sym (cong (unfold H) (cong (onShape g) p)))
                                   (onunfold g s2)
onunfold-subst-shape refl = refl-≃⇒ℱ
comp-obj-eq : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  → f1 ≃⇒ℱ f2 → g1 ≃⇒ℱ g2
  → ∀ (X : Obj F) → onObj (g1 ∘⇒ℱ f1) X ≡ onObj (g2 ∘⇒ℱ f2) X
comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq X =
  trans (cong (onObj g1) (onObj-eq f-eq X)) (onObj-eq g-eq (onObj f2 X))
subst₂-⇒ℱ : ∀ {ℓ} {A1 A2 B1 B2 : Cosmos ℓ} (pA : A2 ≡ A1) (pB : B2 ≡ B1) (g : A2 ⇒ℱ B2)
  → subst₂ (λ A B → A ⇒ℱ B) pA pB g
    ≡ subst (λ D → A1 ⇒ℱ D) pB (subst (λ M → M ⇒ℱ B2) pA g)
subst₂-⇒ℱ refl refl g = refl
onunfold-shape-cong : ∀ {ℓ} {F G : Cosmos ℓ} {m : F ⇒ℱ G} {A} {s1 s2 : Shape F A}
  → (eq : s1 ≡ s2)
  → subst₂ (λ X Y → X ⇒ℱ Y) (cong (unfold F) eq) (cong (unfold G) (cong (onShape m) eq)) (onunfold m s1)
    ≡ onunfold m s2
onunfold-shape-cong refl = refl
subst₂-subst-right : ∀ {ℓ} {A2 A1 B2 B1 B3 : Cosmos ℓ}
  (x : A2 ⇒ℱ B2) (pA : A2 ≡ A1) (pB1 : B2 ≡ B1) (pB2 : B1 ≡ B3)
  → subst (λ B → A1 ⇒ℱ B) pB2 (subst₂ (λ A B → A ⇒ℱ B) pA pB1 x)
    ≡ subst₂ (λ A B → A ⇒ℱ B) pA (trans pB1 pB2) x
subst₂-subst-right x refl refl refl = refl
lemma-unfold-subst-shape-sym : ∀ {ℓ} (C : Cosmos ℓ) {o₁ o₂} (eq : o₁ ≡ o₂) (s : Shape C o₁)
  → sym (unfold-subst-shape {C = C} eq s) ≡ subst-unfold C eq s
lemma-unfold-subst-shape-sym C refl s = refl
subst-unfold-eq-conv : ∀ {ℓ} (C : Cosmos ℓ) {o1 o2 : Obj C}
  (eq1 eq2 : o1 ≡ o2) (s : Shape C o1) (eq : eq1 ≡ eq2)
  → trans (subst-unfold C eq1 s) (cong (unfold C) (cong (λ p → subst (Shape C) p s) eq))
  ≡ subst-unfold C eq2 s
subst-unfold-eq-conv C eq1 .eq1 s refl = trans-reflʳ (subst-unfold C eq1 s)
subst-unfold-shape-conv : ∀ {ℓ} (C : Cosmos ℓ) {o1 o2 : Obj C}
  (eq1 eq2 : o1 ≡ o2) (s : Shape C o1) (eq : eq1 ≡ eq2)
  {x : Shape C o2}
  (p1 : x ≡ subst (Shape C) eq1 s)
  (p2 : x ≡ subst (Shape C) eq2 s)
  (r : p2 ≡ trans p1 (cong (λ p → subst (Shape C) p s) eq))
  → trans (subst-unfold C eq1 s) (cong (unfold C) (sym p1))
  ≡ trans (subst-unfold C eq2 s) (cong (unfold C) (sym p2))
subst-unfold-shape-conv C eq1 eq2 s eq {x} p1 p2 r =
  let
    eq-sub : subst (Shape C) eq1 s ≡ subst (Shape C) eq2 s
    eq-sub = cong (λ p → subst (Shape C) p s) eq
    eq-sub-unfold : unfold C (subst (Shape C) eq1 s) ≡ unfold C (subst (Shape C) eq2 s)
    eq-sub-unfold = cong (unfold C) eq-sub
    h : trans (subst-unfold C eq1 s) eq-sub-unfold ≡ subst-unfold C eq2 s
    h = subst-unfold-eq-conv C eq1 eq2 s eq
    step1 : subst-unfold C eq1 s ≡ trans (subst-unfold C eq2 s) (sym eq-sub-unfold)
    step1 =
      begin
        subst-unfold C eq1 s
          ≡⟨ sym (trans-reflʳ (subst-unfold C eq1 s)) ⟩
        trans (subst-unfold C eq1 s) refl
          ≡⟨ cong (trans (subst-unfold C eq1 s)) (sym (trans-symʳ eq-sub-unfold)) ⟩
        trans (subst-unfold C eq1 s) (trans eq-sub-unfold (sym eq-sub-unfold))
          ≡⟨ sym (trans-assoc' (subst-unfold C eq1 s) eq-sub-unfold (sym eq-sub-unfold)) ⟩
        trans (trans (subst-unfold C eq1 s) eq-sub-unfold) (sym eq-sub-unfold)
          ≡⟨ cong (λ e → trans e (sym eq-sub-unfold)) h ⟩
        trans (subst-unfold C eq2 s) (sym eq-sub-unfold)
      ∎
    sym-p2-eq : sym p2 ≡ trans (sym eq-sub) (sym p1)
    sym-p2-eq =
      begin
        sym p2
          ≡⟨ cong sym r ⟩
        sym (trans p1 eq-sub)
          ≡⟨ sym-trans p1 eq-sub ⟩
        trans (sym eq-sub) (sym p1)
      ∎
    cong-unfold-eq : cong (unfold C) (sym p2)
                    ≡ trans (sym eq-sub-unfold) (cong (unfold C) (sym p1))
    cong-unfold-eq =
      begin
        cong (unfold C) (sym p2)
          ≡⟨ cong (cong (unfold C)) sym-p2-eq ⟩
        cong (unfold C) (trans (sym eq-sub) (sym p1))
          ≡⟨ cong-trans (unfold C) (sym eq-sub) (sym p1) ⟩
        trans (cong (unfold C) (sym eq-sub)) (cong (unfold C) (sym p1))
          ≡⟨ cong (λ e → trans e (cong (unfold C) (sym p1))) (cong-sym (unfold C) eq-sub) ⟩
        trans (sym eq-sub-unfold) (cong (unfold C) (sym p1))
      ∎
  in
  begin
    trans (subst-unfold C eq1 s) (cong (unfold C) (sym p1))
      ≡⟨ cong (λ e → trans e (cong (unfold C) (sym p1))) step1 ⟩
    trans (trans (subst-unfold C eq2 s) (sym eq-sub-unfold)) (cong (unfold C) (sym p1))
      ≡⟨ trans-assoc' (subst-unfold C eq2 s) (sym eq-sub-unfold) (cong (unfold C) (sym p1)) ⟩
    trans (subst-unfold C eq2 s) (trans (sym eq-sub-unfold) (cong (unfold C) (sym p1)))
      ≡⟨ cong (trans (subst-unfold C eq2 s)) (sym cong-unfold-eq) ⟩
    trans (subst-unfold C eq2 s) (cong (unfold C) (sym p2))
  ∎
shape-transport-lemma : ∀ {ℓ} {F G H : Cosmos ℓ}
  {f1 f2 : F ⇒ℱ G} (g1 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2)
  {A : Obj F} (s : Shape F A)
  → onShape g1 (onShape f1 s)
  ≡ subst (Shape H) (sym (cong (onObj g1) (onObj-eq f-eq A))) (onShape g1 (onShape f2 s))
shape-transport-lemma {ℓ} {F} {G} {H} {f1} {f2} g1 f-eq {A} s =
  trans
    (cong (onShape g1) (onShape-eq f-eq s))
    (trans
      (onShape-subst-comm g1 (sym (onObj-eq f-eq A)) (onShape f2 s))
      (cong (λ p → subst (Shape H) p (onShape g1 (onShape f2 s)))
            (cong-sym (onObj g1) (onObj-eq f-eq A))))
unfold-onShape-sym-lemma : ∀ {ℓ} {G H : Cosmos ℓ} (g : G ⇒ℱ H)
  {o₁ o₂ : Obj G} (eq : o₁ ≡ o₂) (s : Shape G o₁)
  → sym (unfold-onShape-subst G H g eq s)
  ≡ trans (subst-unfold H (cong (onObj g) eq) (onShape g s))
          (cong (unfold H) (sym (onShape-subst-comm g eq s)))
unfold-onShape-sym-lemma {ℓ} {G} {H} g {o₁} {o₂} eq s =
  let
    mid-shape : Shape H (onObj g o₂)
    mid-shape = subst (Shape H) (cong (onObj g) eq) (onShape g s)
    p : unfold H (onShape g (subst (Shape G) eq s)) ≡ unfold H mid-shape
    p = cong (unfold H) (onShape-subst-comm g eq s)
    q : unfold H mid-shape ≡ unfold H (onShape g s)
    q = unfold-subst-shape {C = H} (cong (onObj g) eq) (onShape g s)
    def : unfold-onShape-subst G H g eq s ≡ trans p q
    def = refl
  in
  begin
    sym (unfold-onShape-subst G H g eq s)
      ≡⟨ cong sym def ⟩
    sym (trans p q)
      ≡⟨ sym-trans p q ⟩
    trans (sym q) (sym p)
      ≡⟨ cong (λ e → trans e (sym p))
              (lemma-unfold-subst-shape-sym H (cong (onObj g) eq) (onShape g s)) ⟩
    trans (subst-unfold H (cong (onObj g) eq) (onShape g s)) (sym p)
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g) eq) (onShape g s)))
              (sym-cong {f = unfold H} (onShape-subst-comm g eq s)) ⟩
    trans (subst-unfold H (cong (onObj g) eq) (onShape g s))
          (cong (unfold H) (sym (onShape-subst-comm g eq s)))
  ∎
path-eq-target-lemma : ∀ {ℓ} {F G H : Cosmos ℓ}
  {f1 f2 : F ⇒ℱ G} (g1 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2)
  {A : Obj F} (s : Shape F A)
  → trans (sym (unfold-onShape-subst G H g1 (sym (onObj-eq f-eq A)) (onShape f2 s)))
          (sym (cong (unfold H) (cong (onShape g1) (onShape-eq f-eq s))))
  ≡ trans (subst-unfold H (sym (cong (onObj g1) (onObj-eq f-eq A))) (onShape g1 (onShape f2 s)))
          (cong (unfold H) (sym (shape-transport-lemma {F = F} {G = G} {H = H} g1 f-eq s)))
path-eq-target-lemma {ℓ} {F} {G} {H} {f1} {f2} g1 f-eq {A} s =
  let
    eqO = onObj-eq f-eq A
    eqS = onShape-eq f-eq s
    s2 = onShape f2 s
    mid-shape = onShape g1 s2
    a : onShape g1 (onShape f1 s) ≡ onShape g1 (subst (Shape G) (sym eqO) s2)
    a = cong (onShape g1) eqS
    b : onShape g1 (subst (Shape G) (sym eqO) s2) ≡ subst (Shape H) (cong (onObj g1) (sym eqO)) mid-shape
    b = onShape-subst-comm {G = G} {H = H} g1 (sym eqO) s2
    p1 : onShape g1 (onShape f1 s) ≡ subst (Shape H) (cong (onObj g1) (sym eqO)) mid-shape
    p1 = trans a b
    eq-p : cong (onObj g1) (sym eqO) ≡ sym (cong (onObj g1) eqO)
    eq-p = cong-sym (onObj g1) eqO
    eq-sub : subst (Shape H) (cong (onObj g1) (sym eqO)) mid-shape
           ≡ subst (Shape H) (sym (cong (onObj g1) eqO)) mid-shape
    eq-sub = cong (λ p → subst (Shape H) p mid-shape) eq-p
    shape-conv : shape-transport-lemma {F = F} {G = G} {H = H} g1 f-eq s ≡ trans p1 eq-sub
    shape-conv = sym (trans-assoc' a b eq-sub)
    p2 : onShape g1 (onShape f1 s) ≡ subst (Shape H) (sym (cong (onObj g1) eqO)) mid-shape
    p2 = shape-transport-lemma {F = F} {G = G} {H = H} g1 f-eq s
    p2' = sym b
    p3' = sym a
    shape-merge' : trans p2' p3' ≡ sym p1
    shape-merge' = sym (sym-trans a b)
    cong-unfold-merge : cong (unfold H) (trans p2' p3')
                      ≡ trans (cong (unfold H) p2') (cong (unfold H) p3')
    cong-unfold-merge = cong-trans (unfold H) p2' p3'
    h = unfold-onShape-subst G H g1 (sym eqO) s2
    q = unfold-subst-shape {C = H} (cong (onObj g1) (sym eqO)) mid-shape
    h-def : h ≡ trans (cong (unfold H) b) q
    h-def = refl
    sym-h-step1 : sym h ≡ trans (sym q) (sym (cong (unfold H) b))
    sym-h-step1 =
      begin
        sym h
          ≡⟨ cong sym h-def ⟩
        sym (trans (cong (unfold H) b) q)
          ≡⟨ sym-trans (cong (unfold H) b) q ⟩
        trans (sym q) (sym (cong (unfold H) b))
      ∎
    sym-q-eq : sym q ≡ subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape
    sym-q-eq = lemma-unfold-subst-shape-sym H (cong (onObj g1) (sym eqO)) mid-shape
    sym-cong-b : sym (cong (unfold H) b) ≡ cong (unfold H) (sym b)
    sym-cong-b = sym (cong-sym (unfold H) b)
    sym-cong-a : sym (cong (unfold H) a) ≡ cong (unfold H) (sym a)
    sym-cong-a = sym (cong-sym (unfold H) a)
    sym-h-final : sym h ≡ trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
                               (cong (unfold H) (sym b))
    sym-h-final =
      begin
        sym h
          ≡⟨ sym-h-step1 ⟩
        trans (sym q) (sym (cong (unfold H) b))
          ≡⟨ cong₂ trans sym-q-eq sym-cong-b ⟩
        trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
              (cong (unfold H) (sym b))
      ∎
  in
  begin
    trans (sym h) (sym (cong (unfold H) a))
      ≡⟨ cong (λ e → trans e (sym (cong (unfold H) a))) sym-h-final ⟩
    trans (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
                 (cong (unfold H) (sym b)))
          (sym (cong (unfold H) a))
      ≡⟨ trans-assoc' (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
                      (cong (unfold H) (sym b))
                      (sym (cong (unfold H) a)) ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (trans (cong (unfold H) (sym b)) (sym (cong (unfold H) a)))
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape))
              (cong (trans (cong (unfold H) (sym b))) sym-cong-a) ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (trans (cong (unfold H) (sym b)) (cong (unfold H) (sym a)))
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape))
              (sym cong-unfold-merge) ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (cong (unfold H) (trans p2' p3'))
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape))
              (cong (cong (unfold H)) shape-merge') ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (cong (unfold H) (sym p1))
      ≡⟨ subst-unfold-shape-conv H
           (cong (onObj g1) (sym eqO))
           (sym (cong (onObj g1) eqO))
           mid-shape eq-p
           p1 p2 shape-conv ⟩
    trans (subst-unfold H (sym (cong (onObj g1) eqO)) mid-shape)
          (cong (unfold H) (sym p2))
  ∎
path-eq-source-lemma : ∀ {ℓ} {G : Cosmos ℓ} {o₁ o₂ : Obj G}
  (eqO : o₁ ≡ o₂) {s₁ : Shape G o₁} {s₂ : Shape G o₂}
  (eqS : s₁ ≡ subst (Shape G) (sym eqO) s₂)
  → trans (sym (unfold-subst-shape {C = G} (sym eqO) s₂))
          (sym (cong (unfold G) eqS))
  ≡ trans (subst-unfold G (sym eqO) s₂)
          (cong (unfold G) (sym eqS))
path-eq-source-lemma {ℓ} {G} {o₁} {o₂} eqO {s₁} {s₂} eqS =
  cong₂ trans
    (lemma-unfold-subst-shape-sym G (sym eqO) s₂)
    (sym-cong {f = unfold G {o₁}} eqS)
subst₂-comp-≃⇒ℱ : ∀ {ℓ} {S M1 M2 T1 T2 : Cosmos ℓ}
  (eqM : M2 ≡ M1) (eqT : T2 ≡ T1)
  (g : M2 ⇒ℱ T2) (f : S ⇒ℱ M2)
  → (subst₂ (λ A B → A ⇒ℱ B) eqM eqT g) ∘⇒ℱ (subst (λ C → S ⇒ℱ C) eqM f)
    ≃⇒ℱ
    subst (λ C → S ⇒ℱ C) eqT (g ∘⇒ℱ f)
subst₂-comp-≃⇒ℱ {S = S} eqM eqT g f =
  ≡→≃⇒ℱ $
    trans
      (cong (λ g' → g' ∘⇒ℱ subst (λ C → S ⇒ℱ C) eqM f) (subst₂-⇒ℱ eqM eqT g))
      (subst-∘-comm eqM eqT g f)
onObj-cong-≡ : ∀ {ℓ} {S T : Cosmos ℓ} {h1 h2 : S ⇒ℱ T} {X : Obj S}
             → h1 ≡ h2 → onObj h1 X ≡ onObj h2 X
onObj-cong-≡ refl = refl
subst-∘⇒ℱ-comm : ∀ {ℓ} {S M T1 T2 : Cosmos ℓ}
                → (p : T2 ≡ T1)
                → (f : S ⇒ℱ M)
                → (g : M ⇒ℱ T2)
                → subst (λ C → M ⇒ℱ C) p g ∘⇒ℱ f
                  ≡ subst (λ C → S ⇒ℱ C) p (g ∘⇒ℱ f)
subst-∘⇒ℱ-comm refl f g = refl
subst₂-trans : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
  {x1 x2 x3 : A} {y1 y2 y3 : B}
  (p1 : x1 ≡ x2) (p2 : x2 ≡ x3)
  (q1 : y1 ≡ y2) (q2 : y2 ≡ y3)
  (z : P x1 y1)
  → subst₂ P p2 q2 (subst₂ P p1 q1 z) ≡ subst₂ P (trans p1 p2) (trans q1 q2) z
subst₂-trans refl p2 refl q2 z = refl
onHom-subst-comm : ∀ {ℓ} {G H : Cosmos ℓ} (g : G ⇒ℱ H)
                   (X Y X' Y' : Obj G) (p : X ≡ X') (q : Y ≡ Y') (f : Hom G X Y)
                 → onHom g (subst₂ (Hom G) p q f)
                   ≡ subst₂ (Hom H) (cong (onObj g) p) (cong (onObj g) q) (onHom g f)
onHom-subst-comm g X Y .X .Y refl refl f = refl
subst-pos-obj : ∀ {ℓ} {F : Cosmos ℓ} {X Y : Obj F}
  (p : X ≡ Y) {s : Shape F Y} (pos : Pos F s)
  → Pos F (subst (Shape F) (sym p) s)
subst-pos-obj refl pos = pos
subst-hom-obj : ∀ {ℓ} {F : Cosmos ℓ} {X1 X2 Y1 Y2 : Obj F}
  (pX : X1 ≡ X2) (pY : Y1 ≡ Y2) {h : Hom F X2 Y2}
  → Hom F X1 Y1
subst-hom-obj refl refl {h} = h
subst-pos-onPos : ∀ {ℓ} {F G : Cosmos ℓ} (g : F ⇒ℱ G)
  → ∀ {X Y : Obj F} (p : X ≡ Y) (s : Shape F X) (pos : Pos F s)
  → subst (Pos G) (onShape-subst-comm g p s) (onPos g (subst-pos F p s pos))
    ≡ subst-pos G (cong (onObj g) p) (onShape g s) (onPos g pos)
subst-pos-onPos g refl s pos = refl
pos-proof : ∀ {ℓ} {S' S1 H : Cosmos ℓ} {f1 f2 : S' ⇒ℱ S1}
            (g : S1 ⇒ℱ H) (f-eq : f1 ≃⇒ℱ f2)
            {X : Obj S'} {s : Shape S' X} (pos : Pos S' s) →
            onPos g (onPos f1 pos) ≡
            subst (Pos H) (sym (shape-transport-lemma g f-eq s))
              (subst-pos H (sym (cong (onObj g) (f-eq .onObj-eq X)))
                (onShape g (onShape f2 s))
                (onPos g (onPos f2 pos)))
pos-proof {ℓ} {S'} {S1} {H} {f1} {f2} g f-eq {X} {s} pos = final
  where
    obj-eq   = f-eq .onObj-eq X
    shape-eq = f-eq .onShape-eq s
    s2       = onShape f2 s
    p2       = onPos f2 pos
    inner-pos = subst-pos S1 (sym obj-eq) s2 p2
    total-obj = cong (onObj g) obj-eq
    shape-eq' = onShape-subst-comm g (sym obj-eq) s2
    shape-comp-eq = shape-transport-lemma g f-eq s
    step3-shape : subst (Shape H) (cong (onObj g) (sym obj-eq)) (onShape g s2)
                ≡ subst (Shape H) (sym total-obj) (onShape g s2)
    step3-shape = cong (λ p → subst (Shape H) p (onShape g s2))
                       (cong-sym (onObj g) obj-eq)
    C1 = subst-pos H (cong (onObj g) (sym obj-eq)) (onShape g s2) (onPos g p2)
    C2 = subst-pos H (sym total-obj) (onShape g s2) (onPos g p2)
    step3-C-eq : subst (Pos H) step3-shape C1 ≡ C2
    step3-C-eq = subst-pos-eq H (onPos g p2) (cong-sym (onObj g) obj-eq)
    eq2 : subst (Pos H) shape-eq' (onPos g inner-pos) ≡ C1
    eq2 = subst-pos-onPos g (sym obj-eq) s2 p2
    eq3 : onPos g inner-pos ≡ subst (Pos H) (sym shape-eq') C1
    eq3 =
      begin
        onPos g inner-pos
          ≡⟨ refl ⟩
        subst (Pos H) refl (onPos g inner-pos)
          ≡⟨ cong (λ p → subst (Pos H) p (onPos g inner-pos))
                  (sym (trans-symʳ shape-eq')) ⟩
        subst (Pos H) (trans shape-eq' (sym shape-eq')) (onPos g inner-pos)
          ≡⟨ sym (subst-comp shape-eq' (sym shape-eq')) ⟩
        subst (Pos H) (sym shape-eq') (subst (Pos H) shape-eq' (onPos g inner-pos))
          ≡⟨ cong (subst (Pos H) (sym shape-eq')) eq2 ⟩
        subst (Pos H) (sym shape-eq') C1
      ∎
    step1      = cong (onPos g) (f-eq .onPos-eq pos)
    step2      = onPos-subst-comm g (sym shape-eq) inner-pos
    step3-cast = cong (subst (Pos H) (cong (onShape g) (sym shape-eq))) eq3
    step4-merge = subst-comp (sym shape-eq') (cong (onShape g) (sym shape-eq))
    P = trans (sym shape-eq') (cong (onShape g) (sym shape-eq))
    step5 : onPos g (onPos f1 pos) ≡ subst (Pos H) P C1
    step5 = trans step1 (trans step2 (trans step3-cast step4-merge))
    path-eq : trans step3-shape (sym shape-comp-eq) ≡ P
    path-eq =
      begin
        trans step3-shape (sym shape-comp-eq)
          ≡⟨ cong (trans step3-shape)
                  (sym-trans (cong (onShape g) shape-eq)
                             (trans shape-eq' step3-shape)) ⟩
        trans step3-shape
              (trans (sym (trans shape-eq' step3-shape))
                     (sym (cong (onShape g) shape-eq)))
          ≡⟨ cong (trans step3-shape)
                  (cong (λ q → trans q (sym (cong (onShape g) shape-eq)))
                        (sym-trans shape-eq' step3-shape)) ⟩
        trans step3-shape
              (trans (trans (sym step3-shape) (sym shape-eq'))
                     (sym (cong (onShape g) shape-eq)))
          ≡⟨ sym (trans-assoc step3-shape) ⟩
        trans (trans step3-shape (trans (sym step3-shape) (sym shape-eq')))
              (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (λ q → trans q (sym (cong (onShape g) shape-eq)))
                  (sym (trans-assoc step3-shape)) ⟩
        trans (trans (trans step3-shape (sym step3-shape)) (sym shape-eq'))
              (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (λ q → trans (trans q (sym shape-eq'))
                               (sym (cong (onShape g) shape-eq)))
                  (trans-symʳ step3-shape) ⟩
        trans (trans refl (sym shape-eq'))
              (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (λ q → trans q (sym (cong (onShape g) shape-eq)))
                  (transReflˡ (sym shape-eq')) ⟩
        trans (sym shape-eq') (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (trans (sym shape-eq')) (sym (cong-sym (onShape g) shape-eq)) ⟩
        trans (sym shape-eq') (cong (onShape g) (sym shape-eq))
          ≡⟨ refl ⟩
        P
      ∎
    step6 : subst (Pos H) P C1 ≡ subst (Pos H) (sym shape-comp-eq) C2
    step6 =
      begin
        subst (Pos H) P C1
          ≡⟨ cong (λ p → subst (Pos H) p C1) (sym path-eq) ⟩
        subst (Pos H) (trans step3-shape (sym shape-comp-eq)) C1
            ≡⟨ sym (subst-comp {A = Shape H (onObj g (onObj f1 X))} {B = Pos H} step3-shape (sym shape-comp-eq) {b = C1}) ⟩
        subst (Pos H) (sym shape-comp-eq) (subst (Pos H) step3-shape C1)
          ≡⟨ cong (subst (Pos H) (sym shape-comp-eq)) step3-C-eq ⟩
        subst (Pos H) (sym shape-comp-eq) C2
      ∎
    final = trans step5 step6
hom-proof : ∀ {ℓ} {S' S1 H : Cosmos ℓ} {f1 f2 : S' ⇒ℱ S1}
            (g : S1 ⇒ℱ H) (f-eq : f1 ≃⇒ℱ f2)
            {X Y : Obj S'} (h : Hom S' X Y) →
            onHom g (onHom f1 h) ≡
            subst₂ (Hom H) (sym (cong (onObj g) (f-eq .onObj-eq X)))
                           (sym (cong (onObj g) (f-eq .onObj-eq Y)))
                           (onHom g (onHom f2 h))
hom-proof {ℓ} {S'} {S1} {H} {f1} {f2} g f-eq {X} {Y} h =
  let
    objX  = f-eq .onObj-eq X
    objY  = f-eq .onObj-eq Y
    hom-eq = f-eq .onHom-eq h
    step1  = cong (onHom g) hom-eq
    step2  = onHom-subst-comm g (onObj f2 X) (onObj f2 Y) (onObj f1 X) (onObj f1 Y)
              (sym objX) (sym objY) (onHom f2 h)
    step3  = cong₂ (λ p q → subst₂ (Hom H) p q (onHom g (onHom f2 h)))
                   (cong-sym (onObj g) objX)
                   (cong-sym (onObj g) objY)
  in trans step1 (trans step2 step3)
subst₂-tgt-merge : ∀ {ℓ} {A A' B B' B'' : Cosmos ℓ}
                   (p : A ≡ A') (r : B ≡ B') (q : B' ≡ B'') (f : A ⇒ℱ B)
                 → subst₂ _⇒ℱ_ p q (subst (λ C → A ⇒ℱ C) r f)
                   ≡ subst₂ _⇒ℱ_ p (trans r q) f
subst₂-tgt-merge refl refl refl f = refl
comp-standard-unfold-path : ∀ {ℓ} {C : Cosmos ℓ} {o1 o2 o3 : Obj C}
  (p12 : o1 ≡ o2) {s1 : Shape C o1} {s2 : Shape C o2} (eq12 : s2 ≡ subst (Shape C) p12 s1)
  (p23 : o2 ≡ o3) {s3 : Shape C o3} (eq23 : s3 ≡ subst (Shape C) p23 s2)
  → trans
      (trans (subst-unfold C p12 s1) (cong (unfold C) (sym eq12)))
      (trans (subst-unfold C p23 s2) (cong (unfold C) (sym eq23)))
    ≡ trans
      (subst-unfold C (trans p12 p23) s1)
      (cong (unfold C) (sym (trans eq23 (trans (cong (subst (Shape C) p23) eq12) (subst-comp p12 p23 {b = s1})))))
comp-standard-unfold-path refl refl refl refl = refl
comp-cong-r-≃⇒ℱ-gen : ∀ {ℓ} {S S' T1 T2 : Cosmos ℓ}
  {g1 : S ⇒ℱ T1} {g2 : S ⇒ℱ T2}
  (p : T2 ≡ T1)
  (g-eq : g1 ≃⇒ℱ subst (λ C → S ⇒ℱ C) p g2)
  (f : S' ⇒ℱ S)
  → g1 ∘⇒ℱ f ≃⇒ℱ subst (λ C → S' ⇒ℱ C) p (g2 ∘⇒ℱ f)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onObj-eq X   = g-eq .onObj-eq (onObj f X)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onShape-eq s = g-eq .onShape-eq (onShape f s)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onPos-eq pos = g-eq .onPos-eq (onPos f pos)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onHom-eq h   = g-eq .onHom-eq (onHom f h)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onunfold-eq s =
  comp-cong-r-≃⇒ℱ-gen
    _
    (g-eq .onunfold-eq (onShape f s))
    (onunfold f s)
comp-cong-r-≃⇒ℱ : ∀ {ℓ} {F G H : Cosmos ℓ}
  {g1 g2 : G ⇒ℱ H} (g-eq : g1 ≃⇒ℱ g2)
  (f : F ⇒ℱ G)
  → (g1 ∘⇒ℱ f) ≃⇒ℱ (g2 ∘⇒ℱ f)
comp-cong-r-≃⇒ℱ g-eq f = comp-cong-r-≃⇒ℱ-gen refl g-eq f

comp-cong-≃⇒ℱ : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
              → f1 ≃⇒ℱ f2 → g1 ≃⇒ℱ g2
              → (g1 ∘⇒ℱ f1) ≃⇒ℱ (g2 ∘⇒ℱ f2)
sym-trans-cong-sym : ∀ {ℓ} (F G H : Cosmos ℓ)
                   (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
                   (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
                   (X : Obj F)
                 → trans (sym (g-eq .onObj-eq (onObj f2 X)))
                         (cong (onObj g1) (sym (f-eq .onObj-eq X)))
                 ≡ sym (trans (cong (onObj g1) (f-eq .onObj-eq X))
                              (g-eq .onObj-eq (onObj f2 X)))
sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq X =
  let eqO-f = f-eq .onObj-eq X
      eqO-g = g-eq .onObj-eq (onObj f2 X)
  in
  begin
    trans (sym eqO-g) (cong (onObj g1) (sym eqO-f))
      ≡⟨ cong (trans (sym eqO-g)) (cong-sym (onObj g1) eqO-f) ⟩
    trans (sym eqO-g) (sym (cong (onObj g1) eqO-f))
      ≡⟨ sym (sym-trans (cong (onObj g1) eqO-f) eqO-g) ⟩
    sym (trans (cong (onObj g1) eqO-f) eqO-g)
  ∎
comp-shape-eq : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
  {A : Obj F} (s : Shape F A)
  → onShape (g1 ∘⇒ℱ f1) s ≡ subst (Shape H) (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A)) (onShape (g2 ∘⇒ℱ f2) s)
comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq {A} s =
  let
    eqO : onObj f1 A ≡ onObj f2 A
    eqO = onObj-eq f-eq A
    eqS : onShape f1 s ≡ subst (Shape G) (sym eqO) (onShape f2 s)
    eqS = onShape-eq f-eq s
    eqO-total = comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A
    final-path-eq : trans (sym (onObj-eq g-eq (onObj f2 A))) (cong (onObj g1) (sym eqO)) ≡ sym eqO-total
    final-path-eq = sym-trans-cong-sym F G H f1 f2 g1 g2 f-eq g-eq A
  in
  begin
    onShape g1 (onShape f1 s)
      ≡⟨ cong (onShape g1) eqS ⟩
    onShape g1 (subst (Shape G) (sym eqO) (onShape f2 s))
      ≡⟨ onShape-subst-comm g1 (sym eqO) (onShape f2 s) ⟩
    subst (Shape H) (cong (onObj g1) (sym eqO)) (onShape g1 (onShape f2 s))
      ≡⟨ cong (subst (Shape H) (cong (onObj g1) (sym eqO))) (onShape-eq g-eq (onShape f2 s)) ⟩
    subst (Shape H) (cong (onObj g1) (sym eqO))
          (subst (Shape H) (sym (onObj-eq g-eq (onObj f2 A))) (onShape g2 (onShape f2 s)))
      ≡⟨ subst-comp (sym (onObj-eq g-eq (onObj f2 A))) (cong (onObj g1) (sym eqO)) ⟩
    subst (Shape H) (trans (sym (onObj-eq g-eq (onObj f2 A))) (cong (onObj g1) (sym eqO)))
          (onShape g2 (onShape f2 s))
      ≡⟨ cong (λ p → subst (Shape H) p (onShape g2 (onShape f2 s))) final-path-eq ⟩
    subst (Shape H) (sym eqO-total) (onShape g2 (onShape f2 s))
  ∎
comp-unfold-path : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
  {A : Obj F} (s : Shape F A)
  → unfold H (onShape (g2 ∘⇒ℱ f2) s) ≡ unfold H (onShape (g1 ∘⇒ℱ f1) s)
comp-unfold-path F G H f1 f2 g1 g2 f-eq g-eq {A} s =
  trans
    (subst-unfold H (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A)) (onShape (g2 ∘⇒ℱ f2) s))
    (cong (unfold H) (sym (comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s)))
apply-g-eq-to-substed-pos : (ℓ : Level) (B C : Cosmos ℓ)
                          → (g1 g2 : B ⇒ℱ C)
                          → (O1 O2 : Obj B) (eqO : O1 ≡ O2)
                          → (S1 : Shape B O1) (S2 : Shape B O2) (eqS : S1 ≡ subst (Shape B) (sym eqO) S2)
                          → (P1 : Pos B S1) (P2 : Pos B S2)
                          → (eqP : P1 ≡ subst (Pos B) (sym eqS) (subst-pos B (sym eqO) S2 P2))
                          → onPos g1 P1
                            ≡ subst (Pos C)
                                (trans (sym (onShape-subst-comm g1 (sym eqO) S2)) (cong (onShape g1) (sym eqS)))
                                (subst-pos C
                                  (cong (onObj g1) (sym eqO))
                                  (onShape g1 S2)
                                  (onPos g1 P2))
apply-g-eq-to-substed-pos ℓ B C g1 g2 O1 O2 eqO S1 S2 eqS P1 P2 eqP =
  J (λ O2' eqO' →
       ∀ (S2' : Shape B O2') (eqS' : S1 ≡ subst (Shape B) (sym eqO') S2')
         (P2' : Pos B S2') (eqP' : P1 ≡ subst (Pos B) (sym eqS') (subst-pos B (sym eqO') S2' P2')) →
       onPos g1 P1
       ≡ subst (Pos C)
           (trans (sym (onShape-subst-comm g1 (sym eqO') S2')) (cong (onShape g1) (sym eqS')))
           (subst-pos C (cong (onObj g1) (sym eqO')) (onShape g1 S2') (onPos g1 P2')))
    eqO
    (λ S2' eqS' P2' eqP' →
       let
         goal : onPos g1 P1 ≡ subst (Pos C) (cong (onShape g1) (sym eqS')) (onPos g1 P2')
         goal =
           begin
             onPos g1 P1
           ≡⟨ cong (onPos g1) eqP' ⟩
             onPos g1 (subst (Pos B) (sym eqS') P2')
           ≡⟨ onPos-subst-comm g1 (sym eqS') P2' ⟩
             subst (Pos C) (cong (onShape g1) (sym eqS')) (onPos g1 P2')
           ∎
       in goal)
    S2 eqS P2 eqP
subst-pos-eq-cong : ∀ {ℓ} {C : Cosmos ℓ} {O O' : Obj C} {p q : O ≡ O'}
  → (e : p ≡ q) (S : Shape C O) (x : Pos C S)
  → subst (Pos C) (cong (λ r → subst (Shape C) r S) e) (subst-pos C p S x)
    ≡ subst-pos C q S x
subst-pos-eq-cong refl S x = refl
subst-pos-trans : (ℓ : Level) (C : Cosmos ℓ) {O O' O'' : Obj C}
                → (eqA : O ≡ O') (eqB : O' ≡ O'') (S : Shape C O) (p : Pos C S)
                → subst-pos C eqB (subst (Shape C) eqA S) (subst-pos C eqA S p)
                  ≡ subst (Pos C) (sym (subst-comp eqA eqB {b = S}))
                          (subst-pos C (trans eqA eqB) S p)
subst-pos-trans ℓ C refl refl S p = refl
subst-pos-cong : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} (eqO : X ≡ Y) {S S' : Shape C X} (eqS : S ≡ S') {p : Pos C S}
               → subst-pos C eqO S' (subst (Pos C) eqS p) 
               ≡ subst (Pos C) (cong (subst (Shape C) eqO) eqS) (subst-pos C eqO S p)
subst-pos-cong C eqO refl {p} = refl
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
subst-comp-tgt : ∀ {ℓ} {A B C1 C2 : Cosmos ℓ} (eq : C1 ≡ C2)
                → (f : A ⇒ℱ B) (g : B ⇒ℱ C1)
                → subst (λ C → A ⇒ℱ C) eq (g ∘⇒ℱ f)
                  ≡ subst (λ C → B ⇒ℱ C) eq g ∘⇒ℱ f
subst-comp-tgt refl f g = refl
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onObj-eq X =
  comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq X
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onShape-eq {A} s =
  comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onPos-eq {A} {s} p =
  let
    O1f : Obj G
    O1f = onObj f1 A
    O2f : Obj G
    O2f = onObj f2 A
    eqO-f : O1f ≡ O2f
    eqO-f = onObj-eq f-eq A
    S1f : Shape G O1f
    S1f = onShape f1 s
    S2f : Shape G O2f
    S2f = onShape f2 s
    eqS-f : S1f ≡ subst (Shape G) (sym eqO-f) S2f
    eqS-f = onShape-eq f-eq s
    P1f : Pos G S1f
    P1f = onPos f1 p
    P2f : Pos G S2f
    P2f = onPos f2 p
    eqP-f : P1f ≡ subst (Pos G) (sym eqS-f) (subst-pos G (sym eqO-f) S2f P2f)
    eqP-f = onPos-eq f-eq p
    O1g : Obj H
    O1g = onObj g1 O1f
    O2g : Obj H
    O2g = onObj g2 O2f
    eqO-g : onObj g1 O2f ≡ O2g
    eqO-g = onObj-eq g-eq O2f
    p-obj : onObj g1 O2f ≡ O1g
    p-obj = cong (onObj g1) (sym eqO-f)
    S1g : Shape H O1g
    S1g = onShape g1 S1f
    S2g : Shape H O2g
    S2g = onShape g2 S2f
    P2g : Pos H S2g
    P2g = onPos g2 P2f
    eqO-total : O1g ≡ O2g
    eqO-total = trans (cong (onObj g1) eqO-f) (onObj-eq g-eq O2f)
    eqS-total : S1g ≡ subst (Shape H) (sym eqO-total) S2g
    eqS-total = comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
    final-path-eq : trans (sym eqO-g) p-obj ≡ sym eqO-total
    final-path-eq = sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq A
    shape-endpoint-eq : subst (Shape H) (trans (sym eqO-g) p-obj) S2g ≡ subst (Shape H) (sym eqO-total) S2g
    shape-endpoint-eq = cong (λ q → subst (Shape H) q S2g) final-path-eq
    step1-shape : S1g ≡ onShape g1 (subst (Shape G) (sym eqO-f) S2f)
    step1-shape = cong (onShape g1) eqS-f
    step2-shape : onShape g1 (subst (Shape G) (sym eqO-f) S2f)
                ≡ subst (Shape H) p-obj (onShape g1 S2f)
    step2-shape = onShape-subst-comm g1 (sym eqO-f) S2f
    step3-shape : subst (Shape H) p-obj (onShape g1 S2f)
                ≡ subst (Shape H) p-obj (subst (Shape H) (sym eqO-g) S2g)
    step3-shape = cong (subst (Shape H) p-obj) (onShape-eq g-eq S2f)
    step4-shape : subst (Shape H) p-obj (subst (Shape H) (sym eqO-g) S2g)
                ≡ subst (Shape H) (trans (sym eqO-g) p-obj) S2g
    step4-shape = subst-comp (sym eqO-g) p-obj {b = S2g}
    path-shape : subst (Shape H) (trans (sym eqO-g) p-obj) S2g ≡ S1g
    path-shape = trans (sym step4-shape)
               (trans (sym step3-shape)
                (trans (sym step2-shape) (sym step1-shape)))
    eqS-unfold : eqS-total ≡ trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))
    eqS-unfold =
      begin
        eqS-total
          ≡⟨ cong (λ p → trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape p))))
                  (trans-reflʳ shape-endpoint-eq) ⟩
        trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))
      ∎
    path-shape-lemma : path-shape ≡ trans shape-endpoint-eq (sym eqS-total)
    path-shape-lemma = sym (begin
      trans shape-endpoint-eq (sym eqS-total)
        ≡⟨ cong (trans shape-endpoint-eq) (cong sym eqS-unfold) ⟩
      trans shape-endpoint-eq (sym (trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))))
        ≡⟨ cong (trans shape-endpoint-eq)
                (sym-trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (sym (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))) (sym step1-shape))
        ≡⟨ cong (trans shape-endpoint-eq)
                (cong (λ p → trans p (sym step1-shape))
                  (sym-trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (trans (sym (trans step3-shape (trans step4-shape shape-endpoint-eq))) (sym step2-shape)) (sym step1-shape))
        ≡⟨ cong (trans shape-endpoint-eq)
                (cong (λ p → trans p (sym step1-shape))
                  (cong (λ p → trans p (sym step2-shape))
                    (sym-trans step3-shape (trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (trans (trans (sym (trans step4-shape shape-endpoint-eq)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape))
        ≡⟨ cong (trans shape-endpoint-eq)
                (cong (λ p → trans p (sym step1-shape))
                  (cong (λ p → trans p (sym step2-shape))
                    (cong (λ p → trans p (sym step3-shape))
                      (sym-trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (trans (trans (trans (sym shape-endpoint-eq) (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape))
        ≡⟨ sym (trans-assoc shape-endpoint-eq) ⟩
      trans (trans shape-endpoint-eq (trans (trans (trans (sym shape-endpoint-eq) (sym step4-shape)) (sym step3-shape)) (sym step2-shape))) (sym step1-shape)
        ≡⟨ cong (λ p → trans p (sym step1-shape)) (sym (trans-assoc shape-endpoint-eq)) ⟩
      trans (trans (trans shape-endpoint-eq (trans (trans (sym shape-endpoint-eq) (sym step4-shape)) (sym step3-shape))) (sym step2-shape)) (sym step1-shape)
        ≡⟨ cong (λ p → trans (trans p (sym step2-shape)) (sym step1-shape)) (sym (trans-assoc shape-endpoint-eq)) ⟩
      trans (trans (trans (trans shape-endpoint-eq (trans (sym shape-endpoint-eq) (sym step4-shape))) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ cong (λ p → trans (trans (trans p (sym step3-shape)) (sym step2-shape)) (sym step1-shape)) (sym (trans-assoc shape-endpoint-eq)) ⟩
      trans (trans (trans (trans (trans shape-endpoint-eq (sym shape-endpoint-eq)) (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ cong (λ p → trans (trans (trans (trans p (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)) (trans-symʳ shape-endpoint-eq) ⟩
      trans (trans (trans (trans refl (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ refl ⟩
      trans (trans (trans (sym step4-shape) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ trans-assoc (trans (sym step4-shape) (sym step3-shape)) ⟩
      trans (trans (sym step4-shape) (sym step3-shape)) (trans (sym step2-shape) (sym step1-shape))
        ≡⟨ trans-assoc (sym step4-shape) ⟩
      trans (sym step4-shape) (trans (sym step3-shape) (trans (sym step2-shape) (sym step1-shape)))
        ≡⟨ refl ⟩
      path-shape
      ∎)
    pos1 : Pos G S1f
    pos1 = subst (Pos G) (sym eqS-f) (subst-pos G (sym eqO-f) S2f P2f)
    pos2 : Pos H (subst (Shape H) p-obj (onShape g1 S2f))
    pos2 = subst-pos H p-obj (onShape g1 S2f) (onPos g1 P2f)
    pos3 : Pos H (subst (Shape H) p-obj (onShape g1 S2f))
    pos3 = subst-pos H p-obj (onShape g1 S2f)
             (subst (Pos H) (sym (onShape-eq g-eq S2f))
               (subst-pos H (sym eqO-g) S2g P2g))
    path4-lemma : cong (onShape g1) (sym eqS-f) ≡ sym step1-shape
    path4-lemma = sym (sym-cong eqS-f)
    path3-lemma : trans (sym step4-shape) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f)))
                ≡ trans (sym step4-shape) (sym step3-shape)
    path3-lemma = cong₂ trans refl (sym (sym-cong (onShape-eq g-eq S2f)))
    path3-total : trans
                    (trans (sym step4-shape)
                      (cong (subst (Shape H) p-obj)
                        (sym (onShape-eq g-eq S2f))))
                    (trans (sym step2-shape) (sym step1-shape))
                  ≡ path-shape
    path3-total =
      begin
        trans
          (trans (sym step4-shape)
            (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
          (trans (sym step2-shape) (sym step1-shape))
          ≡⟨ cong (λ p → trans p (trans (sym step2-shape) (sym step1-shape))) path3-lemma ⟩
        trans (trans (sym step4-shape) (sym step3-shape)) (trans (sym step2-shape) (sym step1-shape))
          ≡⟨ trans-assoc (sym step4-shape) ⟩
        trans (sym step4-shape) (trans (sym step3-shape) (trans (sym step2-shape) (sym step1-shape)))
          ≡⟨ refl ⟩
        path-shape
      ∎
    apply-g-result : onPos g1 P1f
                   ≡ subst (Pos H) (trans (sym step2-shape) (cong (onShape g1) (sym eqS-f))) pos2
    apply-g-result = apply-g-eq-to-substed-pos ℓ G H g1 g2 O1f O2f eqO-f S1f S2f eqS-f P1f P2f eqP-f
    pos5-lemma : onPos g1 pos1
               ≡ subst (Pos H) (trans (sym step2-shape) (cong (onShape g1) (sym eqS-f))) pos2
    pos5-lemma = trans (cong (onPos g1) (sym eqP-f)) apply-g-result
  in
  begin
    onPos g1 P1f
      ≡⟨ cong (onPos g1) eqP-f ⟩
    onPos g1 pos1
      ≡⟨ pos5-lemma ⟩
    subst (Pos H) (trans (sym step2-shape) (cong (onShape g1) (sym eqS-f))) pos2
      ≡⟨ cong (λ q → subst (Pos H) q pos2) (cong₂ trans refl path4-lemma) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape)) pos2
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (cong (subst-pos H p-obj (onShape g1 S2f)) (onPos-eq g-eq P2f)) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape)) pos3
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (subst-pos-cong H p-obj
                {S = subst (Shape H) (sym eqO-g) S2g}
                {S' = onShape g1 S2f}
                (sym (onShape-eq g-eq S2f))
                {p = subst-pos H (sym eqO-g) S2g P2g}) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape))
      (subst (Pos H) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f)))
        (subst-pos H p-obj (subst (Shape H) (sym eqO-g) S2g)
          (subst-pos H (sym eqO-g) S2g P2g)))
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (cong (subst (Pos H) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
                    (subst-pos-trans ℓ H (sym eqO-g) p-obj S2g P2g)) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape))
      (subst (Pos H) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f)))
        (subst (Pos H) (sym step4-shape)
          (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)))
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (subst-subst {P = Pos H} (sym step4-shape)
                            {y≡z = cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))}) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape))
      (subst (Pos H)
        (trans (sym step4-shape)
          (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
        (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
      ≡⟨ subst-subst {P = Pos H}
                      (trans (sym step4-shape)
                        (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
                      {y≡z = trans (sym step2-shape) (sym step1-shape)} ⟩
    subst (Pos H)
      (trans
        (trans (sym step4-shape)
          (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
        (trans (sym step2-shape) (sym step1-shape)))
      (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)
      ≡⟨ cong (λ q → subst (Pos H) q
               (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
             path3-total ⟩
    subst (Pos H) path-shape
      (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)
      ≡⟨ cong (λ q → subst (Pos H) q
               (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
             path-shape-lemma ⟩
    subst (Pos H) (trans shape-endpoint-eq (sym eqS-total))
      (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)
      ≡⟨ sym (subst-subst {P = Pos H} shape-endpoint-eq {y≡z = sym eqS-total}) ⟩
    subst (Pos H) (sym eqS-total)
      (subst (Pos H) shape-endpoint-eq
        (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
      ≡⟨ cong (subst (Pos H) (sym eqS-total))
              (subst-pos-eq-cong final-path-eq S2g P2g) ⟩
    subst (Pos H) (sym eqS-total)
      (subst-pos H (sym eqO-total) S2g P2g)
  ∎
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onHom-eq {A} {B} h =
  let
    eqO-f-X : onObj f1 A ≡ onObj f2 A
    eqO-f-X = onObj-eq f-eq A
    eqO-f-Y : onObj f1 B ≡ onObj f2 B
    eqO-f-Y = onObj-eq f-eq B
    eqHom-f : onHom f1 h ≡ subst₂ (Hom G) (sym eqO-f-X) (sym eqO-f-Y) (onHom f2 h)
    eqHom-f = onHom-eq f-eq h
    O2f-X : Obj G
    O2f-X = onObj f2 A
    O2f-Y : Obj G
    O2f-Y = onObj f2 B
    eqO-g-X : onObj g1 O2f-X ≡ onObj g2 O2f-X
    eqO-g-X = onObj-eq g-eq O2f-X
    eqO-g-Y : onObj g1 O2f-Y ≡ onObj g2 O2f-Y
    eqO-g-Y = onObj-eq g-eq O2f-Y
    eqHom-g : onHom g1 (onHom f2 h) ≡ subst₂ (Hom H) (sym eqO-g-X) (sym eqO-g-Y) (onHom g2 (onHom f2 h))
    eqHom-g = onHom-eq g-eq (onHom f2 h)
    p-obj-X : onObj g1 O2f-X ≡ onObj g1 (onObj f1 A)
    p-obj-X = cong (onObj g1) (sym eqO-f-X)
    p-obj-Y : onObj g1 O2f-Y ≡ onObj g1 (onObj f1 B)
    p-obj-Y = cong (onObj g1) (sym eqO-f-Y)
    eqO-total-X : onObj g1 (onObj f1 A) ≡ onObj g2 O2f-X
    eqO-total-X = trans (cong (onObj g1) eqO-f-X) (onObj-eq g-eq O2f-X)
    eqO-total-Y : onObj g1 (onObj f1 B) ≡ onObj g2 O2f-Y
    eqO-total-Y = trans (cong (onObj g1) eqO-f-Y) (onObj-eq g-eq O2f-Y)
    final-path-X : trans (sym eqO-g-X) p-obj-X ≡ sym eqO-total-X
    final-path-X = sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq A
    final-path-Y : trans (sym eqO-g-Y) p-obj-Y ≡ sym eqO-total-Y
    final-path-Y = sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq B
  in
  begin
    onHom (g1 ∘⇒ℱ f1) h
      ≡⟨ refl ⟩
    onHom g1 (onHom f1 h)
      ≡⟨ cong (onHom g1) eqHom-f ⟩
    onHom g1 (subst₂ (Hom G) (sym eqO-f-X) (sym eqO-f-Y) (onHom f2 h))
      ≡⟨ onHom-subst-comm g1 O2f-X O2f-Y (onObj f1 A) (onObj f1 B)
           (sym eqO-f-X) (sym eqO-f-Y) (onHom f2 h) ⟩
    subst₂ (Hom H) p-obj-X p-obj-Y (onHom g1 (onHom f2 h))
      ≡⟨ cong (subst₂ (Hom H) p-obj-X p-obj-Y) eqHom-g ⟩
    subst₂ (Hom H) p-obj-X p-obj-Y (subst₂ (Hom H) (sym eqO-g-X) (sym eqO-g-Y) (onHom g2 (onHom f2 h)))
      ≡⟨ subst₂-trans (sym eqO-g-X) p-obj-X (sym eqO-g-Y) p-obj-Y (onHom g2 (onHom f2 h)) ⟩
    subst₂ (Hom H) (trans (sym eqO-g-X) p-obj-X) (trans (sym eqO-g-Y) p-obj-Y) (onHom g2 (onHom f2 h))
      ≡⟨ cong₂ (λ p q → subst₂ (Hom H) p q (onHom g2 (onHom f2 h))) final-path-X final-path-Y ⟩
    subst₂ (Hom H) (sym eqO-total-X) (sym eqO-total-Y) (onHom g2 (onHom f2 h))
      ≡⟨ refl ⟩
    subst₂ (Hom H) (sym eqO-total-X) (sym eqO-total-Y) (onHom (g2 ∘⇒ℱ f2) h)
  ∎
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onunfold-eq {A} s =
  let
    eqO-f : onObj f1 A ≡ onObj f2 A
    eqO-f = onObj-eq f-eq A
    eqS-f : onShape f1 s ≡ subst (Shape G) (sym eqO-f) (onShape f2 s)
    eqS-f = onShape-eq f-eq s
    t1 : Shape G (onObj f1 A)
    t1 = onShape f1 s
    t2 : Shape G (onObj f2 A)
    t2 = onShape f2 s
    O1-f : Obj G
    O1-f = onObj f1 A
    O2-f : Obj G
    O2-f = onObj f2 A
    eqO-g : onObj g1 O2-f ≡ onObj g2 O2-f
    eqO-g = onObj-eq g-eq O2-f
    eqS-g : onShape g1 t2 ≡ subst (Shape H) (sym eqO-g) (onShape g2 t2)
    eqS-g = onShape-eq g-eq t2
    s1-g : Shape H (onObj g1 O1-f)
    s1-g = onShape g1 t1
    s_mid-g : Shape H (onObj g1 O2-f)
    s_mid-g = onShape g1 t2
    s3-g : Shape H (onObj g2 O2-f)
    s3-g = onShape g2 t2
    eqO-g1 : onObj g1 O1-f ≡ onObj g1 O2-f
    eqO-g1 = cong (onObj g1) eqO-f
    shape-transport : s1-g ≡ subst (Shape H) (sym eqO-g1) s_mid-g
    shape-transport = shape-transport-lemma {F = F} {G = G} {H = H} {f1 = f1} {f2 = f2} g1 f-eq s
    path-f-G : unfold G t2 ≡ unfold G t1
    path-f-G = trans (subst-unfold G (sym eqO-f) t2) (cong (unfold G) (sym eqS-f))
    path-f-H : unfold H s_mid-g ≡ unfold H s1-g
    path-f-H = trans (subst-unfold H (sym eqO-g1) s_mid-g) (cong (unfold H) (sym shape-transport))
    path-g-H : unfold H s3-g ≡ unfold H s_mid-g
    path-g-H = trans (subst-unfold H (sym eqO-g) s3-g) (cong (unfold H) (sym eqS-g))
    path-g-total : unfold H s3-g ≡ unfold H s1-g
    path-g-total = trans path-g-H path-f-H
    path-eq-target : trans (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                          (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    ≡ path-f-H
    path-eq-target = path-eq-target-lemma {F = F} {G = G} {H = H} {f1 = f1} {f2 = f2} g1 f-eq s
    path-eq-source : trans (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                          (sym (cong (unfold G) eqS-f))
                    ≡ path-f-G
    path-eq-source = path-eq-source-lemma {G = G} {o₁ = O1-f} {o₂ = O2-f} eqO-f {s₁ = t1} {s₂ = t2} eqS-f
    P-f : Cosmos ℓ → Set (lsuc ℓ)
    P-f C = unfold F s ⇒ℱ C
    P-g : Cosmos ℓ → Set (lsuc ℓ)
    P-g C = unfold G t2 ⇒ℱ C
    Q-g : Cosmos ℓ → Set (lsuc ℓ)
    Q-g C = C ⇒ℱ unfold H s_mid-g
    f-bisim : onunfold f1 s ≃⇒ℱ subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s)
    f-bisim = onunfold-eq f-eq s
    g-bisim : onunfold g1 t2 ≃⇒ℱ subst (λ C → unfold G t2 ⇒ℱ C) path-g-H (onunfold g2 t2)
    g-bisim = onunfold-eq g-eq t2
    g-bisim-trans-raw : subst₂ (λ A B → A ⇒ℱ B) path-f-G refl (onunfold g1 t2)
      ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B) path-f-G refl (subst P-g path-g-H (onunfold g2 t2))
    g-bisim-trans-raw = subst₂-≃⇒ℱ path-f-G refl g-bisim
    merge-eq : ∀ (f : unfold G t2 ⇒ℱ unfold H s_mid-g) →
      subst₂ (λ A B → A ⇒ℱ B) path-f-G refl f
      ≡ subst Q-g path-f-G f
    merge-eq f = trans (subst₂-⇒ℱ path-f-G refl f)
        (subst-refl-id (λ D → unfold G t1 ⇒ℱ D) _)
    g-bisim-trans : subst Q-g path-f-G (onunfold g1 t2)
      ≃⇒ℱ subst Q-g path-f-G (subst P-g path-g-H (onunfold g2 t2))
    g-bisim-trans = ≡-left-≃⇒ℱ (sym (merge-eq (onunfold g1 t2))) $
      ≡-right-≃⇒ℱ g-bisim-trans-raw (merge-eq (subst P-g path-g-H (onunfold g2 t2)))
    eqSub-g : subst Q-g path-f-G (subst P-g path-g-H (onunfold g2 t2))
      ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-H (onunfold g2 t2)
    eqSub-g = subst-target-source≡subst₂ path-f-G path-g-H (onunfold g2 t2)
    g-bisim-comb : subst Q-g path-f-G (onunfold g1 t2)
                  ≃⇒ℱ
                  subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-H (onunfold g2 t2)
    g-bisim-comb = ≡-right-≃⇒ℱ g-bisim-trans eqSub-g
    left-merge : subst (λ C → unfold G t1 ⇒ℱ C) path-f-H (subst Q-g path-f-G (onunfold g1 t2))
               ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
    left-merge = subst-source-target≡subst₂ path-f-G path-f-H (onunfold g1 t2)
    right-merge : subst (λ C → unfold G t1 ⇒ℱ C) path-f-H (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-H (onunfold g2 t2))
                ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G (trans path-g-H path-f-H) (onunfold g2 t2)
    right-merge = subst₂-subst-right (onunfold g2 t2) path-f-G path-g-H path-f-H
    g-left-transport : onunfold g1 t1 ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
    g-left-transport =
      let
        step1 : onunfold g1 t1 ≃⇒ℱ
                subst₂ (λ A B → A ⇒ℱ B)
                      (sym (cong (unfold G) eqS-f))
                      (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                      (onunfold g1 (subst (Shape G) (sym eqO-f) t2))
        step1 = onunfold-subst-shape {G = G} {H = H} {g = g1} eqS-f
        step2 : onunfold g1 (subst (Shape G) (sym eqO-f) t2) ≡
                subst₂ (λ A C' → A ⇒ℱ C')
                      (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                      (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                      (onunfold g1 t2)
        step2 = onunfold-subst-comm G H g1 (sym eqO-f) t2
        step3 : subst₂ _⇒ℱ_
                    (sym (cong (unfold G) eqS-f))
                    (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    (onunfold g1 (subst (Shape G) (sym eqO-f) t2))
              ≡
                subst₂ _⇒ℱ_
                    (sym (cong (unfold G) eqS-f))
                    (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    (subst₂ _⇒ℱ_
                          (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                          (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                          (onunfold g1 t2))
        step3 = cong (λ z → subst₂ _⇒ℱ_
                              (sym (cong (unfold G) eqS-f))
                              (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                              z)
                    step2
        eqA1 : unfold G (subst (Shape G) (sym eqO-f) t2) ≡ unfold G t2
        eqA1 = unfold-subst-shape {C = G} {o₁ = onObj f2 A} {o₂ = onObj f1 A} (sym eqO-f) t2
        eqA2 : unfold G t2 ≡ unfold G t1
        eqA2 = trans (sym (unfold-subst-shape {C = G} {o₁ = onObj f2 A} {o₂ = onObj f1 A} (sym eqO-f) t2))
                    (sym (cong (unfold G) eqS-f))
        eqB1 : unfold H (onShape g1 (subst (Shape G) (sym eqO-f) t2)) ≡ unfold H (onShape g1 t2)
        eqB1 = unfold-onShape-subst G H g1 (sym eqO-f) t2
        eqB2 : unfold H (onShape g1 t2) ≡ unfold H (onShape g1 t1)
        eqB2 = trans (sym eqB1) (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
        step4 : subst₂ _⇒ℱ_
                      (sym (cong (unfold G) eqS-f))
                      (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                      (subst₂ _⇒ℱ_ (sym eqA1) (sym eqB1) (onunfold g1 t2))
                ≡ subst₂ _⇒ℱ_ eqA2 eqB2 (onunfold g1 t2)
        step4 =
          let
            p1 = sym eqA1
            p2 = sym (cong (unfold G) eqS-f)
            q1 = sym eqB1
            q2 = sym (cong (unfold H) (cong (onShape g1) eqS-f))
            r  = onunfold g1 t2
            base : subst₂ _⇒ℱ_ p2 q2 (subst₂ _⇒ℱ_ p1 q1 r)
                 ≡ subst₂ _⇒ℱ_ (trans p1 p2) (trans q1 q2) r
            base = subst₂-comp {A = Cosmos ℓ} {B = Cosmos ℓ} {C = _⇒ℱ_}
                              p1 p2 q1 q2
            tr1 : trans p1 p2 ≡ eqA2
            tr1 = refl
            tr2 : trans q1 q2 ≡ eqB2
            tr2 = refl
            replace : subst₂ _⇒ℱ_ (trans p1 p2) (trans q1 q2) r ≡ subst₂ _⇒ℱ_ eqA2 eqB2 r
            replace = trans (cong (λ p → subst₂ _⇒ℱ_ p (trans q1 q2) r) tr1)
                            (cong (λ q → subst₂ _⇒ℱ_ eqA2 q r) tr2)
          in trans base replace
        path-eq-G : trans (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                          (sym (cong (unfold G) eqS-f))
                    ≡ path-f-G
        path-eq-G = path-eq-source
        path-eq-H : trans (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                          (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    ≡ path-f-H
        path-eq-H = path-eq-target
        step5 : subst₂ (λ A B → A ⇒ℱ B)
                      (trans (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                              (sym (cong (unfold G) eqS-f)))
                      (trans (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                              (sym (cong (unfold H) (cong (onShape g1) eqS-f))))
                      (onunfold g1 t2)
                ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
        step5 = cong₂ (λ p q → subst₂ (λ A B → A ⇒ℱ B) p q (onunfold g1 t2)) path-eq-G path-eq-H
        step6 : subst₂ (λ A B → A ⇒ℱ B)
                      (sym (cong (unfold G) eqS-f))
                      (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                      (onunfold g1 (subst (Shape G) (sym eqO-f) t2))
                ≃⇒ℱ
                subst₂ (λ A B → A ⇒ℱ B)
                      path-f-G
                      path-f-H
                      (onunfold g1 t2)
        step6 = ≡→≃⇒ℱ (trans step3 (trans step4 step5))
      in
      trans-≃⇒ℱ step1 step6
    g-right-combine : subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
                    ≃⇒ℱ
                    subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2)
    g-right-combine =
      let
        eq1 = sym (subst-source-target≡subst₂ path-f-G path-f-H (onunfold g1 t2))
        eq2 = subst₂-subst-right (onunfold g2 t2) path-f-G path-g-H path-f-H
        mid = subst-≃⇒ℱ ℓ (unfold G t1) _ _ path-f-H g-bisim-comb
      in
      ≡-left-≃⇒ℱ eq1 (≡-right-≃⇒ℱ mid eq2)
    g-bisim-final : onunfold g1 t1 ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2)
    g-bisim-final = trans-≃⇒ℱ g-left-transport g-right-combine
    comp-subst-comm : (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2)) ∘⇒ℱ (subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
                    ≡ subst (λ C → unfold F s ⇒ℱ C) path-g-total (onunfold g2 t2 ∘⇒ℱ onunfold f2 s)
    comp-subst-comm =
      begin
        (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2))
          ∘⇒ℱ
        (subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
      ≡⟨ cong (λ g' → g' ∘⇒ℱ subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
              (sym (subst-source-target≡subst₂ path-f-G path-g-total (onunfold g2 t2))) ⟩
        (subst (λ B → unfold G t1 ⇒ℱ B) path-g-total
          (subst (λ A → A ⇒ℱ unfold H s3-g) path-f-G (onunfold g2 t2)))
          ∘⇒ℱ
        (subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
      ≡⟨ subst-∘-comm path-f-G path-g-total (onunfold g2 t2) (onunfold f2 s) ⟩
        subst (λ C → unfold F s ⇒ℱ C) path-g-total (onunfold g2 t2 ∘⇒ℱ onunfold f2 s)
      ∎
  in
    {!   !}

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
UnitCosmosMorphLift .morphLift-comp _ _ _ = sym-≃⇒ℱ (id-l-≃⇒ℱ id⇒ℱ)

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
