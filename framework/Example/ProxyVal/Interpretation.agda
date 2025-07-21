{-# OPTIONS --without-K --safe #-}

module Example.ProxyVal.Interpretation where

open import Utils.Misc  -- for trivialOrd and trivialOrdIsPreorder
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Language
open import Annotation.Interpretation
open import Annotation.Soundness

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; sym; subst; module ≡-Reasoning)
open ≡-Reasoning using (begin_; step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_∘′_; id)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ann : AnnSig

  Γ : Ctxt
  τ τ′ τₐ τᵣ τ₁ τ₂ : Ty

ℐproxyval : AnnIntr {𝒜} 𝒯
AnnIntr.Ix         (ℐproxyval {𝒜}) = ⊤
AnnIntr.IxRel      (ℐproxyval {𝒜}) A ix ix′ = ⊤
AnnIntr.Inv        (ℐproxyval {𝒜}) s = ⊤
AnnIntr.Ord        (ℐproxyval {𝒜}) = trivialOrd
AnnIntr.isPreorder (ℐproxyval {𝒜}) = trivialOrdIsPreorder
AnnIntr.𝔹          (ℐproxyval {𝒜}) A ix◁ix′ e = ⊤
AnnIntr.𝔹Sound     (ℐproxyval {𝒜}) step inv inv′ mono bsat = bsat
AnnIntr.ℙ          (ℐproxyval {𝒜}) {τ = τ} A ix◁ix′ em = (ATAnn 𝒜  ∣  ⌊ em ⌋m isvalof τ)

ℐproxyval-monotonic : AnnTransitInterpIs {𝒯 = 𝒯} ℐproxyval Monotonic
ℐproxyval-monotonic tag step esat₁ termSat = tt , tt

ℐproxyval-sound : AnnTransitInterpIs {𝒯 = 𝒯} ℐproxyval Sound
ℐproxyval-sound `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat ⋆) termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐproxyval-sound `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat esat) termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐproxyval-sound `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂)) termSat inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat = (tt , tt) ,′ (tt , tt)
    }
ℐproxyval-sound `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (inl esat)) termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , tt
    }
ℐproxyval-sound `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (inr esat)) termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , tt
    }
ℐproxyval-sound `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (roll τ esat)) termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , tt
    }
ℐproxyval-sound `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (box esat)) termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , box/v premWit
    }
ℐproxyval-sound `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat)) termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , ƛ/v ⌊ esat ⌋i
   }
ℐproxyval-sound `R-merge-box
  step@(mkStep (τ′ , refl)
          termEnv
          (mkTerm ψ₁ refl)
          (mkTerm ψ₂ refl)
          premWit
          trWit)
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  termSat@record { metaVarIx = mvix₁
                 ; boundarySat = ((tt , tt) , (tt , iv)) }
  mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , iv
    }
ℐproxyval-sound `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl)
          termEnv
          (mkTerm ψ₁ refl)
          (mkTerm ψ₂ refl)
          premWit
          trWit)
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esatb)))
  termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , ƛ/v eb
    }
ℐproxyval-sound `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat))) termSat inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , tt
    }
ℐproxyval-sound `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ) termSat inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat = (tt , tt) ,′ (tt , tt)
    }

mutual
  data _∣_⊢ᵛ_ Ann : (Γ : Ctxt) → (τ : Ty) → Set where
      proxyᵛ : ∀ {eᵛ} →
               (A : Ann τ) →
               (iv : Ann ∣ ⌊ eᵛ ⌋ᵛ isvalof τ) →
               (vm : Ann ∣ ⌊ eᵛ ⌋ᵛ ismonctorof τ) →
               ----------------------------------
               Ann ∣ Γ ⊢ᵛ τ

      B#_⟪_⟫ : (A : Ann τ) →
               Ann ∣ [] ⊢ᵛ τ →
               --------------
               Ann ∣ Γ ⊢ᵛ τ

      ⋆ : Ann ∣ Γ ⊢ᵛ `1

      `z : Ann ∣ Γ ⊢ᵛ `ℕ

      `s : Ann ∣ Γ ⊢ᵛ `ℕ →
           --------------
           Ann ∣ Γ ⊢ᵛ `ℕ

      foldN : Ann ∣ Γ ⊢ᵛ `ℕ →
              Ann ∣ Γ ⊢ᵛ τ →
              Ann ∣ (`ℕ ∷ τ ∷ Γ) ⊢ᵛ τ →
              -----------------------
              Ann ∣ Γ ⊢ᵛ τ

      assert : Ann ∣ Γ ⊢ᵛ `ℕ →
               -------------
               Ann ∣ Γ ⊢ᵛ `1

      _`,_ : Ann ∣ Γ ⊢ᵛ τ₁ →
             Ann ∣ Γ ⊢ᵛ τ₂ →
             ---------------
             Ann ∣ Γ ⊢ᵛ (τ₁ `* τ₂)

      π₁ :   Ann ∣ Γ ⊢ᵛ (τ₁ `* τ₂) →
             ---------------------
             Ann ∣ Γ ⊢ᵛ τ₁

      π₂ :   Ann ∣ Γ ⊢ᵛ (τ₁ `* τ₂) →
             ---------------------
             Ann ∣ Γ ⊢ᵛ τ₂

      inl :        Ann ∣ Γ ⊢ᵛ τ₁ →
                   ---------------------
                   Ann ∣ Γ ⊢ᵛ (τ₁ `+ τ₂)

      inr :        Ann ∣ Γ ⊢ᵛ τ₂ →
                   ---------------------
                   Ann ∣ Γ ⊢ᵛ (τ₁ `+ τ₂)

      case_of_∣_ : Ann ∣ Γ ⊢ᵛ (τ₁ `+ τ₂) →
                   Ann ∣ (τ₁ ∷ Γ) ⊢ᵛ τ →
                   Ann ∣ (τ₂ ∷ Γ) ⊢ᵛ τ →
                   ---------------------
                   Ann ∣ Γ ⊢ᵛ τ

      box :   Ann ∣ Γ ⊢ᵛ τ →
              ----------------
              Ann ∣ Γ ⊢ᵛ Box τ

      unbox : Ann ∣ Γ ⊢ᵛ Box τ →
              ----------------
              Ann ∣ Γ ⊢ᵛ τ

      `_ :  (y : τ ∈ Γ) →
            -------------
            Ann ∣ Γ ⊢ᵛ τ

      ƛ_ :  Ann ∣ (τₐ ∷ Γ) ⊢ᵛ τᵣ →
            ---------------------
            Ann ∣ Γ ⊢ᵛ (τₐ `→ τᵣ)

      _·_ : Ann ∣ Γ ⊢ᵛ (τₐ `→ τᵣ) →
            Ann ∣ Γ ⊢ᵛ τₐ →
            ---------------------
            Ann ∣ Γ ⊢ᵛ τᵣ

      unroll : ∀ {τ} →
               Ann ∣ Γ ⊢ᵛ μ τ →
               ------------------------------
               Ann ∣ Γ ⊢ᵛ tsubst τ [t0↦ μ τ ]

      roll :   ∀ τ →
               Ann ∣ Γ ⊢ᵛ tsubst τ [t0↦ μ τ ] →
               ------------------------------
               Ann ∣ Γ ⊢ᵛ μ τ

      fix : Ann ∣ (τ ∷ Γ) ⊢ᵛ τ →
            ------------------
            Ann ∣ Γ ⊢ᵛ τ

      _⨟_ : Ann ∣ Γ ⊢ᵛ τ →
            Ann ∣ Γ ⊢ᵛ τ₁ →
            -------------
            Ann ∣ Γ ⊢ᵛ τ₁

  ⌊_⌋ᵛ : (eᵛ : Ann ∣ Γ ⊢ᵛ τ) → Ann ∣ Γ ⊢ τ
  ⌊ proxyᵛ A iv vm    ⌋ᵛ = proxy A vm
  ⌊ B# A ⟪ e ⟫        ⌋ᵛ = B# A ⟪ ⌊ e ⌋ᵛ ⟫
  ⌊ ⋆                 ⌋ᵛ = ⋆
  ⌊ `z                ⌋ᵛ = `z
  ⌊ `s e              ⌋ᵛ = `s ⌊ e ⌋ᵛ
  ⌊ foldN e ez es     ⌋ᵛ = foldN ⌊ e ⌋ᵛ ⌊ ez ⌋ᵛ ⌊ es ⌋ᵛ
  ⌊ assert e          ⌋ᵛ = assert ⌊ e ⌋ᵛ
  ⌊ e₁ `, e₂          ⌋ᵛ = ⌊ e₁ ⌋ᵛ `, ⌊ e₂ ⌋ᵛ
  ⌊ π₁ e              ⌋ᵛ = π₁ ⌊ e ⌋ᵛ
  ⌊ π₂ e              ⌋ᵛ = π₂ ⌊ e ⌋ᵛ
  ⌊ inl e             ⌋ᵛ = inl ⌊ e ⌋ᵛ
  ⌊ inr e             ⌋ᵛ = inr ⌊ e ⌋ᵛ
  ⌊ case e of e₁ ∣ e₂ ⌋ᵛ = case ⌊ e ⌋ᵛ of ⌊ e₁ ⌋ᵛ ∣ ⌊ e₂ ⌋ᵛ
  ⌊ box e             ⌋ᵛ = box ⌊ e ⌋ᵛ
  ⌊ unbox e           ⌋ᵛ = unbox ⌊ e ⌋ᵛ
  ⌊ ` y               ⌋ᵛ = ` y
  ⌊ ƛ e               ⌋ᵛ = ƛ ⌊ e ⌋ᵛ
  ⌊ e · eₐ            ⌋ᵛ = ⌊ e ⌋ᵛ · ⌊ eₐ ⌋ᵛ
  ⌊ unroll e          ⌋ᵛ = unroll ⌊ e ⌋ᵛ
  ⌊ roll τ e          ⌋ᵛ = roll τ ⌊ e ⌋ᵛ
  ⌊ fix e             ⌋ᵛ = fix ⌊ e ⌋ᵛ
  ⌊ e ⨟ e₁            ⌋ᵛ = ⌊ e ⌋ᵛ ⨟ ⌊ e₁ ⌋ᵛ

  ⊢ᵛ⇒ℐproxyval : ∀ {𝒯} → (eᵛ : ATAnn 𝒜 ∣ Γ ⊢ᵛ τ) → ℐproxyval {𝒜} {𝒯} ⊨[ tt ] ⌊ eᵛ ⌋ᵛ
  ⊢ᵛ⇒ℐproxyval (proxyᵛ {eᵛ = e} A iv vm) = proxy/i vm tt tt tt iv (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (B# A ⟪ e ⟫) = B/i tt tt tt tt (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval ⋆ = ⋆
  ⊢ᵛ⇒ℐproxyval `z = `z
  ⊢ᵛ⇒ℐproxyval (`s e) = `s (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (foldN e ez es) = foldN (⊢ᵛ⇒ℐproxyval e) (⊢ᵛ⇒ℐproxyval ez) (⊢ᵛ⇒ℐproxyval es)
  ⊢ᵛ⇒ℐproxyval (assert e) = assert (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (e₁ `, e₂) = ⊢ᵛ⇒ℐproxyval e₁ `, ⊢ᵛ⇒ℐproxyval e₂
  ⊢ᵛ⇒ℐproxyval (π₁ e) = π₁ (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (π₂ e) = π₂ (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (inl e) = inl (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (inr e) = inr (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (case e of e₁ ∣ e₂) = case ⊢ᵛ⇒ℐproxyval e of ⊢ᵛ⇒ℐproxyval e₁ ∣ ⊢ᵛ⇒ℐproxyval e₂
  ⊢ᵛ⇒ℐproxyval (box e) = box (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (unbox e) = unbox (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (` y) = ` y
  ⊢ᵛ⇒ℐproxyval (ƛ e) = ƛ ⊢ᵛ⇒ℐproxyval e
  ⊢ᵛ⇒ℐproxyval (e · eₐ) = ⊢ᵛ⇒ℐproxyval e · ⊢ᵛ⇒ℐproxyval eₐ
  ⊢ᵛ⇒ℐproxyval (unroll e) = unroll (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (roll τ e) = roll τ (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (fix e) = fix (⊢ᵛ⇒ℐproxyval e)
  ⊢ᵛ⇒ℐproxyval (e ⨟ e₁) = ⊢ᵛ⇒ℐproxyval e ⨟ ⊢ᵛ⇒ℐproxyval e₁

  ℐproxyval⇒⊢ᵛ : ∀ {𝒯} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
    ℐproxyval {𝒜} {𝒯} ⊨[ tt ] e →
    ATAnn 𝒜 ∣ Γ ⊢ᵛ τ
  ℐproxyval⇒⊢ᵛ esat = proj₁ (ℐproxyval⇒⊢ᵛ-and-eq esat)

  to-⊢ᵛ-forget : ∀ {𝒯} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
    (esat : ℐproxyval {𝒜} {𝒯} ⊨[ tt ] e) →
    e ≡ (⌊_⌋ᵛ ∘′ ℐproxyval⇒⊢ᵛ) esat
  to-⊢ᵛ-forget esat = proj₂ (ℐproxyval⇒⊢ᵛ-and-eq esat)

  transport-isval : {e : Ann ∣ [] ⊢ τ} →
    isval Ann τ e →
    {eᵛ : Ann ∣ [] ⊢ᵛ τ} →
    e ≡ ⌊ eᵛ ⌋ᵛ →
    isval Ann τ ⌊ eᵛ ⌋ᵛ
  transport-isval {Ann} {τ} iv eq = subst (isval Ann τ) eq iv

  ℐproxyval⇒⊢ᵛ-and-eq : ∀ {𝒯} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
    ℐproxyval {𝒜} {𝒯} ⊨[ tt ] e →
    Σ (ATAnn 𝒜 ∣ Γ ⊢ᵛ τ) ((e ≡_) ∘′ ⌊_⌋ᵛ)
  ℐproxyval⇒⊢ᵛ-and-eq (proxy/i {A = A} (box/m e) .tt ix′ ix◁ix′ (box/v psat) (box esat)) =
    proxyᵛ A (box/v (transport-isval psat (proj₂ eᵛ,eq))) (box/m ⌊ proj₁ eᵛ,eq ⌋ᵛ) ,
    cong (λ e → proxy {e = box e} A (box/m e)) (proj₂ eᵛ,eq) where
      eᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat
  ℐproxyval⇒⊢ᵛ-and-eq (proxy/i {A = A} (ƛ/m e) .tt ix′ ix◁ix′ (ƛ/v .e) (ƛ esat)) =
    proxyᵛ A (ƛ/v ⌊ proj₁ eᵛ,eq ⌋ᵛ) (ƛ/m ⌊ proj₁ eᵛ,eq ⌋ᵛ) ,
    -- Note: the implicit argument of proxy refers to e, so this is not function composition (_∘_)
    cong (λ e → proxy {e = ƛ e} A (ƛ/m e)) (proj₂ eᵛ,eq) where
      eᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat
  ℐproxyval⇒⊢ᵛ-and-eq (B/i {A = A} .tt ix′ ix◁ix′ bsat esat) =
    Product.map (B# A ⟪_⟫) (cong (B# A ⟪_⟫)) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq ⋆ = ⋆ , refl
  ℐproxyval⇒⊢ᵛ-and-eq `z = `z , refl
  ℐproxyval⇒⊢ᵛ-and-eq (`s esat) =
    Product.map `s (cong `s) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq {e = foldN e ez es} (foldN esat esatz esats) =
    foldN (proj₁ eᵛ,eq) (proj₁ ezᵛ,eq) (proj₁ esᵛ,eq) ,
    (begin
        foldN e ez es
      ≡⟨ cong (λ e → foldN e _ _) (proj₂ eᵛ,eq) ⟩
        foldN ⌊ proj₁ eᵛ,eq ⌋ᵛ ez es
      ≡⟨ cong (λ ez → foldN _ ez _) (proj₂ ezᵛ,eq) ⟩
        foldN ⌊ proj₁ eᵛ,eq ⌋ᵛ ⌊ proj₁ ezᵛ,eq ⌋ᵛ es
      ≡⟨ cong (λ es → foldN _ _ es) (proj₂ esᵛ,eq) ⟩
        foldN ⌊ proj₁ eᵛ,eq ⌋ᵛ ⌊ proj₁ ezᵛ,eq ⌋ᵛ ⌊ proj₁ esᵛ,eq ⌋ᵛ
      ≡⟨⟩
        ⌊ foldN (proj₁ eᵛ,eq) (proj₁ ezᵛ,eq) (proj₁ esᵛ,eq) ⌋ᵛ
    ∎) where
      eᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat
      ezᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esatz
      esᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esats
  ℐproxyval⇒⊢ᵛ-and-eq (assert esat) =
    Product.map assert (cong assert) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq {e = e₁ `, e₂} (esat₁ `, esat₂) =
    (proj₁ e₁ᵛ,eq `, proj₁ e₂ᵛ,eq) ,
    (begin
        e₁ `, e₂
      ≡⟨ cong (_`, _) (proj₂ e₁ᵛ,eq) ⟩
        ⌊ proj₁ e₁ᵛ,eq ⌋ᵛ `, e₂
      ≡⟨ cong (_ `,_) (proj₂ e₂ᵛ,eq) ⟩
        ⌊ proj₁ e₁ᵛ,eq ⌋ᵛ `, ⌊ proj₁ e₂ᵛ,eq ⌋ᵛ
      ≡⟨⟩
        ⌊ proj₁ e₁ᵛ,eq `, proj₁ e₂ᵛ,eq ⌋ᵛ
    ∎) where
      e₁ᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat₁
      e₂ᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat₂
  ℐproxyval⇒⊢ᵛ-and-eq (π₁ esat) =
    Product.map π₁ (cong π₁) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (π₂ esat) =
    Product.map π₂ (cong π₂) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (inl esat) =
    Product.map inl (cong inl) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (inr esat) =
    Product.map inr (cong inr) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq {e = case e of e₁ ∣ e₂} (case esat of esat₁ ∣ esat₂) =
    case proj₁ eᵛ,eq of proj₁ e₁ᵛ,eq ∣ proj₁ e₂ᵛ,eq ,
    (begin
        case e of e₁ ∣ e₂
      ≡⟨ cong (case_of _ ∣ _) (proj₂ eᵛ,eq) ⟩
        case ⌊ proj₁ eᵛ,eq ⌋ᵛ of e₁ ∣ e₂
      ≡⟨ cong (case _ of_∣ _) (proj₂ e₁ᵛ,eq) ⟩
        case ⌊ proj₁ eᵛ,eq ⌋ᵛ of ⌊ proj₁ e₁ᵛ,eq ⌋ᵛ ∣ e₂
      ≡⟨ cong (case _ of _ ∣_) (proj₂ e₂ᵛ,eq) ⟩
        case ⌊ proj₁ eᵛ,eq ⌋ᵛ of ⌊ proj₁ e₁ᵛ,eq ⌋ᵛ ∣ ⌊ proj₁ e₂ᵛ,eq ⌋ᵛ
      ≡⟨⟩
        ⌊ case proj₁ eᵛ,eq of proj₁ e₁ᵛ,eq ∣ proj₁ e₂ᵛ,eq ⌋ᵛ
    ∎) where
      eᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat
      e₁ᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat₁
      e₂ᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat₂
  ℐproxyval⇒⊢ᵛ-and-eq (box esat) =
    Product.map box (cong box) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (unbox esat) =
    Product.map unbox (cong unbox) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (` y) = ` y , refl
  ℐproxyval⇒⊢ᵛ-and-eq (ƛ esat) =
    Product.map ƛ_ (cong ƛ_) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq {e = e · eₐ} (esat · esatₐ) =
    proj₁ eᵛ,eq · proj₁ eₐᵛ,eq ,
    (begin
        e · eₐ
      ≡⟨ cong (_· _) (proj₂ eᵛ,eq) ⟩
        ⌊ proj₁ eᵛ,eq ⌋ᵛ · eₐ
      ≡⟨ cong (_ ·_) (proj₂ eₐᵛ,eq) ⟩
        ⌊ proj₁ eᵛ,eq ⌋ᵛ · ⌊ proj₁ eₐᵛ,eq ⌋ᵛ
      ≡⟨⟩
        ⌊ proj₁ eᵛ,eq · proj₁ eₐᵛ,eq ⌋ᵛ
    ∎) where
      eᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat
      eₐᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esatₐ
  ℐproxyval⇒⊢ᵛ-and-eq (unroll esat) =
    Product.map unroll (cong unroll) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (roll τ esat) =
    Product.map (roll τ) (cong (roll τ)) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq (fix esat) =
    Product.map fix (cong fix) (ℐproxyval⇒⊢ᵛ-and-eq esat)
  ℐproxyval⇒⊢ᵛ-and-eq {e = e ⨟ e₁} (esat ⨟ esat₁) =
    proj₁ eᵛ,eq ⨟ proj₁ e₁ᵛ,eq ,
    (begin
        e ⨟ e₁
      ≡⟨ cong (_⨟ _) (proj₂ eᵛ,eq) ⟩
        ⌊ proj₁ eᵛ,eq ⌋ᵛ ⨟ e₁
      ≡⟨ cong (_ ⨟_) (proj₂ e₁ᵛ,eq) ⟩
        ⌊ proj₁ eᵛ,eq ⌋ᵛ ⨟ ⌊ proj₁ e₁ᵛ,eq ⌋ᵛ
      ≡⟨⟩
        ⌊ proj₁ eᵛ,eq ⨟ proj₁ e₁ᵛ,eq ⌋ᵛ
    ∎) where
      eᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat
      e₁ᵛ,eq = ℐproxyval⇒⊢ᵛ-and-eq esat₁

  proxy-carry-only-value : ∀ {s₁ s₂} {e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    𝒯 ⊢ s₁ , e₁ ⟶* s₂ , e₂ →
    ∃[ e₁ᵛ ] e₁ ≡ ⌊ e₁ᵛ ⌋ᵛ →
    ∃[ e₂ᵛ ] e₂ ≡ ⌊ e₂ᵛ ⌋ᵛ
  proxy-carry-only-value steps (e₁ᵛ , refl) =
    e₂ᵛ , to-⊢ᵛ-forget esat₂ where
      esat₁ = ⊢ᵛ⇒ℐproxyval e₁ᵛ
      esat₂ = soundness* ℐproxyval ℐproxyval-monotonic ℐproxyval-sound steps tt esat₁
      e₂ᵛ = ℐproxyval⇒⊢ᵛ esat₂

  {-
  -- problem: need to takle the problem with K -- in the whole, got the problematic eq : ⌊ e ⌋ᵛ ≡ ⌊ e ⌋ᵛ
  from-⊢ᵛ-forget : ∀ {s} →
    (eᵛ : ATAnn 𝒜 ∣ Γ ⊢ᵛ τ) →
    eᵛ ≡ (ℐproxyval⇒⊢ᵛ {𝒜 = 𝒜} {s = s} ∘′ ⊢ᵛ⇒ℐproxyval) eᵛ
  from-⊢ᵛ-forget {𝒜} {Γ} {Box τ} {s = s} (proxyᵛ {eᵛ = box e} A (box/v iv) (box/m ._))
    with ℐproxyval⇒⊢ᵛ-and-eq {s = s} (⊢ᵛ⇒ℐproxyval e) | from-⊢ᵛ-forget {s = s} e
  ... | .e , eq | refl = {!!}
  from-⊢ᵛ-forget {s = s} (proxyᵛ {eᵛ = ƛ e} A (ƛ/v ._) (ƛ/m ._))
    rewrite sym (from-⊢ᵛ-forget {s = s} e)
    = refl
  from-⊢ᵛ-forget (B# A ⟪ e ⟫) = cong (B# A ⟪_⟫) (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget ⋆ = refl
  from-⊢ᵛ-forget `z = refl
  from-⊢ᵛ-forget (`s e) = cong `s (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget {s = s} (foldN e ez es)
    rewrite sym (from-⊢ᵛ-forget {s = s} e)
          | sym (from-⊢ᵛ-forget {s = s} ez)
    = cong (foldN _ _) (from-⊢ᵛ-forget es)
  from-⊢ᵛ-forget (assert e) = cong assert (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget {s = s} (e₁ `, e₂)
    rewrite sym (from-⊢ᵛ-forget {s = s} e₁)
    = cong (_ `,_) (from-⊢ᵛ-forget e₂)
  from-⊢ᵛ-forget (π₁ e) = cong π₁ (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (π₂ e) = cong π₂ (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (inl e) = cong inl (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (inr e) = cong inr (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget {s = s} (case e of e₁ ∣ e₂)
    rewrite sym (from-⊢ᵛ-forget {s = s} e)
          | sym (from-⊢ᵛ-forget {s = s} e₁)
    = cong (case _ of _ ∣_) (from-⊢ᵛ-forget e₂)
  from-⊢ᵛ-forget (box e) = cong box (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (unbox e) = cong unbox (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (` y) = refl
  from-⊢ᵛ-forget (ƛ e) = cong ƛ_ (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget {s = s} (e · eₐ)
    rewrite sym (from-⊢ᵛ-forget {s = s} e)
    = cong (_ ·_) (from-⊢ᵛ-forget eₐ)
  from-⊢ᵛ-forget (unroll e) = cong unroll (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (roll τ e) = cong (roll τ) (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget (fix e) = cong fix (from-⊢ᵛ-forget e)
  from-⊢ᵛ-forget {s = s} (e ⨟ e₁)
    rewrite sym (from-⊢ᵛ-forget {s = s} e)
    = cong (_ ⨟_) (from-⊢ᵛ-forget e₁)
  -}
