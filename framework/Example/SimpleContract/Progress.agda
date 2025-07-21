{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)

module Example.SimpleContract.Progress {m} (ℙ𝕣𝕖𝕕 : Fin m → ℕ → Bool) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product.Base as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; _∘′_)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language
open import Syntax.Template
open import OpSemantics.Base
open import OpSemantics.TypeSafety
open import Annotation.Interpretation
open import Annotation.Soundness

𝒜ctc : AnnTerm
Pred⟦_⟧ : Fin m → ∀ {v} → ATAnn 𝒜ctc ∣ v isvalof `ℕ → Bool
Pred⟦ m ⟧ = ℙ𝕣𝕖𝕕 m ∘′ nat-val⇒ℕ where
  nat-val⇒ℕ : ∀ {v} → ATAnn 𝒜ctc ∣ v isvalof `ℕ → ℕ
  nat-val⇒ℕ z/v      = zero
  nat-val⇒ℕ (s/v iv) = suc (nat-val⇒ℕ iv)

open import Example.SimpleContract.ExtensibleAnnotation 𝒜ctc Pred⟦_⟧
  hiding (𝒜ctc)
open import Example.FirstOrder.FirstOrderTy 𝒜ctc
open import Example.FirstOrder.FlatBoundaryExpr 𝒜ctc
open import Example.FirstOrder.Interpretation 𝒜ctc

AnnTerm.Ann   𝒜ctc τ = CtcN [] τ
AnnTerm.State 𝒜ctc   = Status

open AnnTerm 𝒜ctc using (Ann; State)

import TransitionRelationUtil

private variable
  s s′ : Status

  Δ Δ′ : TCtxt
  Γ Γ′ : Ctxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ
  e e′ : Ann ∣ Γ ⊢ τ
  v : Ann ∣ [] ⊢ τ

data CtcProgress : (s : State) → (e : Ann ∣ [] ⊢ τ) → Set where
  CP-step :
    𝒯c id𝒜view ⊢ Ok , e ⟶ s′ , e′ →
    CtcProgress Ok e

  CP-err :
    (ec : Ann ∣ e ⦂ τ ▷ (assert `z) ⦂ `1) →
    CtcProgress s e

  CP-val :
    (iv : Ann ∣ v isvalof τ) →
    CtcProgress s v

ctc-pending-progress :
  (tag : RuleTag) →
  ℐfstord (𝒯c id𝒜view) ⊨[ tt ] e →
  ATPendingStep 𝒜ctc (AnnRules Ann tag) e →
  ∃[ s′ ] ∃[ e′ ] ATStep 𝒜ctc (AnnRules Ann tag , 𝒯c id𝒜view tag) Ok e s′ e′

ctc-progress-step : ∀ e → ℐfstord (𝒯c id𝒜view) ⊨[ tt ] e → CtcProgress {τ} Ok e

ctc-progress :
  ℐfstord (𝒯c id𝒜view) ⊨[ tt ] e →
  𝒯c id𝒜view ⊢ Ok , e ⟶* s′ , e′ →
  s′ ≡ Err ⊎
  (Ann ∣ e′ isvalof τ) ⊎
  (Ann ∣ e′ ⦂ τ ▷ (assert `z) ⦂ `1) ⊎
  (∃[ s″ ] ∃[ e″ ] 𝒯c id𝒜view ⊢ s′ , e′ ⟶ s″ , e″)
ctc-progress {s′ = s′} {e′ = e′} ⊨e/fb steps with s′
... | Err = inj₁ refl
... | Ok with ctc-progress-step e′ (soundness*  (ℐfstord(𝒯c id𝒜view))
                                                (ℐfstord-monotonic (𝒯c id𝒜view))
                                                (ℐfstord-sound (𝒯c id𝒜view))
                                                steps
                                                tt
                                                ⊨e/fb)
... | CP-step step = inj₂ (inj₂ (inj₂ (_ , _ , step)))
... | CP-err ec    = inj₂ (inj₂ (inj₁ ec))
... | CP-val iv    = inj₂ (inj₁ iv)

ctc-progress-step e ⊨e/fb with progress Ok e
... | P-step step = CP-step (R-redex step)
... | P-pending ec tag pending = CP-step (R-bdr tag Ok (proj₁ s′,eᵣ′,stepᵣ) (proj₂ e′,step))
  where s′,eᵣ′,stepᵣ = ctc-pending-progress tag (proj₂ (idecompose-by-ectxt ec ⊨e/fb)) pending
        e′,step      = plug-∃ ec (proj₂ (proj₂ s′,eᵣ′,stepᵣ))
... | P-err ec = CP-err ec
... | P-val iv = CP-val iv

ctc-pending-progress `R-cross-unit ⊨e/fb pending@record { tyVarsWit = refl } =
  _ , _ , Pending⇒Step pending (λ ()) (refl ,′ refl)
ctc-pending-progress `R-cross-nat ⊨e/fb
  pending@record  { tyVarsWit = refl
                  ; term₁ = mkTerm ψ₁ refl
                  ; premiseWit = iv }
  = (if flat-pred (ψ₁(here refl)) iv then Ok else Err) ,
    _ ,
    Pending⇒Step pending (λ ()) (Ok , (refl ,′ refl) ,′ refl)
ctc-pending-progress `R-cross-cons ⊨e/fb
  pending@record { tyVarsWit = ((τ₁ , τ₂) , refl)
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where
                           (here refl)         → */c-κ₁ (ψ₁(here refl))
                           (there (here refl)) → */c-κ₂ (ψ₁(here refl)))
                         -- Technically, there is no need to write down */c-κᵢ (ψ₁(here refl)) above
                         -- because the proof below (refl ,′ refl) constrains the annotations
                         ((refl ,′ refl) ,′ (refl ,′ refl))
ctc-pending-progress `R-cross-inl ⊨e/fb
  pending@record { tyVarsWit = ((τ₁ , τ₂) , refl)
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where (here refl) → +/c-κ₁ (ψ₁(here refl)))
                         ((refl ,′ refl) ,′ refl)
ctc-pending-progress `R-cross-inr ⊨e/fb
  pending@record { tyVarsWit = ((τ₁ , τ₂) , refl)
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where (here refl) → +/c-κ₂ (ψ₁(here refl)))
                         ((refl ,′ refl) ,′ refl)
ctc-pending-progress `R-cross-roll ⊨e/fb
  pending@record { tyVarsWit = (τ′ , refl)
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where (here refl) → μ/c-κ (ψ₁(here refl)))
                         ((refl ,′ refl) ,′ refl)
ctc-pending-progress `R-cross-box ⊨e/fb
  pending@record { tyVarsWit = (τ′ , refl)
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where (here refl) → ψ₁(here refl))
                         ((refl ,′ refl) ,′ refl)
ctc-pending-progress `R-cross-lam ⊨e/fb
  pending@record { tyVarsWit = ((τₐ , τᵣ) , refl)
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where (here refl) → ψ₁(here refl))
                         ((refl ,′ refl) ,′ refl)
ctc-pending-progress `R-merge-box
  ⊨e/fb@(B/i ix ix′ ix◁ix′ (τ/fo , e-prx/fb@()) esat)
  pending@record { tyVarsWit = (τ′ , refl)
                 ; term₁ = mkTerm ψ₁ refl }
ctc-pending-progress `R-merge-lam
  ⊨e/fb@(B/i ix ix′ ix◁ix′ (τ/fo , e-prx/fb@()) esat)
  pending@record { tyVarsWit = (τ′ , refl)
                 ; term₁ = mkTerm ψ₁ refl }
ctc-pending-progress `R-proxy-unbox ⊨e/fb
  pending@record { tyVarsWit = tt
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where (here refl) → box/c-κ (ψ₁(here refl)))
                         ((refl ,′ refl) ,′ refl)
ctc-pending-progress `R-proxy-β ⊨e/fb
  pending@record { tyVarsWit = τₐ
                 ; term₁ = mkTerm ψ₁ refl }
  = _ , _ , Pending⇒Step pending
                         (λ where
                           (here refl)         → →/c-dom-κ (ψ₁(here refl))
                           (there (here refl)) → →/c-rng-κ (ψ₁(here refl)))
                         ((refl ,′ refl) ,′ (refl ,′ refl))

{-
test : (ϑ : ∀ {Γτ} → Γτ ∈ (([] ,′ `ℕ) ∷ []) → Ann ∣ proj₁ Γτ ⊢ proj₂ Γτ) → Ann ∣ ϑ(here refl) isvalof `ℕ → _
test ϑ isval =
  𝒯c id𝒜view `R-cross-nat (`ℕ , refl) (ϑ , isval)
-}
