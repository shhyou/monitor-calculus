{-# OPTIONS --without-K --safe #-}

module Example.Count.NonDecreasingInterpretation where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Language
open import Annotation.Interpretation
open import Annotation.Soundness
open import Example.Count.Annotation

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; sym; subst; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
import Data.Nat.Properties as Nat
open import Data.Product.Base as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_on_; _∘′_; id)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ann : AnnSig

module _ {𝒜 : AnnTerm} (𝒜view : AnnTermView 𝒜 𝒜cnt) where
  open AnnTerm 𝒜 using (Ann; State)
  open AnnTermViewUtils 𝒜view

  ℐinc : ∀ 𝒯 → AnnIntr {𝒜} (𝒯 ∩tr 𝒯cnt 𝒜view)
  AnnIntr.Ix         (ℐinc 𝒯) = ⊤
  AnnIntr.IxRel      (ℐinc 𝒯) A ix ix′ = ⊤
  AnnIntr.Inv        (ℐinc 𝒯) s = ⊤
  AnnIntr.Ord        (ℐinc 𝒯) = _≤_ on (getState ∘′ proj₁)
  AnnIntr.isPreorder (ℐinc 𝒯) =
    record  { isEquivalence = PropEq.isEquivalence
            ; reflexive = Nat.≤-reflexive ∘′ cong (getState ∘′ proj₁)
            ; trans = Nat.≤-trans
            }
  AnnIntr.𝔹          (ℐinc 𝒯) A ix◁ix′ e = ⊤
  AnnIntr.𝔹Sound     (ℐinc 𝒯) step inv inv′ mono bsat = bsat
  AnnIntr.ℙ          (ℐinc 𝒯) {τ = τ} A ix◁ix′ em = ⊤

  ℐinc-monotonic : ∀ 𝒯 → AnnTransitInterpIs (ℐinc 𝒯) Monotonic
  ℐinc-monotonic 𝒯 `R-cross-unit {s₁ = s₁}
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat ⋆)
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-nat {s₁ = s₁}
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat esat)
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-cons {s₁ = s₁}
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-inl {s₁ = s₁}
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (inl esat))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-inr {s₁ = s₁}
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (inr esat))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-roll {s₁ = s₁}
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-box {s₁ = s₁}
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (box esat))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-cross-lam {s₁ = s₁}
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-merge-box {s₁ = s₁}
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box esat)))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-merge-lam {s₁ = s₁}
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-proxy-unbox {s₁ = s₁}
    (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁
  ℐinc-monotonic 𝒯 `R-proxy-β {s₁ = s₁}
    (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(tr , c′≡1+c@refl))
    ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
    termSat =
      _ , subst (c ≤_) (sym (AnnTermView.put-get 𝒜view s₁ (suc c))) (Nat.m≤n+m c 1) where c = getState s₁

  ℐinc-sound : ∀ 𝒯 → AnnTransitInterpIs (ℐinc 𝒯) Sound
  ℐinc-sound 𝒯 `R-cross-unit
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat ⋆) termSat inv′,mono = record
      { annCtxtIx = λ ()
      ; annIx = λ ()
      ; isTermIx = tt
      ; boundarySat = tt
      }
  ℐinc-sound 𝒯 `R-cross-nat
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat esat) termSat inv′,mono = record
      { annCtxtIx = λ ()
      ; annIx = λ ()
      ; isTermIx = id
      ; boundarySat = tt
      }
  ℐinc-sound 𝒯 `R-cross-cons
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂)) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id ,′ refl ,′ id
      ; boundarySat = (tt , tt) ,′ (tt , tt)
      }
  ℐinc-sound 𝒯 `R-cross-inl
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat (inl esat)) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-cross-inr
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat (inr esat)) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-cross-roll
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat (roll τ esat)) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-cross-box
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat (box esat)) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-cross-lam
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (B/i ix ix′ ix◁ix′ bsat (ƛ esat)) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
     }
  ℐinc-sound 𝒯 `R-merge-box
    step@(mkStep (τ′ , refl)
            termEnv
            (mkTerm ψ₁ refl)
            (mkTerm ψ₂ refl)
            premWit
            trWit)
    (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
    termSat@record { metaVarIx = mvix₁
                   ; boundarySat = ((tt , tt) , (tt , tt)) }
    mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-merge-lam
    (mkStep ((τₐ , τᵣ) , refl)
            termEnv
            (mkTerm ψ₁ refl)
            (mkTerm ψ₂ refl)
            premWit
            trWit)
    (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esatb)))
    termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-proxy-unbox
    (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat))) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐinc-sound 𝒯 `R-proxy-β
    (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
    ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ) termSat inv′,mono = record
      { annCtxtIx = λ x → tt
      ; annIx = λ x → tt
      ; isTermIx = refl ,′ id ,′ refl ,′ id
      ; boundarySat = (tt , tt) ,′ (tt , tt)
      }
