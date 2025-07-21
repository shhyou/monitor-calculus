{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; pred)

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.Bounded.NonRecursiveHeight
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (stronger? : SEPred Label 𝒜 → SEPred Label 𝒜 → Dec ⊤)
  (H : ℕ)
  where

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length; map)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; _∘′_; flip′)

open import Utils.Misc
open import Data.Tick using (Tick; evalTick; execTick; ✓_)
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Interpretation

open import Contract.Common Label
open import Contract.Base Label 𝒜
open import SpaceEfficient.Base Label 𝒜
open import SpaceEfficient.Height Label 𝒜
open import SpaceEfficient.NonRecursive Label 𝒜
open import SpaceEfficient.Properties.Height Label 𝒜cctc-view stronger?
open import SpaceEfficient.Properties.NonRecursive Label 𝒜cctc-view stronger?
open AnnTerm 𝒜 hiding (State)

open AnnTermView 𝒜cctc-view using (getAnn)
open SECtcTransitSteps 𝒜cctc-view stronger?

ℐnrheight : AnnIntr 𝒯cctc
AnnIntr.Ix         ℐnrheight = ⊤
AnnIntr.IxRel      ℐnrheight cκ ix ix′ = ⊤
AnnIntr.Ord        ℐnrheight = trivialOrd
AnnIntr.isPreorder ℐnrheight = trivialOrdIsPreorder
AnnIntr.Inv        ℐnrheight s = ⊤
AnnIntr.𝔹          ℐnrheight A ix◁ix′ e =
  SECtcNonRecursive cκ ×
  SECtcMaxH cκ H
  where cκ = getAnn A
AnnIntr.𝔹Sound     ℐnrheight (R-redex step)            inv inv′ mono cnr,cmh = cnr,cmh
AnnIntr.𝔹Sound     ℐnrheight (R-bdr rule-no s s′ step) inv inv′ mono cnr,cmh = cnr,cmh
AnnIntr.ℙ          ℐnrheight A ix◁ix′ em =
  AnnIntr.𝔹 ℐnrheight A ix◁ix′ ⌊ em ⌋m


ℐnrheight-monotonic : AnnTransitInterpIs ℐnrheight Monotonic
ℐnrheight-monotonic tag step esat₁ termSat = tt , tt

ℐnrheight-sound : AnnTransitInterpIs ℐnrheight Sound
ℐnrheight-sound `R-cross-unit {s₁ = s₁}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (s₁-status-eq , refl))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐnrheight-sound `R-cross-nat {s₁ = s₁} {s₂}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , (s₁-status-eq , refl) , cκ-checks-tr))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐnrheight-sound `R-cross-cons {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq₁ , cκ-eq₂))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        ( tt ,
          subst SECtcNonRecursive (sym cκ-eq₁) (cnr-*₁ cnr) ,′
          subst (flip′ SECtcMaxH H) (sym cκ-eq₁) (cmh-*₁ cκmh) ) ,′
        ( tt ,
          subst SECtcNonRecursive (sym cκ-eq₂) (cnr-*₂ cnr) ,′
          subst (flip′ SECtcMaxH H) (sym cκ-eq₂) (cmh-*₂ cκmh) )
    }
ℐnrheight-sound `R-cross-inl {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-+₁ cnr) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-+₁ cκmh)
    }
ℐnrheight-sound `R-cross-inr {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-+₂ cnr) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-+₂ cκmh)
    }
ℐnrheight-sound `R-cross-roll {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  (record { boundarySat = _ , cnr@() , cκmh }) -- cnr@() ,IMPOSSIBLE
  inv′,mono
ℐnrheight-sound `R-cross-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) cnr ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) cκmh
    }
ℐnrheight-sound `R-cross-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) cnr ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) cκmh
    }
ℐnrheight-sound `R-merge-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  (record { inv = I ; boundarySat = (_ , cnr , cκmh) , (_ , cnr′ , cκmh′) })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-join cnr′ cnr) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-join cκmh′ cκmh)
    }
ℐnrheight-sound `R-merge-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  (record { inv = I ; boundarySat = (_ , cnr , cκmh) , (_ , cnr′ , cκmh′) })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-join cnr′ cnr) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-join cκmh′ cκmh)
    }
ℐnrheight-sound `R-proxy-unbox {s₁ = s₁}
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-box cnr) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-box cκmh)
    }
ℐnrheight-sound `R-proxy-β {s₁ = s₁}
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκₐ-eq , cκᵣ-eq))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  (record { boundarySat = _ , cnr , cκmh })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        ( tt ,
          subst SECtcNonRecursive (sym cκᵣ-eq) (cnr-rng cnr) ,′
          subst (flip′ SECtcMaxH H) (sym cκᵣ-eq) (cmh-rng cκmh) ) ,′
        ( tt ,
          subst SECtcNonRecursive (sym cκₐ-eq) (cnr-dom cnr) ,′
          subst (flip′ SECtcMaxH H) (sym cκₐ-eq) (cmh-dom cκmh) )
    }
