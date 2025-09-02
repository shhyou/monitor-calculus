{-# OPTIONS --safe --without-K #-}

open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Bounded.Size
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (OP : SEOrderedPredicate Label 𝒜 (AnnTermView.getState 𝒜cctc-view) (AnnTermView.putState 𝒜cctc-view))
  (H : ℕ)
  where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_∘′_; flip′)

open import Utils.Misc
open import Data.Tick using (Tick; evalTick; execTick; ✓_)
open import Data.IsNonEmpty
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Invariant

open import Contract.Common Label
open import Contract.Base Label 𝒜
open SpaceEfficient.OrderedPredicate Label 𝒜
open import SpaceEfficient.Base Label 𝒜

open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)

open import SpaceEfficient.Size Label 𝒜
open import SpaceEfficient.Height Label 𝒜
open import SpaceEfficient.NonRecursive Label 𝒜
open import SpaceEfficient.LeafPredicate Label 𝒜
open import SpaceEfficient.Properties.UniqueSublist Label 𝒜cctc-view OP
open import SpaceEfficient.Properties.Height Label 𝒜cctc-view stronger?
open import SpaceEfficient.Properties.NonRecursive Label 𝒜cctc-view stronger?
open import SpaceEfficient.Properties.Size Label 𝒜cctc-view stronger?

open AnnTerm 𝒜 hiding (State)
open AnnTermView 𝒜cctc-view using (getAnn)
open SECtcTransitSteps 𝒜cctc-view stronger?

ℐsize : (c : ℕ) → AnnInvr 𝒯cctc
AnnInvr.Ix         (ℐsize _) = ℕ
AnnInvr.IxRel      (ℐsize c) A ix ix′ = c ≡ ix × c ≡ ix′
AnnInvr.Ord        (ℐsize _) = trivialOrd
AnnInvr.isPreorder (ℐsize _) = trivialOrdIsPreorder
AnnInvr.Inv        (ℐsize _) s = ⊤
AnnInvr.𝔹          (ℐsize _) A {ix = c} ix◁ix′ e =
  SECtcNonRecursive cκ ×
  SECtcPreds (ord-preds ⊇#_) cκ ×
  SECtcMaxH cκ H ×
  sectc-size cκ ≤ c * 2 ^ H * length ord-preds
  where cκ = getAnn A
AnnInvr.𝔹Sound     (ℐsize _) (R-redex step)        inv inv′ mono cnr,c#⊆U,cmh,bnd = cnr,c#⊆U,cmh,bnd
AnnInvr.𝔹Sound     (ℐsize _) (R-bdr tag s s′ step) inv inv′ mono cnr,c#⊆U,cmh,bnd = cnr,c#⊆U,cmh,bnd
AnnInvr.ℙ          (ℐsize c) A ix◁ix′ em =
  AnnInvr.𝔹 (ℐsize c) A ix◁ix′ ⌊ em ⌋m


USublist⇒BoundedLen : ∀ {Δ τ cκ} →
  SECtcPreds (ord-preds ⊇#_) cκ →
  SECtcPreds ((_≤ length ord-preds) ∘′ length) {Δ} {τ} cκ
USublist⇒BoundedLen = cps-map USublist-length




c₀ = proj₁ sectc-bounded
sectc-is-bounded = proj₂ (proj₂ sectc-bounded)
1≤|ord-preds| = IsNonEmpty-length ord-preds-nonempty

ℐsize-monotonic : AnnInvrIs (ℐsize c₀) Monotonic
ℐsize-monotonic tag step esat₁ termSat = tt , tt

ℐsize-sound : AnnInvrIs (ℐsize c₀) Sound
ℐsize-sound `R-cross-unit {s₁ = s₁}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (s₁-status-eq , refl))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐsize-sound `R-cross-nat {s₁ = s₁} {s₂}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit@n-is-val
          (.s₁ , (s₁-status-eq , refl) , cκ-checks-tr))
  esat
  (record { isSatIx = ix◁ix′ , intrix })
  inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = relabel-nat-val n-is-val
    ; boundarySat = tt
    }
ℐsize-sound `R-cross-cons {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq₁ , cκ-eq₂))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (esat₁ `, esat₂))
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrix₁ , intrix₂ })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx =
        refl ,′
        (subst (ℐsize c₀ ⊨[_] _) (sym intrix₁)) ,′
        refl ,′
        (subst (ℐsize c₀ ⊨[_] _) (sym intrix₂))
    ; boundarySat =
        ( ix◁ix′ ,
          subst SECtcNonRecursive (sym cκ-eq₁) (cnr-*₁ cnr) ,′
          cκ₁-us ,′
          cmh₁ ,′
          |cκ₁|≤bnd ) ,′
        ( ix◁ix′ ,
          subst SECtcNonRecursive (sym cκ-eq₂) (cnr-*₂ cnr) ,′
          cκ₂-us ,′
          cmh₂ ,′
          |cκ₂|≤bnd )
    }
    where cκ₁-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq₁) (cps-*₁ cκ-us)
          cmh₁   = subst (flip′ SECtcMaxH H) (sym cκ-eq₁) (cmh-*₁ cmh)
          cκ₂-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq₂) (cps-*₂ cκ-us)
          cmh₂   = subst (flip′ SECtcMaxH H) (sym cκ-eq₂) (cmh-*₂ cmh)

          |cκ₁|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh₁ (USublist⇒BoundedLen cκ₁-us)
          |cκ₂|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh₂ (USublist⇒BoundedLen cκ₂-us)
ℐsize-sound `R-cross-inl {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (inl esat))
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-+₁ cnr) ,′
        cκ₁-us ,′
        cmh₁ ,′
        |cκ₁|≤bnd
    }
    where cκ₁-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-+₁ cκ-us)
          cmh₁   = subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-+₁ cmh)

          |cκ₁|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh₁ (USublist⇒BoundedLen cκ₁-us)
ℐsize-sound `R-cross-inr {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (inr esat))
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-+₂ cnr) ,′
        cκ₂-us ,′
        cmh₂ ,′
        |cκ₂|≤bnd
    }
    where cκ₂-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-+₂ cκ-us)
          cmh₂   = subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-+₂ cmh)

          |cκ₂|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh₂ (USublist⇒BoundedLen cκ₂-us)
ℐsize-sound `R-cross-roll {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (roll .τ′ esat))
  (record { boundarySat = _ , cnr@() , cκ-us , cmh , |cκ| }) -- cnr@() IMPOSSIBLE
  inv′,mono
ℐsize-sound `R-cross-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (box esat))
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) cnr ,′
        cκ′-us ,′
        cmh′ ,′
        |cκ′|≤bnd
    }
    where cκ′-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) cκ-us
          cmh′   = subst (flip′ SECtcMaxH H) (sym cκ-eq) cmh

          |cκ′|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh′ (USublist⇒BoundedLen cκ′-us)
ℐsize-sound `R-cross-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (ƛ esat))
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) cnr ,′
        cκ′-us ,′
        cmh′ ,′
        |cκ′|≤bnd
    }
    where cκ′-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) cκ-us
          cmh′   = subst (flip′ SECtcMaxH H) (sym cκ-eq) cmh

          |cκ′|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh′ (USublist⇒BoundedLen cκ′-us)
ℐsize-sound `R-merge-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″@(refl , refl) psat (box esatm)))
  (record { boundarySat = (_ , cnr , cκ-us , cmh , |cκ|) ,
                          (_ , cnr′ , cκ-us′ , cmh′ , |cκ′|)
          ; isSatIx = (ix~ctxt , ix′~ann) , (ix′~ctxt′ , ix″~ann′) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-join cnr′ cnr) ,′
        cκ″-us ,′
        cmh″ ,′
        |cκ″|≤bnd
    }
    where cκ″-us  = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq)
                          (cps-join 𝒜cctc-view stronger? usublist-join-flats cκ-us′ cκ-us)
          cmh″    = subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-join cmh′ cmh)

          |cκ″|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh″ (USublist⇒BoundedLen cκ″-us)
ℐsize-sound `R-merge-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (B/i ix ix′ ix◁ix′@(refl , _) bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″@(refl , refl) psat (ƛ esat)))
  (record { boundarySat = (_ , cnr , cκ-us , cmh , |cκ|) ,
                          (_ , cnr′ , cκ-us′ , cmh′ , |cκ′|)
          ; isSatIx = (ix~ctxt , ix′~ann) , (ix′~ctxt′ , ix″~ann′) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-join cnr′ cnr) ,′
        cκ″-us ,′
        cmh″ ,′
        |cκ″|≤bnd
    }
    where cκ″-us  = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq)
                          (cps-join 𝒜cctc-view stronger? usublist-join-flats cκ-us′ cκ-us)
          cmh″    = subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-join cmh′ cmh)

          |cκ″|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh″ (USublist⇒BoundedLen cκ″-us)
ℐsize-sound `R-proxy-unbox {s₁ = s₁}
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκ-eq))
  (unbox (proxy/i em ix ix′ ix◁ix′@(refl , _) psat (box esat)))
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrix })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐsize c₀ ⊨[_] _) (sym intrix)
    ; boundarySat =
        ix◁ix′ ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-box cnr) ,′
        cκ′-us ,′
        cmh′ ,′
        |cκ′|≤bnd
    }
    where cκ′-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-box cκ-us)
          cmh′   = subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-box cmh)

          |cκ′|≤bnd = sectc-is-bounded 1≤|ord-preds| cmh′ (USublist⇒BoundedLen cκ′-us)
ℐsize-sound `R-proxy-β {s₁ = s₁}
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          ((s₁-status-eq , refl) , cκₐ-eq , cκᵣ-eq))
  ((proxy/i em ix ix′ ix◁ix′@(refl , refl) psat (ƛ esat)) · esatₐ)
  (record { boundarySat = _ , cnr , cκ-us , cmh , |cκ|
          ; isSatIx = (ix~ctxt , ix′~ann) , intrixᵣ , intrixₐ })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx =
        refl ,′
        (subst (ℐsize c₀ ⊨[_] _) (sym intrixᵣ)) ,′
        refl ,′
        (subst (ℐsize c₀ ⊨[_] _) (sym intrixₐ))
    ; boundarySat =
        ( ix◁ix′ ,
          subst SECtcNonRecursive (sym cκᵣ-eq) (cnr-rng cnr) ,′
          cκᵣ-us ,′
          cmhᵣ ,′
          |cκᵣ|≤bnd ) ,′
        ( (proj₂ ix◁ix′ ,′ proj₁ ix◁ix′) ,
          subst SECtcNonRecursive (sym cκₐ-eq) (cnr-dom cnr) ,′
          cκₐ-us ,′
          cmhₐ ,′
          |cκₐ|≤bnd )
    }
    where cκᵣ-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκᵣ-eq) (cps-rng cκ-us)
          cmhᵣ   = subst (flip′ SECtcMaxH H) (sym cκᵣ-eq) (cmh-rng cmh)
          cκₐ-us = subst (SECtcPreds (ord-preds ⊇#_)) (sym cκₐ-eq) (cps-dom cκ-us)
          cmhₐ   = subst (flip′ SECtcMaxH H) (sym cκₐ-eq) (cmh-dom cmh)

          |cκᵣ|≤bnd = sectc-is-bounded 1≤|ord-preds| cmhᵣ (USublist⇒BoundedLen cκᵣ-us)
          |cκₐ|≤bnd = sectc-is-bounded 1≤|ord-preds| cmhₐ (USublist⇒BoundedLen cκₐ-us)
