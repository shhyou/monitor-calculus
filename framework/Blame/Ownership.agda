{-# OPTIONS --without-K --safe #-}

open import Annotation.Language
open import Blame.Base
  using (module AnnBlameContractLang)
  renaming (𝒜owner to B𝒜owner)
open AnnBlameContractLang
  using ()
  renaming (𝒜blame to B𝒜blame)

module Blame.Ownership
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜owner-view : AnnTermView 𝒜 (B𝒜owner Label))
  (𝒜blame-view : AnnTermView 𝒜 (B𝒜blame Label 𝒜))
  where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; sym; subst; trans; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; step-≡-⟨; step-≡-⟩; step-≡-∣)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; curry; uncurry)
import Data.Product.Properties as Product

open import Data.List.Base as List using (List; []; _∷_; _++_; map; reverse)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
import Data.List.Relation.Unary.All.Properties as ListAll
import Data.List.Properties as List

open import Function.Base using (id; const; constᵣ; _∘_)

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Invariant

open Blame.Base Label hiding (module AnnBlameContractLang)
open import Contract.Common Label
open import Contract.Base Label 𝒜
open import Contract.Satisfaction Label 𝒜
open AnnTerm 𝒜

open AnnBlameContractLang Label 𝒜

private variable
  τ : Ty

𝒜sctc-view  : AnnTermView 𝒜 𝒜sctc
𝒜sctc-view = annTermViewCompose 𝒜blame-sctc-view 𝒜blame-view

𝒜blameobj-view : AnnTermView 𝒜 𝒜blameobj
𝒜blameobj-view = annTermViewCompose 𝒜blame-blameobj-view 𝒜blame-view

getOwner     : Ann τ → Label × Label
getOwner     = AnnTermView.getAnn 𝒜owner-view

getBSCtc     : Ann τ → List (Blame × SCtc1 τ)
getBSCtc     = AnnTermView.getAnn 𝒜blame-view

getSCtc      : Ann τ → List (SCtc1 τ)
getSCtc      = AnnTermView.getAnn 𝒜sctc-view

getBlameObj  : Ann τ → List Blame
getBlameObj  = AnnTermView.getAnn 𝒜blameobj-view

𝒯 : ℕ → AnnTransit 𝒜
𝒯 zero    = ∅tr
𝒯 (suc i) = 𝒯blame 𝒜blameobj-view ∩tr  𝒯owner 𝒜owner-view ∩tr  (𝒯sctc 𝒜sctc-view (𝒯 i))

infixr 5 _++ᵇ_
infixr 5 _∷_

data BlameSeq : Label → Label → List Blame → Set where
  [] : ∀ {l} → BlameSeq l l []
  _∷_ : ∀ {bs l} →
    (b : Blame) →
    BlameSeq (bneg b) l bs →
    BlameSeq (bpos b) l (b ∷ bs)

_++ᵇ_ : ∀ {l j k bs bs′} → BlameSeq k j bs → BlameSeq j l bs′ → BlameSeq k l (bs ++ bs′)
[]        ++ᵇ bs₂ = bs₂
(b ∷ bs₁) ++ᵇ bs₂ = b ∷ (bs₁ ++ᵇ bs₂)

reverseᵇ : ∀ {l k bs} → BlameSeq k l bs → BlameSeq l k (reverse (map blame-swap bs))
reverseᵇ                [] = []
reverseᵇ {bs = .b ∷ bs} (b ∷ bs′)
  rewrite List.unfold-reverse (blame-swap b) (map blame-swap bs)
  = reverseᵇ bs′ ++ᵇ (blame-swap b ∷ [])

SCtcSat′ : ∀ {𝒯} (ℐ : AnnInvr 𝒯) {τ} → SCtc1N [] τ → Set
SCtcSat′ ℐ sκ = ∃[ j ] SCtcSat ℐ j sκ

ℐowner : (i : ℕ) → AnnInvr (𝒯 i)
AnnInvr.Ix         (ℐowner i) = Label
AnnInvr.IxRel      (ℐowner i) obsκs ix ix′ = BlameSeq ix′ ix (getBlameObj obsκs)
AnnInvr.Inv        (ℐowner i) s = ⊤
AnnInvr.Ord        (ℐowner i) = trivialOrd
AnnInvr.isPreorder (ℐowner i) = trivialOrdIsPreorder
AnnInvr.𝔹          (ℐowner zero)    obsκs ix◁ix′ e = ⊥
AnnInvr.𝔹          (ℐowner (suc i)) obsκs {ix = ix} {ix′} ix◁ix′ e =
  (ix , ix′) ≡ getOwner obsκs ×
  All (SCtcSat′ (ℐowner i) ∘ proj₂) (getBSCtc obsκs)
AnnInvr.𝔹Sound     (ℐowner zero)    step inv inv′ mono ()
AnnInvr.𝔹Sound     (ℐowner (suc i)) step inv inv′ mono (bs-own-eq , j-κsats) =
  bs-own-eq ,′ j-κsats
AnnInvr.ℙ          (ℐowner i) obsκs ix◁ix′ em =
  AnnInvr.𝔹 (ℐowner i) obsκs ix◁ix′ ⌊ em ⌋m

ℐowner-monotonic : ∀ i → AnnInvrIs (ℐowner i) Monotonic
ℐowner-monotonic zero    tag step esat₁ termSat = tt , tt
ℐowner-monotonic (suc i) tag step esat₁ termSat = tt , tt

ℐowner-sound : ∀ i → AnnInvrIs (ℐowner i) Sound
ℐowner-sound zero `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound zero `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐowner-sound (suc i) `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat ⋆)
  termSat
  inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐowner-sound (suc i) `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit@n-is-val
    trWit)
  (B/i ix ix′ ix◁ix′ bsat esat)
  termSat@record { boundarySat = _ , j-κsats
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = relabel-nat-val n-is-val
    ; boundarySat = tt
    }
ℐowner-sound (suc i) `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((bs₁-eq , bs₂-eq) , (owns₁-eq , owns₂-eq) , (s-eq , refl) , (sκs₁-eq , sκs₂-eq)))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix₁ , intrix₂ }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx =
        refl ,′
        (subst (ℐowner (suc i) ⊨[_] _) (sym intrix₁)) ,′
        refl ,′
        (subst (ℐowner (suc i) ⊨[_] _) (sym intrix₂))
    ; boundarySat =
       (subst (BlameSeq ix′ ix) (sym bs₁-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns₁-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all-map₂-subst (SCtcSat′ (ℐowner i))
                        */c-sκ₁
                        (sym sκs₁-eq)
                        (ListAll.map (Product.map₂ sκsat-*₁) j-κsats)) ,′
       (subst (BlameSeq ix′ ix) (sym bs₂-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns₂-eq ⟨
                getOwner(ψ₂(there (here refl))) ∎) ,′
        all-map₂-subst (SCtcSat′ (ℐowner i))
                        */c-sκ₂
                        (sym sκs₂-eq)
                        (ListAll.map (Product.map₂ sκsat-*₂) j-κsats))
    }
ℐowner-sound (suc i) `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix′ ix) (sym bs-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all-map₂-subst (SCtcSat′ (ℐowner i))
                        +/c-sκ₁
                        (sym sκs-eq)
                        (ListAll.map (Product.map₂ sκsat-+₁) j-κsats)
    }
ℐowner-sound (suc i) `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix′ ix) (sym bs-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all-map₂-subst (SCtcSat′ (ℐowner i))
                        +/c-sκ₂
                        (sym sκs-eq)
                        (ListAll.map (Product.map₂ sκsat-+₂) j-κsats)
    }
ℐowner-sound (suc i) `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix′ ix) (sym bs-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all-map₂-subst (SCtcSat′ (ℐowner i))
                        μ/c-sκ
                        (sym sκs-eq)
                        (ListAll.map (Product.map₂ sκsat-μ) j-κsats)
    }
ℐowner-sound (suc i) `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix′ ix) (sym bs-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all₂-subst (SCtcSat′ (ℐowner i)) (sym sκs-eq) j-κsats
    }
ℐowner-sound (suc i) `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix′ ix) (sym bs-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all₂-subst (SCtcSat′ (ℐowner i)) (sym sκs-eq) j-κsats
    }
ℐowner-sound (suc i) `R-merge-box
  step@(mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(bs-eq , (owns-eq , match-eq) , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  termSat@record { boundarySat = (_ , (bs-own-eq , j-κsats)) , (_ , (bs-own-eq′ , j-κsats′))
                 ; isSatIx = (ix~ctxt , ix′~ann) , (ix′~ctxt′ , ix″~ann′) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix″ ix) (sym bs-eq) (ix′◁ix″ ++ᵇ ix◁ix′) ,
        (begin (ix ,′ ix″)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix″~ann′) ⟩
                _
            ≡⟨ Product.×-≡,≡→≡ (cong proj₁ bs-own-eq ,′ cong proj₂ bs-own-eq′) ⟩
                (proj₁ (getOwner(ψ₁(here refl))) ,′ proj₂ (getOwner(ψ₁(there (here refl)))))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all₂-subst (SCtcSat′ (ℐowner i))
                    (sym (trans sκs-eq (sym (List.map-++  proj₂
                                                          (getBSCtc(ψ₁(there (here refl))))
                                                          (getBSCtc(ψ₁(here refl)))))))
                    (ListAll.++⁺ j-κsats′ j-κsats)
    }
ℐowner-sound (suc i) `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , (owns-eq , match-eq) , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esatb)))
  termSat@record { boundarySat = (_ , (bs-own-eq , j-κsats)) , (_ , (bs-own-eq′ , j-κsats′))
                 ; isSatIx = (ix~ctxt , ix′~ann) , (ix′~ctxt′ , ix″~ann′) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix″ ix) (sym bs-eq) (ix′◁ix″ ++ᵇ ix◁ix′) ,
        (begin (ix ,′ ix″)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix″~ann′) ⟩
                _
            ≡⟨ Product.×-≡,≡→≡ (cong proj₁ bs-own-eq ,′ cong proj₂ bs-own-eq′) ⟩
                (proj₁ (getOwner(ψ₁(here refl))) ,′ proj₂ (getOwner(ψ₁(there (here refl)))))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all₂-subst (SCtcSat′ (ℐowner i))
                    (sym (trans sκs-eq (sym (List.map-++  proj₂
                                                          (getBSCtc(ψ₁(there (here refl))))
                                                          (getBSCtc(ψ₁(here refl)))))))
                    (ListAll.++⁺ j-κsats′ j-κsats)
    }
ℐowner-sound (suc i) `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ subst (ℐowner (suc i) ⊨[_] _) (sym intrix)
    ; boundarySat =
        subst (BlameSeq ix′ ix) (sym bs-eq) ix◁ix′ ,
        (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ owns-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
        all-map₂-subst (SCtcSat′ (ℐowner i))
                        box/c-sκ
                        (sym sκs-eq)
                        (ListAll.map (Product.map₂ sκsat-box) j-κsats)
    }
ℐowner-sound (suc i) `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((bsₐ-eq , bsᵣ-eq) , (ownsₐ-eq , ownsᵣ-eq) , (s-eq , refl) , (sκsₐ-eq , sκsᵣ-eq)))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat@record { boundarySat = _ , (bs-own-eq , j-κsats)
                 ; isSatIx = (ix~ctxt , ix′~ann) , intrix , intrixₐ }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx =
        refl ,′
        (subst (ℐowner (suc i) ⊨[_] _) (sym intrix)) ,′
        refl ,′
        (subst (ℐowner (suc i) ⊨[_] _) (sym intrixₐ))
    ; boundarySat =
        (subst (BlameSeq ix′ ix) (sym bsᵣ-eq) ix◁ix′ ,
         (begin (ix , ix′)
            ≡⟨ Product.×-≡,≡→≡ (ix~ctxt ,′ ix′~ann) ⟩
                _
            ≡⟨ bs-own-eq ⟩
                getOwner(ψ₁(here refl))
            ≡⟨ ownsᵣ-eq ⟨
                getOwner(ψ₂(there (here refl))) ∎) ,′
         all-map₂-subst (SCtcSat′ (ℐowner i))
                        →/c-rng-sκ
                        (sym sκsᵣ-eq)
                        (ListAll.map (Product.map₂ sκsat-rng) j-κsats)) ,′
        (subst (BlameSeq ix ix′) (sym bsₐ-eq) (reverseᵇ ix◁ix′) ,
         (begin (ix′ ,′ ix)
            ≡⟨ Product.×-≡,≡→≡ (ix′~ann ,′ ix~ctxt) ⟩
                _
            ≡⟨ Product.×-≡,≡→≡ (cong proj₂ bs-own-eq ,′ cong proj₁ bs-own-eq) ⟩
                (proj₂ (getOwner(ψ₁(here refl))) ,′ proj₁ (getOwner(ψ₁(here refl))))
            ≡⟨ ownsₐ-eq ⟨
                getOwner(ψ₂(here refl)) ∎) ,′
         all-reverse-map₂-subst (SCtcSat′ (ℐowner i))
                                →/c-dom-sκ
                                (getBSCtc(ψ₁(here refl)))
                                (sym sκsₐ-eq)
                                (all-reverse (ListAll.map (Product.map₂ sκsat-dom) j-κsats)))
      }
