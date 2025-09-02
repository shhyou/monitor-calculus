{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Contract.Monotonic (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary
  using (IsPreorder; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; subst; sym; trans)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; length; lookup; _++_; map; reverse)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; _∘′_)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Invariant

open import Contract.Common Label
open import Contract.Base Label 𝒜 as StdCtc

open AnnTerm 𝒜

module _ (𝒜view : AnnTermView 𝒜 𝒜sctc) where
  open AnnTermView 𝒜view

  data ErrMono : State × ⊤ → State × ⊤ → Set where
    em-refl : ∀ {s s′}   → (seqs : getState s ≡ getState s′)                      → ErrMono (s , _) (s′ , _)
    em-err  : ∀ {s s′} l → (seq : getState s ≡ Ok) → (seq′ : getState s′ ≡ Err l) → ErrMono (s , _) (s′ , _)

  em-reflexive : ∀ {s,tt s′,tt} → s,tt ≡ s′,tt → ErrMono s,tt s′,tt
  em-reflexive = em-refl ∘′ cong (getState ∘′ proj₁)

  em-trans : ∀ {s₁ s₂ s₃} → ErrMono s₁ s₂ → ErrMono s₂ s₃ → ErrMono s₁ s₃
  em-trans (em-refl s₁≡s₂)         (em-refl s₂≡s₃)         = em-refl (trans s₁≡s₂ s₂≡s₃)
  em-trans (em-refl s₁≡s₂)         (em-err l s₂≡Ok s₃≡Err) = em-err l (trans s₁≡s₂ s₂≡Ok) s₃≡Err
  em-trans (em-err l s₁≡Ok s₂≡Err) (em-refl s₂≡s₃)         = em-err l s₁≡Ok (trans (sym s₂≡s₃) s₂≡Err)
  em-trans (em-err l s₁≡Ok s₂≡Err) (em-err l′ s₂≡Ok s₃≡Err) with trans (sym s₂≡Err) s₂≡Ok
  ... | ()

  emIsPreorder : IsPreorder _≡_ ErrMono
  emIsPreorder = record { isEquivalence = PropEq.isEquivalence
                        ; reflexive = em-reflexive
                        ; trans = em-trans
                        }

  ℐerrmono : ∀ 𝒯 → AnnInvr {𝒜} 𝒯
  AnnInvr.Ix         (ℐerrmono 𝒯) = ⊤
  AnnInvr.IxRel      (ℐerrmono 𝒯) A ix ix′ = ⊤
  AnnInvr.Inv        (ℐerrmono 𝒯) s = ⊤
  AnnInvr.Ord        (ℐerrmono 𝒯) = ErrMono
  AnnInvr.isPreorder (ℐerrmono 𝒯) = emIsPreorder
  AnnInvr.𝔹          (ℐerrmono 𝒯) A ix◁ix′ e = ⊤
  AnnInvr.𝔹Sound     (ℐerrmono 𝒯) step inv inv′ mono bsat = tt
  AnnInvr.ℙ          (ℐerrmono 𝒯) {τ = τ} A ix◁ix′ em = ⊤

  checkNatSCtcsMono : ∀ 𝒯 {n s s′} →
    (sκs : List (SCtc1N [] `ℕ)) →
    checkNatSCtcs 𝒜view 𝒯 sκs n s s′ →
    ErrMono (s , tt) (s′ , tt)
  checkNatSCtcsMono 𝒯 [] checks-tr = em-reflexive (cong (λ s → s , tt) checks-tr)
  checkNatSCtcsMono 𝒯 (flat l e ∷ sκs)
    (s′ , inj₁ (s₁ , (s≡Ok , s≡s₁) , NP-acc iv steps s′≡Ok) , checks-tr)
    = em-trans (em-refl (trans s≡Ok (sym s′≡Ok)))
               (checkNatSCtcsMono 𝒯 sκs checks-tr)
  checkNatSCtcsMono 𝒯 (flat l e ∷ sκs)
    (s′ , inj₁ (s₁ , (s≡Ok , s≡s₁) , NP-rej {s₁ = s₂} steps s₂≡Ok s′:=Err) , checks-tr)
    = em-trans (em-err l s≡Ok (subst (getState s′ ≡_) (put-get s₂ (Err l)) (cong getState s′:=Err)))
               (checkNatSCtcsMono 𝒯 sκs checks-tr)
  checkNatSCtcsMono 𝒯 (flat l e ∷ sκs)
    (s′ , inj₁ (s₁ , (s≡Ok , s≡s₁) , NP-err steps l′ s′≡Err) , checks-tr)
    = em-trans (em-err l′ s≡Ok s′≡Err)
               (checkNatSCtcsMono 𝒯 sκs checks-tr)
  checkNatSCtcsMono 𝒯 (flat l e ∷ sκs)
    (s′ , inj₂ (l′ , s≡Err , s≡s′-full@refl) , checks-tr)
    = checkNatSCtcsMono 𝒯 sκs checks-tr

  ℐerrmono-monotonic : ∀ 𝒯 → AnnInvrIs (ℐerrmono (𝒯sctc 𝒜view 𝒯)) Monotonic
  ℐerrmono-monotonic 𝒯 `R-cross-unit
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(s-eq , s≡s′@refl))
    (B/i ix ix′ ix◁ix′ bsat ⋆)
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-cross-nat
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(s₂ , (s-eq , s≡s₂@refl) , checks-tr))
    (B/i ix ix′ ix◁ix′ bsat esat)
    termSat =
      _ , checkNatSCtcsMono 𝒯 (getAnn(ψ₁(here refl))) checks-tr
  ℐerrmono-monotonic 𝒯 `R-cross-cons
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , (sκs₁-eq , sκs₂-eq)))
    (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-cross-inl
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (inl esat))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-cross-inr
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (inr esat))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-cross-roll
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-cross-box
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (box esat))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-cross-lam
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-merge-box
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box esat)))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-merge-lam
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-proxy-unbox
    (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
    termSat =
      _ , em-refl refl
  ℐerrmono-monotonic 𝒯 `R-proxy-β
    (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , (sκsₐ-eq , sκsᵣ-eq)))
    ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
    termSat =
      _ , em-refl refl

  ℐerrmono-sound : ∀ 𝒯 → AnnInvrIs (ℐerrmono (𝒯sctc 𝒜view 𝒯)) Sound
  ℐerrmono-sound 𝒯 `R-cross-unit
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(s-eq , s≡s′@refl))
    (B/i ix ix′ ix◁ix′ bsat ⋆)
    termSat inv′,mono = record
      { annCtxtIx = λ ()
      ; annIx = λ ()
      ; isTermIx = tt
      ; boundarySat = tt
      }
  ℐerrmono-sound 𝒯 `R-cross-nat
    (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@(s₂ , (s-eq , s≡s₂) , checks-tr))
    (B/i ix ix′ ix◁ix′ bsat esat)
    termSat inv′,mono = record
      { annCtxtIx = λ ()
      ; annIx = λ ()
      ; isTermIx = id
      ; boundarySat = tt
      }
  ℐerrmono-sound 𝒯 `R-cross-cons
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , (sκs₁-eq , sκs₂-eq)))
    (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
    termSat inv′,mono = record
      { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
      ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
      ; isTermIx = refl ,′ id ,′ refl ,′ id
      ; boundarySat = (tt , tt) ,′ (tt , tt)
      }
  ℐerrmono-sound 𝒯 `R-cross-inl
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (inl esat))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix′ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-cross-inr
    (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (inr esat))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix′ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-cross-roll
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix′ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-cross-box
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (box esat))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix′ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-cross-lam
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix′ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-merge-box
    (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box esat)))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix″ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-merge-lam
    (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix″ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-proxy-unbox
    (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , sκs-eq))
    (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
    termSat inv′,mono = record
      { annCtxtIx = [ix↦ ix ]
      ; annIx = [ix↦ ix′ ]
      ; isTermIx = refl ,′ id
      ; boundarySat = tt , tt
      }
  ℐerrmono-sound 𝒯 `R-proxy-β
    (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
      trWit@((s-eq , s≡s′@refl) , (sκsₐ-eq , sκsᵣ-eq)))
    ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
    termSat inv′,mono = record
      { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
      ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
      ; isTermIx = refl ,′ id ,′ refl ,′ id
      ; boundarySat = (tt , tt) ,′ (tt , tt)
      }
