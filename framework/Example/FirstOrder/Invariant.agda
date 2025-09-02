{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Example.FirstOrder.Invariant (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product.Base as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id)

open import Utils.Misc  -- for trivialOrd and trivialOrdIsPreorder
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Invariant
open import Example.FirstOrder.FirstOrderTy 𝒜
open import Example.FirstOrder.FlatBoundaryExpr 𝒜

open AnnTerm 𝒜 using (Ann; State)

private variable
  𝒯 : AnnTransit 𝒜

  Δ Δ′ : TCtxt
  Γ : Ctxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ
  e : Ann ∣ Γ ⊢ τ

ℐfstord : ∀ 𝒯 → AnnInvr {𝒜} 𝒯
AnnInvr.Ix         (ℐfstord 𝒯) = ⊤
AnnInvr.IxRel      (ℐfstord 𝒯) A ix ix′ = ⊤
AnnInvr.Inv        (ℐfstord 𝒯) s = ⊤
AnnInvr.Ord        (ℐfstord 𝒯) = trivialOrd
AnnInvr.isPreorder (ℐfstord 𝒯) = trivialOrdIsPreorder
AnnInvr.𝔹          (ℐfstord 𝒯) {τ = τ} A ix◁ix′ e =
  FirstOrderTy τ × FlatBdrExpr e
AnnInvr.𝔹Sound (ℐfstord 𝒯) (R-redex step)        inv inv′ mono (τ/fo , e/fb) =
  τ/fo ,′
  fbexpr-ctxt fbexpr-betarel step e/fb
AnnInvr.𝔹Sound (ℐfstord 𝒯) (R-bdr tag s s′ step) inv inv′ mono (τ/fo , e/fb) =
  τ/fo ,′
  fbexpr-ctxt (fbexpr-bdrrel 𝒯 tag) step e/fb
AnnInvr.ℙ (ℐfstord 𝒯) A ix◁ix′ em =
  AnnInvr.𝔹 (ℐfstord 𝒯) A ix◁ix′ ⌊ em ⌋m

ℐfstord-monotonic : ∀ 𝒯 → AnnInvrIs (ℐfstord 𝒯) Monotonic
ℐfstord-monotonic 𝒯 tag step esat₁ termSat = tt , tt

ℐfstord-sound : ∀ 𝒯 → AnnInvrIs (ℐfstord 𝒯) Sound
ℐfstord-sound 𝒯 `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat ⋆)
  termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐfstord-sound 𝒯 `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat esat)
  termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐfstord-sound 𝒯 `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat@record { boundarySat = tt , flat/fo (τ₁/ft */f τ₂/ft) , (e₁/fb ,/fb e₂/fb) }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
       (tt ,
        flat/fo τ₁/ft ,′
        e₁/fb) ,′
       (tt ,
        flat/fo τ₂/ft ,′
        e₂/fb)
    }
ℐfstord-sound 𝒯 `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat@record { boundarySat = tt , flat/fo (τ₁/ft +/f τ₂/ft) , inl/fb e/fb }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        flat/fo τ₁/ft ,′
        e/fb
    }
ℐfstord-sound 𝒯 `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat@record { boundarySat = tt , flat/fo (τ₁/ft +/f τ₂/ft) , inr/fb e/fb }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        flat/fo τ₂/ft ,′
        e/fb
    }
ℐfstord-sound 𝒯 `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat@record { boundarySat = tt , flat/fo (μ/f τ′/ft) , roll/fb e/fb }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        flat/fo (ftsubst τ′/ft [ft0↦ μ/f τ′/ft ]) ,′
        e/fb
    }
ℐfstord-sound 𝒯 `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat@record { boundarySat = tt , box/fo τ′/fo , eb/fb }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        box/fo τ′/fo ,′
        eb/fb
    }
ℐfstord-sound 𝒯 `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat@record { boundarySat = tt , τₐ/ft →/fo τᵣ/fo , eₗ/fb }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        τₐ/ft →/fo τᵣ/fo ,′
        eₗ/fb
    }
ℐfstord-sound 𝒯 `R-merge-box
  step@(mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  termSat@record { boundarySat = (tt , τ/fo , e/fb@()) , _ }
  inv′,mono
ℐfstord-sound 𝒯 `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esatb)))
  termSat@record { boundarySat = (tt , τ/fo , e/fb@()) , _ }
  inv′,mono
ℐfstord-sound 𝒯 `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  termSat@record { boundarySat = tt , box/fo τ′/fo , eb/fb }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        τ′/fo ,′
        unbox/fb eb/fb
    }
ℐfstord-sound 𝒯 `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit@ivₐ trWit)
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat@record { boundarySat = tt , τₐ/ft →/fo τᵣ/fo , eₗ/fb }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        (tt ,
         τᵣ/fo ,′
         eₗ/fb ·/fb (B/fb τₐ/ft (ψ₂(here refl)))) ,′
        (tt ,
         flat/fo τₐ/ft ,′
         flatty∧isval⇒fbexpr τₐ/ft ivₐ)
    }
