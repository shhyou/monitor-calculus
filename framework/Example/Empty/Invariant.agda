{-# OPTIONS --without-K --safe #-}

module Example.Empty.Invariant where

open import Utils.Misc -- for trivialOrd and trivialOrdIsPreorder
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Language
open import Annotation.Invariant.Base
open import Annotation.Invariant.Property

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

ℐ⊥ : ∀ {𝒜 𝒯} → AnnInvr {𝒜} 𝒯
AnnInvr.Ix         ℐ⊥ = ⊤
AnnInvr.IxRel      ℐ⊥ A ix ix′ = ⊤
AnnInvr.Inv        ℐ⊥ s = ⊤
AnnInvr.Ord        ℐ⊥ = trivialOrd
AnnInvr.isPreorder ℐ⊥ = trivialOrdIsPreorder
AnnInvr.𝔹          ℐ⊥ A ix◁ix′ e = ⊥
AnnInvr.𝔹Sound     ℐ⊥ step inv inv′ mono ()
AnnInvr.ℙ          ℐ⊥ A ix◁ix′ em = ⊥


ℐ⊥-monotonic : ∀ {𝒜} (𝒯 : AnnTransit 𝒜) → AnnInvrIs {𝒯 = 𝒯} ℐ⊥ Monotonic
ℐ⊥-monotonic 𝒯 tag step esat₁ termSat = tt , tt


ℐ⊥-sound : ∀ {𝒜} (𝒯 : AnnTransit 𝒜) → AnnInvrIs {𝒯 = 𝒯} ℐ⊥ Sound
ℐ⊥-sound {𝒜} 𝒯 `R-cross-unit
      (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () ⋆)
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-nat
      (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () esat)
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-cons
      (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (esat₁ `, esat₂))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-inl
      (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (inl esat))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-inr
      (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (inr esat))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-roll
      (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (roll τ esat))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-box
      (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (box esat))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-cross-lam
      (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (ƛ esat))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-merge-box
      (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ () (box esatm)))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-merge-lam
      (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (B/i ix ix′ ix◁ix′ () (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ () (ƛ esatb)))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-proxy-unbox
      (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        (unbox (proxy/i em ix ix′ ix◁ix′ () (box esat)))
        termSat
        inv′,mono
ℐ⊥-sound {𝒜} 𝒯 `R-proxy-β
      (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
        ((proxy/i em ix ix′ ix◁ix′ () (ƛ esat)) · esatₐ)
        termSat
        inv′,mono
