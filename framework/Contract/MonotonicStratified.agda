{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Contract.MonotonicStratified (Label : Set) where

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
import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; _∘′_)

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Interpretation

𝒜ctc : AnnTerm

open import Contract.Common Label
open import Contract.Base Label 𝒜ctc as StdCtc
open import Contract.Satisfaction Label 𝒜ctc
open import Contract.Monotonic Label 𝒜ctc

AnnTerm.Ann   𝒜ctc τ = List (SCtc1N [] τ)
AnnTerm.State 𝒜ctc   = Status

𝒯 : ℕ → AnnTransit 𝒜ctc
𝒯 zero = ∅tr
𝒯 (suc i) = 𝒯sctc id𝒜view (𝒯 i)


ℐerrmono* : (i : ℕ) → AnnIntr (𝒯 i)
AnnIntr.Ix         (ℐerrmono* i) = ⊤
AnnIntr.IxRel      (ℐerrmono* i) sκs ix ix′ = ⊤
AnnIntr.Inv        (ℐerrmono* i) s = ⊤
AnnIntr.Ord        (ℐerrmono* i) = ErrMono id𝒜view
AnnIntr.isPreorder (ℐerrmono* i) = emIsPreorder id𝒜view
AnnIntr.𝔹          (ℐerrmono* zero) sκs ix◁ix′ e = ⊥
AnnIntr.𝔹          (ℐerrmono* (suc i)) sκs ix◁ix′ e =
  All (SCtcSat (ℐerrmono* i) tt) sκs
AnnIntr.𝔹Sound     (ℐerrmono* zero) step inv inv′ mono ()
AnnIntr.𝔹Sound     (ℐerrmono* (suc i)) {A = sκs} step inv inv′ mono bsat = bsat
AnnIntr.ℙ          (ℐerrmono* i) {τ = τ} sκs ix◁ix′ em =
  AnnIntr.𝔹 (ℐerrmono* i) {τ = τ} sκs ix◁ix′ ⌊ em ⌋m


ℐerrmono*-monotonic : ∀ i → AnnTransitInterpIs (ℐerrmono* i) Monotonic
ℐerrmono*-monotonic zero `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic zero `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat
ℐerrmono*-monotonic (suc i) `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(s-eq , s≡s′@refl))
  (B/i ix ix′ ix◁ix′ bsat ⋆)
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(s₂ , (s-eq , s≡s₂@refl) , checks-tr))
  (B/i ix ix′ ix◁ix′ bsat esat)
  termSat@record { boundarySat = _ , κsats } =
    _ ,
    checkNatSCtcsMono id𝒜view (𝒯 i) (ψ₁(here refl)) checks-tr
ℐerrmono*-monotonic (suc i) `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , (sκs₁-eq , sκs₂-eq)))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box esat)))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  termSat =
    _ , em-refl refl
ℐerrmono*-monotonic (suc i) `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , (sκsₐ-eq , sκsᵣ-eq)))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat =
    _ , em-refl refl


ℐerrmono*-sound : ∀ i → AnnTransitInterpIs (ℐerrmono* i) Sound
ℐerrmono*-sound zero `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound zero `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐerrmono*-sound (suc i) `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(s-eq , s≡s′@refl))
  (B/i ix ix′ ix◁ix′ bsat ⋆)
  termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐerrmono*-sound (suc i) `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(s₂ , (s-eq , s≡s₂) , checks-tr))
  (B/i ix ix′ ix◁ix′ bsat esat)
  termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐerrmono*-sound (suc i) `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , (sκs₁-eq , sκs₂-eq)))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        (tt , all-map-subst (SCtcSat (ℐerrmono* i) tt)
                            */c-sκ₁
                            (sym sκs₁-eq)
                            (ListAll.map sκsat-*₁ κsats)) ,′
        (tt , all-map-subst (SCtcSat (ℐerrmono* i) tt)
                            */c-sκ₂
                            (sym sκs₂-eq)
                            (ListAll.map sκsat-*₂ κsats))
    }
ℐerrmono*-sound (suc i) `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , all-map-subst  (SCtcSat (ℐerrmono* i) tt)
                                        +/c-sκ₁
                                        (sym sκs-eq)
                                        (ListAll.map sκsat-+₁ κsats)
    }
ℐerrmono*-sound (suc i) `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , all-map-subst  (SCtcSat (ℐerrmono* i) tt)
                                        +/c-sκ₂
                                        (sym sκs-eq)
                                        (ListAll.map sκsat-+₂ κsats)
    }
ℐerrmono*-sound (suc i) `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , all-map-subst  (SCtcSat (ℐerrmono* i) tt)
                                        μ/c-sκ
                                        (sym sκs-eq)
                                        (ListAll.map sκsat-μ κsats)
    }
ℐerrmono*-sound (suc i) `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (All (SCtcSat (ℐerrmono* i) tt)) (sym sκs-eq) κsats
    }
ℐerrmono*-sound (suc i) `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (All (SCtcSat (ℐerrmono* i) tt)) (sym sκs-eq) κsats
    }
ℐerrmono*-sound (suc i) `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box esat)))
  termSat@record { boundarySat = (_ , κsats) , (_ , κsats′) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst  (All (SCtcSat (ℐerrmono* i) tt))
                                (sym sκs-eq)
                                (ListAll.++⁺ κsats′ κsats)
    }
ℐerrmono*-sound (suc i) `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  termSat@record { boundarySat = (_ , κsats) , (_ , κsats′) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst  (All (SCtcSat (ℐerrmono* i) tt))
                                (sym sκs-eq)
                                (ListAll.++⁺ κsats′ κsats)
    }
ℐerrmono*-sound (suc i) `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , sκs-eq))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , all-map-subst  (SCtcSat (ℐerrmono* i) tt)
                                        box/c-sκ
                                        (sym sκs-eq)
                                        (ListAll.map sκsat-box κsats)
    }
ℐerrmono*-sound (suc i) `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((s-eq , s≡s′@refl) , (sκsₐ-eq , sκsᵣ-eq)))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat@record { boundarySat = _ , κsats }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        (tt , all-map-subst (SCtcSat (ℐerrmono* i) tt)
                            →/c-rng-sκ
                            (sym sκsᵣ-eq)
                            (ListAll.map sκsat-rng κsats)) ,′
        (tt , all-reverse-map-subst (SCtcSat (ℐerrmono* i) tt)
                                    →/c-dom-sκ
                                    (ψ₁(here refl))
                                    (sym sκsₐ-eq)
                                    (all-reverse (ListAll.map sκsat-dom κsats)))
    }
