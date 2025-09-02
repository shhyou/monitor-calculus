{-# OPTIONS --safe --without-K #-}

open import Annotation.Language
open import SpaceEfficient.Equivalence.Base
  using ()
  renaming (𝒜csctc to SE𝒜csctc; 𝒜sctc-view to SE𝒜sctc-view)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Equivalence.Soundness
  (Label : Set)
  (OP : SEOrderedPredicate  Label (SE𝒜csctc Label)
                            (AnnTermView.getState (SE𝒜sctc-view Label))
                            (AnnTermView.putState (SE𝒜sctc-view Label)))
  where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; _≗_; subst; subst₂; sym; trans; cong)
open import Relation.Binary
  using (IsPreorder; IsEquivalence; IsPartialOrder)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; uncurry)

open import Data.List.Base as List using (List; []; _∷_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec.Base as Vec
  using (Vec; []; _∷_; head; tail; _∷ʳ_; init; last; map; reverse; _++_; zipWith; cast)
import Data.Vec.Properties as Vec
open import Data.Vec.Relation.Binary.Equality.Cast
  using (_≈[_]_; ≈-reflexive; ≈-sym; ≈-trans; module CastReasoning)

import Data.Nat.Literals
open import Agda.Builtin.FromNat

open import Function.Base using (id)

open import Utils.Misc
open import Data.Tick using (Tick; evalTick; ✓_)
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import OpSemantics.Properties
open import Annotation.Invariant

open SpaceEfficient.Equivalence.Base Label

open import Contract.Common Label
open import Contract.Base Label 𝒜csctc
open import Contract.Satisfaction Label 𝒜csctc
open import Contract.Vectorized Label 𝒜csctc
open SpaceEfficient.OrderedPredicate Label 𝒜csctc
open import SpaceEfficient.Base Label 𝒜csctc
open import SpaceEfficient.Sign Label 𝒜csctc
open import SpaceEfficient.Equivalence.OpSemantics Label (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Equivalence.Invariant Label OP
open import SpaceEfficient.Equivalence.Simulation Label OP

open AnnTerm 𝒜csctc using (Ann; State)
open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)
open SECtcTransitSteps 𝒜cctc-view stronger?


ℐsim-monotonic : AnnInvrIs ℐsim Monotonic
ℐsim-monotonic `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , (refl , refl) , (refl , refl)))
  (B/i ix ix′ ix◁ix′ bsat ⋆)
  termSat@record { inv = I } =
    I , so-reflexive refl
ℐsim-monotonic `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , (s₁ , (refl , refl) , cκ-checks-tr) , (s₂ , (refl , refl) , sκs-checks-tr)))
  (B/i ix ix′ ix◁ix′ bsat esat)
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    check-nat-ctc-sim (proj₂(ψ₁(here refl)))
                      premWit
                      []
                      (clc-flat-preds c⊆s)
                      I
                      (subst  (λ cκ → checkNatSECtc cκ (termEnv(here refl)) s₁ _)
                              (flat/cc-η (proj₁(ψ₁(here refl))))
                              cκ-checks-tr)
                      sκs-checks-tr
ℐsim-monotonic `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq₁ , cκ-eq₂) , ((ss-eq , refl) , sκs-eq₁ , sκs-eq₂)))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esat)))
  termSat@record { inv = I; boundarySat = (_ , (pmκ , c⊆s)) , (_ , (pmκ′ , c⊆s′)) } =
    I , so-reflexive refl
ℐsim-monotonic `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  termSat@record { inv = I
                 ; boundarySat = (_ , (pmκ , c⊆s)) , (_ , (pmκ′ , c⊆s′)) } =
    I , so-reflexive refl
ℐsim-monotonic `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl
ℐsim-monotonic `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκsₐ-eq , sκsᵣ-eq)))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat@record { inv = I; boundarySat = _ , (pmκ , c⊆s) } =
    I , so-reflexive refl


subst-CollapsedCtcs-κs : ∀ {τ cκ cκ′} {sκs sκs′ : List (SCtc1N [] τ)} →
  cκ ≡ cκ′ →
  sκs ≡ sκs′ →
  CollapsedCtcs (length sκs) cκ (Vec.fromList sκs) →
  CollapsedCtcs (length sκs′) cκ′ (Vec.fromList sκs′)
subst-CollapsedCtcs-κs cκ-eq sκs-eq clc =
  subst₂ (λ cκ sκs → CollapsedCtcs (length sκs) cκ (Vec.fromList sκs))
         cκ-eq
         sκs-eq
         clc

subst-CollapsedCtcs-len : ∀ {τ m cκ sκs′} →
  {sκs : Vec (SCtc1N [] τ) m} →
  (eq : length sκs′ ≡ m) →
  cast eq (Vec.fromList sκs′) ≡ sκs →
  CollapsedCtcs m cκ sκs →
  CollapsedCtcs (length sκs′) cκ (Vec.fromList sκs′)
subst-CollapsedCtcs-len {cκ = cκ} {sκs′} refl sκs-eq clc
  rewrite Vec.cast-is-id refl (Vec.fromList sκs′) =
  subst (CollapsedCtcs (length sκs′) cκ) (sym sκs-eq) clc

ℐsim-sound : AnnInvrIs ℐsim Sound
ℐsim-sound `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐsim-sound `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐsim-sound `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(s* , ((cs-eq , refl) , cκ₁-eq , cκ₂-eq) , ((ss-eq , refl) , sκs₁-eq , sκs₂-eq)))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
       (tt ,
        subst (SECtcSigned pos []) (sym cκ₁-eq) (pmκ-*₁ pmκ) ,′
        subst-CollapsedCtcs-κs  (sym cκ₁-eq)
                                (sym sκs₁-eq)
                                (subst-CollapsedCtcs-len  (List.length-map */c-sκ₁ sκs)
                                                          (Vec.fromList-map */c-sκ₁ sκs)
                                                          (clc-*₁ c⊆s))) ,′
       (tt ,
        subst (SECtcSigned pos []) (sym cκ₂-eq) (pmκ-*₂ pmκ) ,′
        subst-CollapsedCtcs-κs  (sym cκ₂-eq)
                                (sym sκs₂-eq)
                                (subst-CollapsedCtcs-len  (List.length-map */c-sκ₂ sκs)
                                                          (Vec.fromList-map */c-sκ₂ sκs)
                                                          (clc-*₂ c⊆s)))
    }
    where sκs = proj₂(ψ₁(here refl))
ℐsim-sound `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq) (pmκ-+₁ pmκ) ,′
       subst-CollapsedCtcs-κs (sym cκ-eq)
                              (sym sκs-eq)
                              (subst-CollapsedCtcs-len  (List.length-map +/c-sκ₁ sκs)
                                                        (Vec.fromList-map +/c-sκ₁ sκs)
                                                        (clc-+₁ c⊆s))
    }
    where sκs = proj₂(ψ₁(here refl))
ℐsim-sound `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq) (pmκ-+₂ pmκ) ,′
       subst-CollapsedCtcs-κs (sym cκ-eq)
                              (sym sκs-eq)
                              (subst-CollapsedCtcs-len  (List.length-map +/c-sκ₂ sκs)
                                                        (Vec.fromList-map +/c-sκ₂ sκs)
                                                        (clc-+₂ c⊆s))
    }
    where sκs = proj₂(ψ₁(here refl))
ℐsim-sound `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq) (pmκ-μ pmκ) ,′
       subst-CollapsedCtcs-κs (sym cκ-eq)
                              (sym sκs-eq)
                              (subst-CollapsedCtcs-len  (List.length-map μ/c-sκ sκs)
                                                        (Vec.fromList-map μ/c-sκ sκs)
                                                        (clc-μ-pos pmκ c⊆s))
    }
    where sκs = proj₂(ψ₁(here refl))
ℐsim-sound `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq) pmκ ,′
       subst-CollapsedCtcs-κs (sym cκ-eq) (sym sκs-eq) c⊆s
    }
ℐsim-sound `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq) pmκ ,′
       subst-CollapsedCtcs-κs (sym cκ-eq) (sym sκs-eq) c⊆s
    }
ℐsim-sound `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box esat)))
  termSat@record { boundarySat = (_ , (pmκ , c⊆s)) , (_ , (pmκ′ , c⊆s′)) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq)
             (pmκ-join 𝒜cctc-view stronger? pmκ′ pmκ) ,′
       subst-CollapsedCtcs-κs (sym cκ-eq)
                              (sym sκs-eq)
                              (subst-CollapsedCtcs-len  (List.length-++ sκs′)
                                                        (Vec.fromList-++ sκs′)
                                                        (clc-join c⊆s′ c⊆s))
    }
    where sκs = proj₂(ψ₁(here refl))
          sκs′ = proj₂(ψ₁(there (here refl)))
ℐsim-sound `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  termSat@record { boundarySat = (_ , (pmκ , c⊆s)) , (_ , (pmκ′ , c⊆s′)) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq)
             (pmκ-join 𝒜cctc-view stronger? pmκ′ pmκ) ,′
       subst-CollapsedCtcs-κs  (sym cκ-eq)
                              (sym sκs-eq)
                              (subst-CollapsedCtcs-len  (List.length-++ sκs′)
                                                        (Vec.fromList-++ sκs′)
                                                        (clc-join c⊆s′ c⊆s))
    }
    where sκs = proj₂(ψ₁(here refl))
          sκs′ = proj₂(ψ₁(there (here refl)))
ℐsim-sound `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , cκ-eq) , ((ss-eq , refl) , sκs-eq)))
  (unbox (proxy/i em ix ix′ ix◁ix′ bsat (box esat)))
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
       tt ,
       subst (SECtcSigned pos []) (sym cκ-eq) (pmκ-box pmκ) ,′
       subst-CollapsedCtcs-κs (sym cκ-eq)
                              (sym sκs-eq)
                              (subst-CollapsedCtcs-len  (List.length-map box/c-sκ sκs)
                                                        (Vec.fromList-map box/c-sκ sκs)
                                                        (clc-box c⊆s))
    }
    where sκs = proj₂(ψ₁(here refl))
ℐsim-sound `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
        trWit@(s* , ((cs-eq , refl) , (cκₐ-eq , cκᵣ-eq)) , ((ss-eq , refl) , (sκsₐ-eq , sκsᵣ-eq))))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat@record { boundarySat = _ , (pmκ , c⊆s) }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
       (tt ,
        subst (SECtcSigned pos []) (sym cκᵣ-eq) (pmκ-rng pmκ) ,′
        subst-CollapsedCtcs-κs  (sym cκᵣ-eq)
                                (sym sκsᵣ-eq)
                                (subst-CollapsedCtcs-len  (List.length-map →/c-rng-sκ sκs)
                                                          (Vec.fromList-map →/c-rng-sκ sκs)
                                                          (clc-rng c⊆s))) ,′
       (tt ,
        subst (SECtcSigned pos []) (sym cκₐ-eq) (pmκnegate (pmκ-dom pmκ)) ,′
        subst-CollapsedCtcs-κs (sym cκₐ-eq)
                               (sym sκsₐ-eq)
                               (subst-CollapsedCtcs-len
                                 (begin-≡
                                   length (List.reverse (List.map →/c-dom-sκ sκs))
                                 ≡⟨ len-rev-eq ⟩
                                   length (List.map →/c-dom-sκ sκs)
                                 ≡⟨ len-map-eq ⟩
                                   length sκs
                                 ≡-∎)
                                 (begin
                                   Vec.fromList (List.reverse (List.map →/c-dom-sκ sκs))
                                 ≈⟨ Vec.fromList-reverse (List.map →/c-dom-sκ sκs) ⟩
                                   reverse (Vec.fromList (List.map →/c-dom-sκ sκs))
                                 ≈⟨ ≈-cong  reverse (Vec.cast-reverse
                                                      len-map-eq
                                                      (Vec.fromList (List.map →/c-dom-sκ sκs)))
                                            (Vec.fromList-map →/c-dom-sκ sκs) ⟩
                                   reverse (map →/c-dom-sκ (Vec.fromList sκs))
                                 ∎)
                                 (clc-dom c⊆s)))
    }
    where sκs = proj₂(ψ₁(here refl))
          len-rev-eq = List.length-reverse (List.map →/c-dom-sκ sκs)
          len-map-eq = List.length-map →/c-dom-sκ sκs
          open CastReasoning
