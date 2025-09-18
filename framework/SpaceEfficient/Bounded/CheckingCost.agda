{-# OPTIONS --safe --without-K #-}

open import Annotation.Language
open import SpaceEfficient.Bounded.Base
  using ()
  renaming (𝒜ccctc to SE𝒜ccctc; 𝒜cctc-view to SE𝒜cctc-view)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Bounded.CheckingCost
  (Label : Set)
  (OP : SEOrderedPredicate  Label (SE𝒜ccctc Label)
                            (AnnTermView.getState (SE𝒜cctc-view Label))
                            (AnnTermView.putState (SE𝒜cctc-view Label)))
  where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; _∘′_)

open import Utils.Misc
open import Data.Tick using (Tick; evalTick; execTick; ✓_)
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Invariant
open import Annotation.Soundness

open SpaceEfficient.Bounded.Base Label
open import Contract.Common Label
open import Contract.Base Label 𝒜ccctc
open SpaceEfficient.OrderedPredicate Label 𝒜ccctc
open import SpaceEfficient.Base Label 𝒜ccctc
open import SpaceEfficient.LeafPredicate Label 𝒜ccctc
open import SpaceEfficient.Cost.Checking Label 𝒜ccctc
open import SpaceEfficient.Cost.Join Label 𝒜ccctc
open import SpaceEfficient.Bounded.OpSemantics Label (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Properties.UniqueSublist Label 𝒜cctc-view OP
open AnnTerm 𝒜ccctc hiding (State)

open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)
open SECtcTransitSteps 𝒜cctc-view stronger?

check-bound : (U : List Pred) → ℕ
check-bound U = length U

Inv : State → Set
Inv s =
  State.cost/chk s ≤ State.count s * check-bound ord-preds

ℐchkbnd : AnnInvr 𝒯cntctc
AnnInvr.Ix         ℐchkbnd = ⊤
AnnInvr.IxRel      ℐchkbnd cκ ix ix′ = ⊤
AnnInvr.Ord        ℐchkbnd = trivialOrd
AnnInvr.isPreorder ℐchkbnd = trivialOrdIsPreorder
AnnInvr.Inv        ℐchkbnd = Inv
AnnInvr.𝔹          ℐchkbnd cκ ix◁ix′ e =
  SECtcPreds (ord-preds ⊇#_) (runAnn cκ)
AnnInvr.𝔹Sound     ℐchkbnd (R-redex step)            inv inv′ mono c#⊆U = c#⊆U
AnnInvr.𝔹Sound     ℐchkbnd (R-bdr rule-no s s′ step) inv inv′ mono c#⊆U = c#⊆U
AnnInvr.ℙ          ℐchkbnd cκ ix◁ix′ em =
  AnnInvr.𝔹 ℐchkbnd cκ ix◁ix′ ⌊ em ⌋m


ℐchkbnd-monotonic : AnnInvrIs ℐchkbnd Monotonic
ℐchkbnd-monotonic `R-cross-unit {s₁ = s₁}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , (s₁-status-eq , refl) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-cross-nat {s₁ = s₁} {s₂}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (s₃ , (.s₁ , (s₁-status-eq , refl) , cκ-checks-tr) ,
                (s₄ , s₄-chkcost-eq@refl , (s₅ , s₅-secost-eq@refl , s₂-cnt-eq@refl))))
  esat
  (record { inv = I; boundarySat = _ , cκ-us }) =
    (begin
      State.cost/chk s₃ + length cκ-preds   ≡⟨ cong (_+ length cκ-preds)
                                                    (proj₁ s₃-chkcost,s₃-secost,cnt-eq) ⟨
      State.cost/chk s₁ + length cκ-preds   ≡⟨ Nat.+-comm (State.cost/chk s₁) (length cκ-preds) ⟩
      length cκ-preds + State.cost/chk s₁   ≤⟨ Nat.+-mono-≤ len-cκ-preds≤len-ord-preds I ⟩
      check-bound ord-preds + State.count s₁ * check-bound ord-preds
        ≡⟨ cong ((check-bound ord-preds +_) ∘′ (_* check-bound ord-preds))
                (proj₂ (proj₂ s₃-chkcost,s₃-secost,cnt-eq)) ⟩
      check-bound ord-preds + State.count s₃ * check-bound ord-preds  ≡⟨⟩
      suc (State.count s₃) * check-bound ord-preds                    ∎) ,
    tt
    where
      open ≤-Reasoning

      cκ-preds = flat/cc-preds (runAnn(ψ₁(here refl)))

      s₃-chkcost,s₃-secost,cnt-eq : State.cost/chk s₁ ≡ State.cost/chk s₃ ×
                                    State.cost/se s₁ ≡ State.cost/se s₃ ×
                                    State.count s₁ ≡ State.count s₃
      s₃-chkcost,s₃-secost,cnt-eq =
        check-nat-cctc-preserve-state cκ-preds
                                      (subst check-nat-ty (flat/cc-η (runAnn(ψ₁(here refl)))) cκ-checks-tr)
        where check-nat-ty = λ cκ → checkNatSECtc cκ (termEnv(here refl)) s₁ s₃

      len-cκ-preds≤len-ord-preds : length cκ-preds ≤ check-bound ord-preds
      len-cκ-preds≤len-ord-preds = begin
        length cκ-preds                 ≡⟨ List.length-map flat-pred cκ-preds ⟨
        length (map flat-pred cκ-preds) ≤⟨ USublist-length (cps-flat-preds cκ-us) ⟩
        length ord-preds ∎
ℐchkbnd-monotonic `R-cross-cons {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq₁ , cκ-eq₂) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-cross-inl {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-cross-inr {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-cross-roll {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-cross-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-cross-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-merge-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (s₂ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-merge-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (s₂ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-proxy-unbox {s₁ = s₁}
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt
ℐchkbnd-monotonic `R-proxy-β {s₁ = s₁}
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκₐ-eq , cκᵣ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  Esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * check-bound ord-preds) (check-bound ord-preds)) ,
    tt


ℐchkbnd-sound : AnnInvrIs ℐchkbnd Sound
ℐchkbnd-sound `R-cross-unit {s₁ = s₁}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , (s₁-status-eq , refl) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐchkbnd-sound `R-cross-nat {s₁ = s₁} {s₂}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (s₃ , (.s₁ , (s₁-status-eq , refl) , cκ-checks-tr) ,
                (s₄ , s₄-chkcost-eq@refl , (s₅ , s₅-secost-eq@refl , s₂-cnt-eq@refl))))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐchkbnd-sound `R-cross-cons {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq₁ , cκ-eq₂) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        (tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq₁) (cps-*₁ cκ-us)) ,′
        (tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq₂) (cps-*₂ cκ-us))
    }
ℐchkbnd-sound `R-cross-inl {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-+₁ cκ-us)
    }
ℐchkbnd-sound `R-cross-inr {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-+₂ cκ-us)
    }
ℐchkbnd-sound `R-cross-roll {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-μ cκ-us)
    }
ℐchkbnd-sound `R-cross-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) cκ-us
    }
ℐchkbnd-sound `R-cross-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) cκ-us
    }
ℐchkbnd-sound `R-merge-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) ,
                  (s₂ , chkcost-eq@refl , (s₄ , s₄-secost-eq@refl , s₃-cnt-eq@refl))))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  (record { inv = I ; boundarySat = (_ , cκ-us) , (_ , cκ-us′) })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq)
              (cps-join 𝒜cctc-view stronger? usublist-join-flats cκ-us′ cκ-us)
    }
ℐchkbnd-sound `R-merge-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) ,
                  (s₂ , cost-eq@refl , (s₄ , s₄-secost-eq@refl , s₃-cnt-eq@refl))))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  (record { inv = I ; boundarySat = (_ , cκ-us) , (_ , cκ-us′) })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq)
              (cps-join 𝒜cctc-view stronger? usublist-join-flats cκ-us′ cκ-us)
    }
ℐchkbnd-sound `R-proxy-unbox {s₁ = s₁}
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat = tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-box cκ-us)
    }
ℐchkbnd-sound `R-proxy-β {s₁ = s₁}
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκₐ-eq , cκᵣ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  (record { boundarySat = _ , cκ-us })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        (tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκᵣ-eq) (cps-rng cκ-us)) ,′
        (tt , subst (SECtcPreds (ord-preds ⊇#_)) (sym cκₐ-eq) (cps-dom cκ-us))
    }

check-cost-bounded : ∀ {τ s′} {e e′ : Ann ∣ [] ⊢ τ} →
  𝒯cntctc ⊢ init-state , e ⟶* s′ , e′ →
  ℐchkbnd ⊨[ tt ] e →
  State.cost/chk s′ ≤ State.count s′ * length ord-preds
check-cost-bounded steps ⊨e =
  proj₁ (monotonicity* ℐchkbnd ℐchkbnd-monotonic ℐchkbnd-sound steps z≤n ⊨e)
