{-# OPTIONS --safe --without-K #-}

module SpaceEfficient.Bounded.Base (Label : Set) where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; trans; cong; subst)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)

open import Data.List.Base as List using (List; []; _∷_; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; const; _∘′_)

open import Data.Tick using (Tick; evalTick; ✓_)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language

𝒜ccctc : AnnTerm
open import Example.Count.Annotation
open import Contract.Common Label
open import Contract.Base Label 𝒜ccctc
  using ( SCtc1N; SCtc1; flat; flat-pred
        ; sκflat-change-variable; flat-pred-change-variable; checkNatSCtcs)
open import SpaceEfficient.Base Label 𝒜ccctc
open import SpaceEfficient.Cost.Checking Label 𝒜ccctc
open import SpaceEfficient.Cost.Join Label 𝒜ccctc
open import SpaceEfficient.OrderedPredicate Label 𝒜ccctc
open AnnTerm 𝒜ccctc hiding (State)

private variable
  Δ Δ′ : TCtxt
  τ τ′ τ₁ τ₂ τₐ τᵣ : TyN Δ
  P Q : List Pred → Set

record SECtcAnn τ : Set where
  constructor mkAnn; inductive
  field       runAnn : SECtcN [] τ
open SECtcAnn public

mapAnn : (SECtcN [] τ → SECtcN [] τ′) → SECtcAnn τ → SECtcAnn τ′
mapAnn f = mkAnn ∘′ f ∘′ runAnn

record State : Set where
  inductive
  field
    status    : Status
    cost/chk  : ℕ
    cost/se : ℕ
    count     : ℕ

AnnTerm.Ann   𝒜ccctc τ = SECtcAnn τ
AnnTerm.State 𝒜ccctc = State

init-state : State
init-state = record
  { status = Ok
  ; cost/chk = 0
  ; cost/se = 0
  ; count = 0
  }

𝒜cctc-view : AnnTermView 𝒜ccctc 𝒜cctc
𝒜cctc-view = mkView runAnn
                    State.status
                    (λ st′ s → record s { status = st′ })
                    (λ s → refl)
                    (λ s₁ s₂ → refl)
                    (λ s₁ s₂ s₂′ → refl)

𝒜chkcost-view : AnnTermView 𝒜ccctc 𝒜chkcost
𝒜chkcost-view = mkView runAnn
                        State.cost/chk
                        (λ c′ s → record s { cost/chk = c′ })
                        (λ s → refl)
                        (λ s₁ s₂ → refl)
                        (λ s₁ s₂ s₂′ → refl)

𝒜secost-view : AnnTermView 𝒜ccctc 𝒜secost
𝒜secost-view = mkView runAnn
                      State.cost/se
                      (λ c′ s → record s { cost/se = c′ })
                      (λ s → refl)
                      (λ s₁ s₂ → refl)
                      (λ s₁ s₂ s₂′ → refl)

𝒜cnt-view : AnnTermView 𝒜ccctc 𝒜cnt
𝒜cnt-view = mkView (const tt)
                    State.count
                    (λ c′ s → record s { count = c′ })
                    (λ s → refl)
                    (λ s₁ s₂ → refl)
                    (λ s₁ s₂ s₂′ → refl)
