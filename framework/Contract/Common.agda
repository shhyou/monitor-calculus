{-# OPTIONS --without-K --safe #-}

module Contract.Common (Label : Set) where

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language
open import OpSemantics.Base
open import OpSemantics.Properties

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong; trans; sym; module ≡-Reasoning)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base as List
  using (List; []; _∷_)

data Sgn : Set where
  pos : Sgn
  neg : Sgn

negate : Sgn → Sgn
negate pos = neg
negate neg = pos

pos≢neg : pos ≢ neg
pos≢neg ()

data Status : Set where
  Ok : Status
  Err : (l : Label) → Status

status-distinct : ∀ {l} → ¬ (Ok ≡ Err l)
status-distinct ()

data CheckNatPred {𝒜 : AnnTerm}
  (getState : ATState 𝒜 → Status)
  (putState : Status → ATState 𝒜 → ATState 𝒜)
  (reduce* : ReductionRel 𝒜)
  (l : Label)
  (e : ATAnn 𝒜 ∣ `ℕ ∷ [] ⊢ `ℕ)
  (v : ATAnn 𝒜 ∣ [] ⊢ `ℕ) :
  ATState 𝒜 → ATState 𝒜 → Set where
    NP-acc : ∀ {s s′ n} →
      (iv : ATAnn 𝒜 ∣ n isvalof `ℕ) →
      (steps : reduce* s (esubst e [x0↦ v ]) s′ (`s n)) →
      getState s′ ≡ Ok →
      CheckNatPred getState putState reduce* l e v s s′

    NP-rej : ∀ {s s₁ s′} →
      (steps : reduce* s (esubst e [x0↦ v ]) s₁ `z) →
      getState s₁ ≡ Ok →
      s′ ≡ putState (Err l) s₁ →
      CheckNatPred getState putState reduce* l e v s s′

    NP-err : ∀ {s s′ e′} →
      (steps : reduce* s (esubst e [x0↦ v ]) s′ e′) →
      ∀ l′ →
      getState s′ ≡ Err l′ →
      CheckNatPred getState putState reduce* l e v s s′


module _ {𝒜 : AnnTerm} {getState : ATState 𝒜 → Status} {putState : Status → ATState 𝒜 → ATState 𝒜} where
  check-nat-pred-deterministic-any : ∀ {s s₁ s₂ l e n} →
    getState s ≡ Ok →
    CheckNatPred {𝒜} getState putState (∅tr ⊢_,_⟶*_,_) l e n s s₁ →
    CheckNatPred {𝒜} getState putState (∅tr ⊢_,_⟶*_,_) l e n s s₂ →
    s₁ ≡ s₂
  check-nat-pred-deterministic-any s≡Ok (NP-acc iv₁ steps₁ s₁≡Ok) (NP-acc iv₂ steps₂ s₂≡Ok)
    = trans (sym (∅tr-⟶*-preserve-state steps₁)) (∅tr-⟶*-preserve-state steps₂)
  check-nat-pred-deterministic-any s≡Ok (NP-acc iv₁ steps₁ s₁≡Ok) (NP-rej steps₂ s₂′≡Ok s₂≡Err)
    with value-∅tr-⟶*-deterministic (s/v iv₁) z/v steps₁ steps₂ -- `s m ≡ ` z
  ... | ()
  check-nat-pred-deterministic-any {s} {s₁} {s₂} s≡Ok (NP-acc iv₁ steps₁ s₁≡Ok) (NP-err steps₂ l₂′ s₂≡Err)
    = ⊥-elim (status-distinct
                (begin  Ok            ≡⟨ s≡Ok ⟨
                        getState s    ≡⟨ cong getState (∅tr-⟶*-preserve-state steps₂) ⟩
                        getState s₂   ≡⟨ s₂≡Err ⟩
                        Err l₂′       ∎))
    where open ≡-Reasoning
  check-nat-pred-deterministic-any s≡Ok (NP-rej steps₁ s₁′≡Ok s₁≡Err) (NP-acc iv₂ steps₂ s₂≡Ok)
    with value-∅tr-⟶*-deterministic z/v (s/v iv₂) steps₁ steps₂ -- `z ≡ `s m
  ... | ()
  check-nat-pred-deterministic-any {l = l}
    s≡Ok (NP-rej steps₁ s₁′≡Ok s₁≡Err@refl) (NP-rej steps₂ s₂′≡Ok s₂≡Err@refl)
    = cong (putState (Err l)) (trans (sym (∅tr-⟶*-preserve-state steps₁)) (∅tr-⟶*-preserve-state steps₂))
  check-nat-pred-deterministic-any {s} {s₁} {s₂}
    s≡Ok (NP-rej steps₁ s₁′≡Ok s₁≡Err) (NP-err steps₂ l₂′ s₂≡Err)
    = ⊥-elim (status-distinct
                (begin  Ok            ≡⟨ s≡Ok ⟨
                        getState s    ≡⟨ cong getState (∅tr-⟶*-preserve-state steps₂) ⟩
                        getState s₂   ≡⟨ s₂≡Err ⟩
                        Err l₂′       ∎))
    where open ≡-Reasoning
  check-nat-pred-deterministic-any {s} {s₁} {s₂}
    s≡Ok (NP-err steps₁ l₁′ s₁≡Err) check-nat₂
    = ⊥-elim (status-distinct
                (begin  Ok            ≡⟨ s≡Ok ⟨
                        getState s    ≡⟨ cong getState (∅tr-⟶*-preserve-state steps₁) ⟩
                        getState s₁   ≡⟨ s₁≡Err ⟩
                        Err l₁′       ∎))
    where open ≡-Reasoning


  check-nat-pred-deterministic-ok : ∀ {s s₁ s₂ l₁ l₂ e n} →
    (∀ s′ status → getState (putState status s′) ≡ status) →
    getState s ≡ Ok →
    getState s₁ ≡ Ok →
    CheckNatPred {𝒜} getState putState (∅tr ⊢_,_⟶*_,_) l₁ e n s s₁ →
    CheckNatPred {𝒜} getState putState (∅tr ⊢_,_⟶*_,_) l₂ e n s s₂ →
    s₁ ≡ s₂
  check-nat-pred-deterministic-ok put-get
    s≡Ok s₁≡Ok (NP-acc iv₁ steps₁ s₁≡Ok′) (NP-acc iv₂ steps₂ s₂≡Ok)
    = trans (sym (∅tr-⟶*-preserve-state steps₁)) (∅tr-⟶*-preserve-state steps₂)
  check-nat-pred-deterministic-ok put-get
    s≡Ok s₁≡Ok (NP-acc iv₁ steps₁ s₁≡Ok′) (NP-rej steps₂ s₂′≡Ok s₂≡Err)
    with value-∅tr-⟶*-deterministic (s/v iv₁) z/v steps₁ steps₂ -- `s m ≡ ` z
  ... | ()
  check-nat-pred-deterministic-ok {s} {s₁} {s₂} put-get
    s≡Ok s₁≡Ok (NP-acc iv₁ steps₁ s₁≡Ok′) (NP-err steps₂ l₂′ s₂≡Err)
    = ⊥-elim (status-distinct
                (begin  Ok            ≡⟨ s≡Ok ⟨
                        getState s    ≡⟨ cong getState (∅tr-⟶*-preserve-state steps₂) ⟩
                        getState s₂   ≡⟨ s₂≡Err ⟩
                        Err l₂′       ∎))
    where open ≡-Reasoning
  check-nat-pred-deterministic-ok {s} {s₁} {s₂} {l₁} put-get
    s≡Ok s₁≡Ok (NP-rej {s₁ = s₁′} steps₁ s₁′≡Ok s₁≡Err) check-nat₂
    = ⊥-elim (status-distinct
                (begin  Ok                                ≡⟨ s₁≡Ok ⟨
                        getState s₁                       ≡⟨ cong getState s₁≡Err ⟩
                        getState (putState (Err l₁) s₁′)  ≡⟨ put-get s₁′ (Err l₁) ⟩
                        Err l₁                            ∎))
    where open ≡-Reasoning
  check-nat-pred-deterministic-ok {s} {s₁} {s₂} put-get
    s≡Ok s₁≡Ok (NP-err steps₁ l₁′ s₁≡Err) check-nat₂
    = ⊥-elim (status-distinct
                (begin  Ok            ≡⟨ s≡Ok ⟨
                        getState s    ≡⟨ cong getState (∅tr-⟶*-preserve-state steps₁) ⟩
                        getState s₁   ≡⟨ s₁≡Err ⟩
                        Err l₁′       ∎))
    where open ≡-Reasoning
