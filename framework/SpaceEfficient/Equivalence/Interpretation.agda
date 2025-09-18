{-# OPTIONS --safe --without-K #-}

open import Annotation.Language
open import SpaceEfficient.Equivalence.Base
  using ()
  renaming (𝒜csctc to SE𝒜csctc; 𝒜sctc-view to SE𝒜sctc-view)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Equivalence.Interpretation
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
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec.Base as Vec
  using (Vec; []; _∷_; head; tail; _∷ʳ_; init; last; map; reverse; _++_; zipWith)

import Data.Nat.Literals
open import Agda.Builtin.FromNat

open import Syntax.Type
open import Syntax.Term
open import OpSemantics.Base
open import OpSemantics.Properties
open import Annotation.Interpretation.Base

open SpaceEfficient.Equivalence.Base Label

open import Contract.Common Label
open import Contract.Base Label 𝒜csctc
open import Contract.Satisfaction Label 𝒜csctc
open SpaceEfficient.OrderedPredicate Label 𝒜csctc
open import SpaceEfficient.Base Label 𝒜csctc
open import SpaceEfficient.Sign Label 𝒜csctc
open import SpaceEfficient.Equivalence.OpSemantics Label (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Equivalence.Simulation Label OP

open AnnTerm 𝒜csctc using (Ann; State)
open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)
open SECtcTransitSteps 𝒜cctc-view stronger?


is-diagonal : State → Set
is-diagonal s = proj₁ s ≡ proj₂ s


data SimOrd : Σ State is-diagonal → Σ State is-diagonal → Set where
  so-refl : ∀ {s} → (d : is-diagonal s) → SimOrd (s , d) (s , d)
  so-err : ∀ l → SimOrd ((Ok ,′ Ok) , refl) ((Err l ,′ Err l) , refl)


so-reflexive : ∀ {s,d s′,d} → s,d ≡ s′,d → SimOrd s,d s′,d
so-reflexive {s,d = s , d} refl = so-refl d

so-trans : ∀ {s₁,d s₂,d s₃,d} → SimOrd s₁,d s₂,d → SimOrd s₂,d s₃,d → SimOrd s₁,d s₃,d
so-trans (so-refl d) (so-refl .d)    = so-refl d
so-trans (so-refl d) (so-err l)      = so-err l
so-trans (so-err l)  (so-refl .refl) = so-err l

soIsPreorder : IsPreorder _≡_ SimOrd
soIsPreorder = record { isEquivalence = PropEq.isEquivalence
                      ; reflexive = so-reflexive
                      ; trans = so-trans
                      }


CheckSCtcNatPred : Label → Pred → Ann ∣ [] ⊢ `ℕ → State → State → Set
CheckSCtcNatPred = CheckNatPred (AnnTermView.getState 𝒜sctc-view)
                                (AnnTermView.putState 𝒜sctc-view)
                                (∅tr ⊢_,_⟶*_,_)

check-nat-ctc-sim : ∀ {preds-ctxt cκ-preds n s st st′} →
  ∀ sκ-preds →
  Ann ∣ n isvalof `ℕ →
  All (λ oe → ∃[ l ] CheckSCtcNatPred l (proj₁ oe) n (st′ , Ok) (st′ , Ok)) preds-ctxt →
  CollapsedPreds preds-ctxt cκ-preds (Vec.fromList sκ-preds) →
  (d : Ok ≡ st) →
  checkNatSECtc (flat/cc cκ-preds) n (Ok , st) (st′ , Ok) →
  checkNatSCtcs 𝒜sctc-view ∅tr sκ-preds n (st′ , Ok) s →
  Σ[ d′ ∈ is-diagonal s ]
    SimOrd ((Ok , st) , d) (s , d′)
check-nat-ctc-sim [] nv ok-preds [] d@refl cκ-checks-tr@refl sκs-checks-tr@refl =
  refl , so-reflexive refl
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈ord-preds) ∷ clp-preds) d
  (_ , inj₁ (_ , (refl , refl) , check-nat₁@(NP-acc {n = m} mv oe-steps s₁≡Ok)) , cκ-checks-tr)
  (_ , inj₁ (_ , (refl , refl) , check-nat₂@(NP-acc {n = m′} m′v oe-steps′ s₁′≡Ok)) , sκs-checks-tr)
  with ∅tr-⟶*-preserve-state oe-steps | ∅tr-⟶*-preserve-state oe-steps′ | s₁≡Ok | s₁′≡Ok
... | refl | refl | refl | refl
  = check-nat-ctc-sim sκ-preds
                      nv
                      ((_ , check-nat₂) ∷ ok-preds)
                      clp-preds
                      d
                      cκ-checks-tr
                      sκs-checks-tr
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈ord-preds) ∷ clp-preds) d
  (_ , inj₁ (S1 , (refl , refl) , NP-acc {n = m} mv oe-steps s₁≡Ok) , cκ-checks-tr)
  (_ , inj₁ (S2 , (refl , refl) , NP-rej oe-steps′ s≡Ok s₁≡Err) , sκs-checks-tr)
  with value-∅tr-⟶*-deterministic (s/v mv) z/v oe-steps oe-steps′
... | ()
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈ord-preds) ∷ clp-preds) d
  (_ , inj₁ (_ , (refl , refl) , NP-acc {n = m} mv oe-steps s₁≡Ok) , cκ-checks-tr)
  (_ , inj₁ (_ , (refl , refl) , NP-err oe-steps′ l′ s₁≡Err) , sκs-checks-tr)
  with ∅tr-⟶*-preserve-state oe-steps′ | s₁≡Err
... | refl | ()
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈ord-preds) ∷ clp-preds) d
  (_ , inj₁ (_ , (refl , refl) , NP-rej oe-steps s₁≡Ok s′≡Err) , cκ-checks-tr)
  (_ , inj₁ (_ , (refl , refl) , NP-acc {n = m′} m′v oe-steps′ s′≡Ok₂) , sκs-checks-tr)
  with value-∅tr-⟶*-deterministic z/v (s/v m′v) oe-steps oe-steps′
... | ()
check-nat-ctc-sim {cκ-preds = _ ∷ cκ-preds} (flat l .e ∷ sκ-preds) nv ok-preds
  (oe@(e , e∈ord-preds) ∷ clp-preds)
  d@refl
  (_ , inj₁ (_ , (refl , refl) , NP-rej oe-steps s₁≡Ok s′≡Err) , cκ-checks-tr)
  (_ , inj₁ (_ , (refl , refl) , NP-rej oe-steps′ s₁′≡Ok s′≡Err₂) , sκs-checks-tr)
  with ∅tr-⟶*-preserve-state oe-steps | ∅tr-⟶*-preserve-state oe-steps′ | s′≡Err | s′≡Err₂
... | refl | refl | refl | refl
  with check-nat-cctc-preserve-state cκ-preds cκ-checks-tr
     | check-nat-cctc-preserve-error cκ-preds cκ-checks-tr
     | check-nat-sctc-preserve-state sκ-preds sκs-checks-tr
     | check-nat-sctc-preserve-error sκ-preds sκs-checks-tr
... | refl | refl | refl | refl
  = refl , so-err l
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈ord-preds) ∷ clp-preds) d
  (_ , inj₁ (_ , (refl , refl) , NP-rej oe-steps s₁≡Ok s′≡Err) , cκ-checks-tr)
  (_ , inj₁ (_ , (refl , refl) , NP-err oe-steps′ l′ s′≡Err₂) , sκs-checks-tr)
  with ∅tr-⟶*-preserve-state oe-steps′ | s′≡Err₂
... | refl | ()
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈ord-preds) ∷ clp-preds) d
  (_ , inj₁ (_ , (refl , refl) , NP-err oe-steps l′ s′≡Err) , cκ-checks-tr)
  (_ , inj₁ (_ , (refl , refl) , check-nat₂) , sκs-checks-tr)
  with ∅tr-⟶*-preserve-state oe-steps | s′≡Err
... | refl | ()
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈opreds) ∷ clp-preds) d
  (_ , inj₁ check-nat₁ , cκ-checks-tr)
  (_ , inj₂ (l′ , ok≡Err@() , s-eq₂) , sκs-checks-tr)
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (oe@(e , e∈opreds) ∷ clp-preds) d
  (_ , inj₂ (l′ , ok≡Err@() , s-eq₁) , cκ-checks-tr)
  (_ , check-nat₂ , sκs-checks-tr)
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (⟨ oe@(e , e∈opreds) , oe′ , oe′∈ctxt , oe′≼oe ⟩∷ʳ clp-preds)
  d
  cκ-checks-tr
  (s′ , inj₁ (_ , (refl , refl) , check-nat₂) , sκs-checks-tr)
  with ≼-steps oe′≼oe nv refl (proj₂ (ListAll.lookup ok-preds oe′∈ctxt))
... | l , check-nat₂′
  rewrite sym (check-nat-pred-deterministic-ok  (AnnTermView.put-get 𝒜sctc-view) refl refl
                                                check-nat₂′
                                                check-nat₂)
    = check-nat-ctc-sim sκ-preds nv ok-preds clp-preds d cκ-checks-tr sκs-checks-tr
check-nat-ctc-sim (_ ∷ sκ-preds) nv ok-preds (⟨ oe@(e , e∈opreds) , oe′ , oe′∈ctxt , oe′≼oe ⟩∷ʳ clp-preds)
  d
  cκ-checks-tr
  (_ , inj₂ (l′ , ok≡Err@() , s-eq₂) , sκs-checks-tr)




ℐsim : AnnIntr 𝒯csctc
AnnIntr.Ix         ℐsim = ⊤
AnnIntr.IxRel      ℐsim csκs ix ix′ = ⊤
AnnIntr.Inv        ℐsim = is-diagonal
AnnIntr.Ord        ℐsim = SimOrd
AnnIntr.isPreorder ℐsim = soIsPreorder
AnnIntr.𝔹          ℐsim csκs ix◁ix′ e =
  SECtcSigned pos [] (getSECtc csκs) ×
  CollapsedCtcs (length (getLSCtc csκs)) (getSECtc csκs) (Vec.fromList (getLSCtc csκs))
AnnIntr.𝔹Sound     ℐsim (R-redex step)            inv inv′ mono (pmκ , c⊆s) = pmκ ,′ c⊆s
AnnIntr.𝔹Sound     ℐsim (R-bdr rule-no s s′ step) inv inv′ mono (pmκ , c⊆s) = pmκ ,′ c⊆s
AnnIntr.ℙ          ℐsim csκs ix◁ix′ em =
  AnnIntr.𝔹 ℐsim csκs ix◁ix′ ⌊ em ⌋m
