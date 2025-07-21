{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)

open import SpaceEfficient.Bounded.Base
  using ()
  renaming (𝒜ccctc to SE𝒜ccctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.Bounded.OpSemantics
  (Label : Set)
  (stronger? : SEPred Label (SE𝒜ccctc Label) → SEPred Label (SE𝒜ccctc Label) → Dec ⊤)
  where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; sym; trans)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.List.Base as List using (List; []; _∷_)

open import Syntax.Type
open import Syntax.Term
open import OpSemantics.Base
open import OpSemantics.Properties
open import Annotation.Language

open SpaceEfficient.Bounded.Base Label
open import Example.Count.Annotation
open import Contract.Common Label
open import Contract.Base Label 𝒜ccctc
open SpaceEfficient.OrderedPredicate Label 𝒜ccctc
open import SpaceEfficient.Base Label 𝒜ccctc
open import SpaceEfficient.Cost.Checking Label 𝒜ccctc
open import SpaceEfficient.Cost.Join Label 𝒜ccctc
open AnnTerm 𝒜ccctc hiding (State)

open SECtcTransitSteps
open CheckingCostTransitSteps
open CollapsingCostTransitSteps

𝒯cntctc : AnnTransit 𝒜ccctc
𝒯cntctc = (𝒯cctc 𝒜cctc-view stronger?) ∘tr
          (𝒯chkcost 𝒜chkcost-view 𝒜cctc-view stronger?) ∘tr
          (𝒯secost 𝒜secost-view 𝒜cctc-view stronger?) ∘tr
          (𝒯cnt 𝒜cnt-view)


check-nat-cctc-preserve-state : ∀ {s s* n} →
  ∀ cκ-preds →
  checkNatSECtcs 𝒜cctc-view stronger? cκ-preds n s s* →
  State.cost/chk s ≡ State.cost/chk s* ×
  State.cost/se s ≡ State.cost/se s* ×
  State.count s ≡ State.count s*
check-nat-cctc-preserve-state [] cκ-checks-tr =
  cong State.cost/chk cκ-checks-tr ,′
  cong State.cost/se cκ-checks-tr ,′
  cong State.count cκ-checks-tr
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-acc iv steps s₁≡Ok) , cκ-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps)
  = check-nat-cctc-preserve-state cκ-preds cκ-checks-tr
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-rej steps s₁′≡Ok s₁≡Err) , cκ-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps) | s₁≡Err
  = check-nat-cctc-preserve-state cκ-preds cκ-checks-tr
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-err steps l′ s₁≡Err) , cκ-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps)
  = ⊥-elim (status-distinct s₁≡Err)
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₂ (_ , refl , refl) , cκ-checks-tr)
  = check-nat-cctc-preserve-state cκ-preds cκ-checks-tr
