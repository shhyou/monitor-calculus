{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)

open import SpaceEfficient.Equivalence.Base
  using ()
  renaming (𝒜csctc to SE𝒜csctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.Equivalence.OpSemantics
  (Label : Set)
  (stronger? : SEPred Label (SE𝒜csctc Label) → SEPred Label (SE𝒜csctc Label) → Dec ⊤)
  where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; sym)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language
open import OpSemantics.Properties

open SpaceEfficient.Equivalence.Base Label

open import Contract.Common Label
open import Contract.Base Label 𝒜csctc
open import SpaceEfficient.Base Label 𝒜csctc
open SECtcTransitSteps
open AnnTerm 𝒜csctc using (Ann; State)

𝒯csctc : AnnTransit 𝒜csctc
𝒯csctc = (𝒯cctc 𝒜cctc-view stronger?) ∘tr (𝒯sctc 𝒜sctc-view ∅tr)


check-nat-cctc-preserve-error : ∀ {l st s* n} →
  ∀ cκ-preds →
  checkNatSECtcs 𝒜cctc-view stronger? cκ-preds n (Err l , st) s* →
  proj₁ s* ≡ Err l
check-nat-cctc-preserve-error [] cκ-checks-tr = cong proj₁ (sym cκ-checks-tr)
check-nat-cctc-preserve-error (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (Err≡Ok@() , refl) , check-nat) , cκ-checks-tr)
check-nat-cctc-preserve-error (flat l e ∷ cκ-preds)
  (_ , inj₂ (_ , refl , refl) , cκ-checks-tr)
  = check-nat-cctc-preserve-error cκ-preds cκ-checks-tr


check-nat-cctc-preserve-state : ∀ {s s* n} →
  ∀ cκ-preds →
  checkNatSECtcs 𝒜cctc-view stronger? cκ-preds n s s* →
  proj₂ s ≡ proj₂ s*
check-nat-cctc-preserve-state [] cκ-checks-tr = cong proj₂ cκ-checks-tr
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-acc iv steps s₁≡Ok) , cκ-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps)
  = check-nat-cctc-preserve-state cκ-preds cκ-checks-tr
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-rej steps s₁′≡Ok s₁≡Err) , cκ-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps) | cong proj₂ (sym s₁≡Err)
  = check-nat-cctc-preserve-state cκ-preds cκ-checks-tr
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-err steps l′ s₁≡Err) , cκ-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps)
  = ⊥-elim (status-distinct s₁≡Err)
check-nat-cctc-preserve-state (flat l e ∷ cκ-preds)
  (_ , inj₂ (_ , refl , refl) , cκ-checks-tr)
  = check-nat-cctc-preserve-state cκ-preds cκ-checks-tr


check-nat-sctc-preserve-error : ∀ {l st s n} →
  ∀ sκ-preds →
  checkNatSCtcs 𝒜sctc-view ∅tr sκ-preds n (st , Err l) s →
  proj₂ s ≡ Err l
check-nat-sctc-preserve-error [] sκs-checks-tr = cong proj₂ (sym sκs-checks-tr)
check-nat-sctc-preserve-error (flat l e ∷ sκ-preds)
  (_ , inj₁ (_ , (Err≡Ok@() , refl) , check-nat) , sκs-checks-tr)
check-nat-sctc-preserve-error (flat l e ∷ sκ-preds)
  (_ , inj₂ (_ , refl , refl) , sκs-checks-tr)
  = check-nat-sctc-preserve-error sκ-preds sκs-checks-tr


check-nat-sctc-preserve-state : ∀ {s* s′ n} →
  ∀ sκ-preds →
  checkNatSCtcs 𝒜sctc-view ∅tr sκ-preds n s* s′ →
  proj₁ s* ≡ proj₁ s′
check-nat-sctc-preserve-state [] sκs-checks-tr = cong proj₁ sκs-checks-tr
check-nat-sctc-preserve-state (flat l e ∷ sκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-acc iv steps s₁≡Ok) , sκs-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps)
  = check-nat-sctc-preserve-state sκ-preds sκs-checks-tr
check-nat-sctc-preserve-state (flat l e ∷ sκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-rej steps s₁′≡Ok s₁≡Err) , sκs-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps) | cong proj₁ (sym s₁≡Err)
  = check-nat-sctc-preserve-state sκ-preds sκs-checks-tr
check-nat-sctc-preserve-state (flat l e ∷ sκ-preds)
  (_ , inj₁ (_ , (refl , refl) , NP-err steps l′ s₁≡Err) , sκs-checks-tr)
  rewrite sym (∅tr-⟶*-preserve-state steps)
  = ⊥-elim (status-distinct s₁≡Err)
check-nat-sctc-preserve-state (flat l e ∷ sκ-preds)
  (_ , inj₂ (_ , refl , refl) , sκs-checks-tr)
  = check-nat-sctc-preserve-state sκ-preds sκs-checks-tr
