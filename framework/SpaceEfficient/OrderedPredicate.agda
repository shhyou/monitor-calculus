{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module SpaceEfficient.OrderedPredicate (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary
  using (IsPreorder; IsEquivalence; IsPartialOrder; Reflexive)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; length; lookup; _++_; map)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.IsNonEmpty
open import Syntax.Type
open import Syntax.Term
open import OpSemantics.Base
open import Contract.Common Label

open AnnTerm 𝒜 using (Ann; State)

Pred : Set
Pred = Ann ∣ `ℕ ∷ [] ⊢ `ℕ

record OrderedPredicate (getState : State → Status) (putState : Status → State → State) : Set₁ where
  inductive
  field
    ord-preds : List Pred
    ord-preds-unique : Unique ord-preds
    ord-preds-nonempty : IsNonEmpty ord-preds
    stronger? : Pred → Pred → Dec ⊤
    stronger?-reflexive : Reflexive (λ P Q → True (stronger? P Q))

  OPred : Set
  OPred = Σ Pred (λ e → e ∈ ord-preds)

  field
    _≼_ : OPred → OPred → Set
    isPartialOrder : IsPartialOrder _≡_ _≼_
    stronger⇒≼ : (P : OPred) → (Q : OPred) → True (stronger? (proj₁ P) (proj₁ Q)) → P ≼ Q
    ≼-steps : ∀ {s P Q n l} →
      P ≼ Q →
      Ann ∣ n isvalof `ℕ →
      getState s ≡ Ok →
      CheckNatPred {𝒜} getState putState (∅tr ⊢_,_⟶*_,_) l (proj₁ P) n s s →
      ∃[ l′ ] CheckNatPred {𝒜} getState putState (∅tr ⊢_,_⟶*_,_) l′ (proj₁ Q) n s s
