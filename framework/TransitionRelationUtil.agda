{-# OPTIONS --without-K --safe #-}

module TransitionRelationUtil (S : Set) where

open import Relation.Binary.PropositionalEquality.Core as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty as Empty renaming (⊥ to ⊥ty)
open import Data.Sum as Sum renaming (_⊎_ to _⊎ty_)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

infixr 1 _⊎_
infixr 7 _∩_
infixr 9 _∘_

∅ : S → S → Set
∅ = λ s s′ → ⊥ty

id : S → S → Set
id = λ s s′ → s ≡ s′

-- Facts, invariant propositions
[_] : Set → (S → S → Set)
[ A ] = λ s s′ → A

-- The composition of the state transition relations
_∘_ : (S → S → Set) → (S → S → Set) → (S → S → Set)
st1 ∘ st2 = λ s s′ → ∃ λ s₁ → st1 s s₁ × st2 s₁ s′

-- The intersection of state transition relations
_∩_ : (S → S → Set) → (S → S → Set) → (S → S → Set)
st₁ ∩ st₂ = λ s s′ → st₁ s s′ × st₂ s s′

-- The (disjoint) union of state transition relations
_⊎_ : (S → S → Set) → (S → S → Set) → (S → S → Set)
st₁ ⊎ st₂ = λ s s′ → st₁ s s′ ⊎ty st₂ s s′
