{-# OPTIONS --without-K --safe #-}

module Data.IsNonEmpty where

open import Level using (Level)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List.Base using (List; []; _∷_; length)

private variable
  a : Level
  A : Set a
  xs : List A

data IsNonEmpty {A : Set a} : List A → Set a where
  _∷⁺_ : ∀ x xs → IsNonEmpty (x ∷ xs)

IsNonEmpty-length : IsNonEmpty xs → 1 ≤ length xs
IsNonEmpty-length (x ∷⁺ xs) = s≤s z≤n
