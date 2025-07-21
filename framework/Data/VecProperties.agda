{-# OPTIONS --without-K --safe #-}

module Data.VecProperties where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; trans)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; head; tail; _∷ʳ_; init; last; reverse)
import Data.Vec.Properties as Vec

open import Function.Base using (_∘_)

private variable
  A : Set
  m : ℕ

singleton-head-last : (xs : Vec A 1) → head xs ≡ last xs
singleton-head-last (x ∷ []) = refl

reverse-head-last : (xs : Vec A (suc m)) → head xs ≡ last (reverse xs)
reverse-head-last (x ∷ xs) rewrite Vec.reverse-∷ x xs = sym (Vec.last-∷ʳ x (reverse xs))

head-init : (xs : Vec A (suc (suc m))) → head xs ≡ head (init xs)
head-init (x ∷ xs) = refl

last-tail : (xs : Vec A (suc (suc m))) → last xs ≡ last (tail xs)
last-tail (x ∷ xs) = refl

init-tail : (xs : Vec A (suc (suc m))) → init (tail xs) ≡ tail (init xs)
init-tail (x ∷ xs) = refl

reverse-tail : (xs : Vec A (suc m)) → reverse (tail xs) ≡ init (reverse xs)
reverse-tail (x ∷ xs) rewrite Vec.reverse-∷ x xs = sym (Vec.init-∷ʳ x (reverse xs))
