{-# OPTIONS --without-K --safe #-}

module Data.Tick where

open Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _⊔_)
import Data.Nat.Properties as Nat
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_; _,′_; ∃)
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad

private variable
  ℓ : Level
  A B C : Set ℓ

infix 0 ✓_

record Tick {ℓ} (A : Set ℓ) : Set ℓ where
  no-eta-equality; pattern
  constructor mkTick
  field
    tick : ℕ
    value : A

✓_ : Tick A → Tick A
✓ ma = mkTick (suc (Tick.tick ma)) (Tick.value ma)

functor : RawFunctor {ℓ} Tick
RawFunctor._<$>_ functor f ma = mkTick (Tick.tick ma) (f (Tick.value ma))

applicative : RawApplicative {ℓ} {ℓ} Tick
RawApplicative.rawFunctor applicative = functor
RawApplicative.pure applicative a = mkTick 0 a
RawApplicative._<*>_ applicative mf ma = mkTick (Tick.tick mf + Tick.tick ma)
                                                (Tick.value mf (Tick.value ma))

monad : RawMonad {ℓ} {ℓ} Tick
RawMonad.rawApplicative monad = applicative
RawMonad._>>=_ monad ma f = mkTick (Tick.tick ma + Tick.tick mb) (Tick.value mb)
  where mb = f (Tick.value ma)

runTick : Tick A → A × ℕ
runTick m = Tick.value m ,′ Tick.tick m

evalTick : Tick A → A
evalTick = Tick.value

execTick : Tick A → ℕ
execTick = Tick.tick

ifTick : (b : Bool) → (m₁ : Tick A) → (m₂ : Tick A) → Tick A
ifTick b m₁ m₂ = mkTick (Tick.tick m₁ ⊔ Tick.tick m₂)
                        (if b then Tick.value m₁ else Tick.value m₂)

tick-if : ∀ b {m₁ m₂ : Tick A} →
  Tick.value (if b then m₁ else m₂) ≡ Tick.value (ifTick b m₁ m₂) ×
  Tick.tick  (if b then m₁ else m₂) ≤ Tick.tick  (ifTick b m₁ m₂)
tick-if false {m₁} {m₂} = refl ,′ Nat.m≤n⊔m (Tick.tick m₁) (Tick.tick m₂)
tick-if true  {m₁} {m₂} = refl ,′ Nat.m≤m⊔n (Tick.tick m₁) (Tick.tick m₂)
