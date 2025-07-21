{-# OPTIONS --without-K --safe #-}

module Syntax.Type where

open import Utils.Misc

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)

TCtxt : Set
TCtxt = List ⊤

infixr 60 `_
infixr 60 μ_
infixr 25 _`→_
infixr 20 _`+_
infixr 23 _`*_


infix 55 [t0↦_]

{-
  Natural:
    τ₁ `* τ₂

  Conatural:
    box τ₁ `* box τ₂

  Unknown:
    τ₁ `+ τ₂
    box (τ₁ `+ τ₂)
    box τ₁ `+ box τ₂

    μ τ
    μ (box τ) -- currently don't monitor recursive types
-}

private variable
  Δ Δ′ : TCtxt

data TyN : TCtxt → Set where
  `_ : (a : tt ∈ Δ) → TyN Δ
  `1 : TyN Δ
  `ℕ : TyN Δ
  _`*_ : TyN Δ → TyN Δ → TyN Δ
  _`+_ : TyN Δ → TyN Δ → TyN Δ
  Box : TyN Δ → TyN Δ
  _`→_ : TyN Δ → TyN Δ → TyN Δ
  μ_ : TyN (tt ∷ Δ) → TyN Δ

Ty = TyN []

pext : ∀ {A : Set} {x′ : A} {xs xs′} →
  (xs⊆xs′ : ∀ {x} → x ∈ xs → x ∈ xs′) →
  (∀ {x} → x ∈ x′ ∷ xs → x ∈ x′ ∷ xs′)
pext xs⊆xs′ (here refl)  = here refl
pext xs⊆xs′ (there x∈xs) = there (xs⊆xs′ x∈xs)

t0mapsto [t0↦_] : ∀ {a} → TyN Δ → tt ∈ (a ∷ Δ) → TyN Δ
t0mapsto ty (here refl) = ty
t0mapsto ty (there x∈Δ) = ` x∈Δ

[t0↦_] = t0mapsto

trename : TyN Δ → (ren : tt ∈ Δ → tt ∈ Δ′) → TyN Δ′
trename (` a) ren = ` ren a
trename `1 ren = `1
trename `ℕ ren = `ℕ
trename (ty₁ `* ty₂) ren = trename ty₁ ren `* trename ty₂ ren
trename (ty₁ `+ ty₂) ren = trename ty₁ ren `+ trename ty₂ ren
trename (Box ty) ren = Box (trename ty ren)
trename (tyₐ `→ tyᵣ) ren = trename tyₐ ren `→ trename tyᵣ ren
trename (μ ty) ren = μ trename ty (pext ren)

text : (tt ∈ Δ → TyN Δ′) →
       ∀ {a} → tt ∈ (a ∷ Δ) → TyN (a ∷ Δ′)
text ρ (here refl) = ` here refl
text ρ (there x∈Δ) = trename (ρ x∈Δ) there

tsubst : TyN Δ → (ρ : tt ∈ Δ → TyN Δ′) → TyN Δ′
tsubst (` a) ρ = ρ a
tsubst `1 ρ = `1
tsubst `ℕ ρ = `ℕ
tsubst (ty₁ `* ty₂) ρ = tsubst ty₁ ρ `* tsubst ty₂ ρ
tsubst (ty₁ `+ ty₂) ρ = tsubst ty₁ ρ `+ tsubst ty₂ ρ
tsubst (Box ty) ρ = Box (tsubst ty ρ)
tsubst (tyₐ `→ tyᵣ) ρ = tsubst tyₐ ρ `→ tsubst tyᵣ ρ
tsubst (μ ty) ρ = μ tsubst ty (text ρ)

Ctxt : Set
Ctxt = List Ty
