{-# OPTIONS --without-K --safe #-}

module Data.RawFilter where

open import Level using (Level; 0ℓ) renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Function.Base using (_∘′_; _∘₂′_; _$′_)

open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_)
open import Relation.Binary
  using ( Rel
        ; IsPreorder; IsEquivalence -- from Structures
        ; Preorder -- from Bundles
        )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base as Product using (Σ; proj₁; proj₂; _×_; _,′_)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _+_; _*_; _⊔_; _⊓_)
open import Data.List.Base using (List; []; _∷_; length)

private variable
  c ℓ : Level
  C D : Set c

record RawFilter {c} (C : Set c) ℓ : Set (lsuc (c l⊔ ℓ)) where
  no-eta-equality; pattern
  field
    Gen : Set c
    member : Gen → C → Set ℓ

record 𝕌 {c ℓ} {C : Set c} (F : RawFilter C ℓ) (P : Pred C ℓ) : Set (c l⊔ ℓ) where
  no-eta-equality; pattern
  field
    base : RawFilter.Gen F
    ultimately : ∀ x → RawFilter.member F base x → P x

make𝕌 : ∀ {c ℓ} {C : Set c} {F : RawFilter C ℓ} {P : Pred C ℓ} →
  {base : RawFilter.Gen F} →
  (∀ x → RawFilter.member F base x → P x) →
  𝕌 F P
make𝕌 {base = base} member = record { base = base ; ultimately = member }

infix 2 𝕌-syntax

𝕌-syntax : ∀ {c ℓ} {C : Set c} (F : RawFilter C ℓ) (P : Pred C ℓ) → Set (c l⊔ ℓ)
𝕌-syntax = 𝕌

syntax 𝕌-syntax F (λ x → P) = 𝕌[ x ∈ F ] P

pureᶠ : (A : Set) → RawFilter A 0ℓ
pureᶠ A = record { Gen = ⊤ ; member = λ tt x → ⊤ }

∀ᶠ : ∀ {c} (C : Set c) {D : C → Set c} →
  ((x : C) → RawFilter (D x) ℓ) → RawFilter ((x : C) → D x) (c l⊔ ℓ)
∀ᶠ C F = record
  { Gen = (x : C) → RawFilter.Gen (F x)
  ; member = λ to-base to-D → (x : C) → RawFilter.member (F x) (to-base x) (to-D x)
  }

Σᶠ : ∀ {c} (C : Set c) {D : C → Set c} →
  ((x : C) → RawFilter (D x) ℓ) →
  RawFilter (Σ C D) ℓ
Σᶠ C F = record
  { Gen = (x : C) → RawFilter.Gen (F x)
  ; member = λ to-base p → RawFilter.member (F (proj₁ p)) (to-base (proj₁ p)) (proj₂ p)
  }

infix 1 Σᶠ-syntax

Σᶠ-syntax : ∀ {c} (C : Set c) {D : C → Set c} →
            ((x : C) → RawFilter (D x) ℓ) →
            RawFilter (Σ C D) ℓ
Σᶠ-syntax = Σᶠ

syntax Σᶠ-syntax F (λ c → e) = Σᶠ[ c ∈ F ] e

infix 1 ∃ᶠ-syntax

∃ᶠ : ∀ {c} {C : Set c} {D : C → Set c} →
  ((x : C) → RawFilter (D x) ℓ) →
  RawFilter (Σ C D) ℓ
∃ᶠ = Σᶠ _

∃ᶠ-syntax : ∀ {c} {C : Set c} {D : C → Set c} →
            ((x : C) → RawFilter (D x) ℓ) →
            RawFilter (Σ C D) ℓ
∃ᶠ-syntax = ∃ᶠ

syntax ∃ᶠ-syntax (λ c → e) = ∃ᶠ[ c ] e

infixr 1 _×ᶠ_

_×ᶠ_ : RawFilter C ℓ → RawFilter D ℓ → RawFilter (C × D) ℓ
F₁ ×ᶠ F₂ = record
  { Gen = Gen F₁ × Gen F₂
  ; member = (Product.uncurry′ _×_) ∘₂′ (Product.zip′ (member F₁) (member F₂))
  }
  where open RawFilter

ℕ≤ᶠ : RawFilter ℕ 0ℓ
ℕ≤ᶠ = record { Gen = ℕ ; member = λ x₀ x → x₀ ≤ x }

ListLenᶠ* : (A : Set) → RawFilter (List A) 0ℓ
ListLenᶠ* A = record { Gen = ℕ ; member = λ len₀ xs → len₀ ≤ length xs }

Dominated′ : {A : Set} → (F : RawFilter A 0ℓ) → (f g : A → ℕ) → Set
Dominated′ F f g = 𝕌[ c ∈ ℕ≤ᶠ ] 𝕌[ x ∈ F ] f x ≤ c * g x

Dominated : {A : Set} → (F : RawFilter A 0ℓ) → (h : A → ℕ × ℕ) → Set
Dominated F h = Dominated′ F (proj₁ ∘′ h) (proj₂ ∘′ h)
