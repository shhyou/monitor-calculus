{-# OPTIONS --without-K --safe #-}

module Data.NatProperties where

open import Relation.Binary.PropositionalEquality

open import Data.Nat.Base
open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans; module ≤-Reasoning)

open import Function.Base using (_∘′_)

-------------------------------------------------------------------------
-- Finite summation identities

-- Also see: (very similar, although different in that we don't use Fin here.)
-- Algebra.Properties.Semiring.Sum
-- Algebra.Properties.Monoid.Sum
-- Algebra.Properties.CommutativeMonoid.Sum

∑ : (n : ℕ) → (f : ℕ → ℕ) → ℕ
∑ 0       f = 0
∑ (suc n) f = f n + ∑ n f

∑-syntax : (n : ℕ) → (f : ℕ → ℕ) → ℕ
∑-syntax = ∑

infix 5 ∑-syntax

syntax ∑-syntax n (λ i → expr) = ∑[ i < n ] expr

*-distribˡ-∑ : ∀ k m {f} → k * ∑ m f ≡ ∑ m ((k *_) ∘′ f)
*-distribˡ-∑ k zero    {f} = Nat.*-zeroʳ k
*-distribˡ-∑ k (suc m) {f} = begin
  k * ∑ (suc m) f              ≡⟨⟩
  k * (f m + ∑ m f)            ≡⟨ Nat.*-distribˡ-+ k (f m) (∑ m f) ⟩
  k * f m + k * ∑ m f          ≡⟨ cong (k * f m +_) (*-distribˡ-∑ k m) ⟩
  k * f m + ∑ m ((k *_) ∘′ f)  ≡⟨⟩
  ∑ (suc m) ((k *_) ∘′ f)      ∎ where open ≡-Reasoning

∑-assocʳ-+ : ∀ m {f} → ∑ (suc m) f ≡ ∑ m (f ∘′ suc) + f 0
∑-assocʳ-+ zero    {f} = Nat.+-identityʳ (f 0)
∑-assocʳ-+ (suc m) {f} = begin
  ∑ (suc (suc m)) f                   ≡⟨⟩
  f (suc m) + ∑ (suc m) f             ≡⟨ cong (f (suc m) +_) (∑-assocʳ-+ m) ⟩
  f (suc m) + (∑ m (f ∘′ suc) + f 0)  ≡⟨ Nat.+-assoc (f (suc m)) (∑ m (f ∘′ suc)) (f 0) ⟨
  f (suc m) + ∑ m (f ∘′ suc) + f 0    ≡⟨⟩
  ∑ (suc m) (f ∘′ suc) + f 0          ∎ where open ≡-Reasoning

∑-^-≤-^ : ∀ m a → 2 ≤ a → ∑[ i < m ] a ^ i ≤ a ^ (suc m)
∑-^-≤-^ zero    a 2≤a = ≤-trans z≤n (Nat.*-monoˡ-≤ 1 2≤a)
∑-^-≤-^ (suc m) a 2≤a = begin
  ∑[ i < suc m ] a ^ i     ≡⟨⟩
  aᵐ + (∑[ i < m ] a ^ i)  ≤⟨ Nat.+-monoʳ-≤ aᵐ (∑-^-≤-^ m a 2≤a) ⟩
  aᵐ + a ^ (suc m)         ≡⟨ cong (_+ a ^ (suc m)) (Nat.*-identityˡ aᵐ) ⟨
  1 * aᵐ + a ^ (suc m)     ≡⟨ Nat.*-distribʳ-+ aᵐ 1 a ⟨
  (1 + a) * aᵐ             ≤⟨ Nat.*-monoˡ-≤ aᵐ 1+a≤a² ⟩
  (a * a) * aᵐ             ≡⟨ Nat.*-assoc a a aᵐ ⟩
  a * (a * aᵐ)             ≡⟨⟩
  a ^ (suc (suc m))        ∎
  where open ≤-Reasoning
        aᵐ = a ^ m

        1+a≤a² : 1 + a ≤ a * a
        1+a≤a² = begin
          1 + a ≤⟨ Nat.+-monoˡ-≤ a (≤-trans (s≤s z≤n) 2≤a) ⟩
          a + a ≡⟨ cong (a +_) (Nat.*-identityˡ a) ⟨
          2 * a ≤⟨ Nat.*-monoˡ-≤ a 2≤a ⟩
          a * a ∎

geometry-sum : ∀ x c a b m →
  x ≤ c * (a ^ m) + b * (∑[ i < m ] a ^ i) →
  a * x + b ≤ c * (a ^ suc m) + b * (∑[ i < suc m ] a ^ i)
geometry-sum x c a b m x≤exp = begin
    a * x + b
  ≤⟨ Nat.+-monoˡ-≤ b (Nat.*-monoʳ-≤ a x≤exp) ⟩
    a * (c * aᵐ + b * (∑[ i < m ] a ^ i)) + b
  ≡⟨ cong (_+ b) (Nat.*-distribˡ-+ a _ _) ⟩
    a * (c * aᵐ) + a * (b * (∑[ i < m ] a ^ i)) + b
  ≡⟨ cong (λ X → X + a * (b * (∑[ i < m ] a ^ i)) + b) (EQR.begin
      a * (c * aᵐ) EQR.≡⟨ Nat.*-assoc a c aᵐ ⟨
      (a * c) * aᵐ EQR.≡⟨ cong (_* aᵐ) (Nat.*-comm a c) ⟩
      (c * a) * aᵐ EQR.≡⟨ Nat.*-assoc c a aᵐ ⟩
      c * a¹⁺ᵐ EQR.∎) ⟩
    c * a¹⁺ᵐ + a * (b * (∑[ i < m ] a ^ i)) + b
  ≡⟨ cong (λ X → c * a¹⁺ᵐ + X + b) (EQR.begin
      a * (b * (∑[ i < m ] a ^ i)) EQR.≡⟨ Nat.*-assoc a b _ ⟨
      (a * b) * (∑[ i < m ] a ^ i) EQR.≡⟨ cong (_* (∑[ i < m ] a ^ i)) (Nat.*-comm a b) ⟩
      (b * a) * (∑[ i < m ] a ^ i) EQR.≡⟨ Nat.*-assoc b a _ ⟩
      b * (a * (∑[ i < m ] a ^ i)) EQR.∎) ⟩
    c * a¹⁺ᵐ + b * (a * (∑[ i < m ] a ^ i)) + b
  ≡⟨ cong (c * a¹⁺ᵐ + b * (a * (∑[ i < m ] a ^ i)) +_) (Nat.*-identityʳ b) ⟨
    c * a¹⁺ᵐ + b * (a * (∑[ i < m ] a ^ i)) + b * 1
  ≡⟨ Nat.+-assoc (c * a¹⁺ᵐ) _ _ ⟩
    c * a¹⁺ᵐ + (b * (a * (∑[ i < m ] a ^ i)) + b * 1)
  ≡⟨ cong (c * a¹⁺ᵐ +_) (Nat.*-distribˡ-+ b _ _) ⟨
    c * a¹⁺ᵐ + b * (a * (∑[ i < m ] a ^ i) + 1)
  ≡⟨ cong (λ X → c * a¹⁺ᵐ + b * X) (EQR.begin
      a * (∑[ i < m ] a ^ i) + 1   EQR.≡⟨ cong (_+ 1) (*-distribˡ-∑ a m) ⟩
      (∑[ i < m ] a ^ (suc i)) + 1 EQR.≡⟨ ∑-assocʳ-+ m ⟨
      ∑[ i < suc m ] a ^ i         EQR.∎) ⟩
    c * a¹⁺ᵐ + b * (∑[ i < suc m ] a ^ i) ∎
  where open ≤-Reasoning
        module EQR = ≡-Reasoning

        aᵐ = a ^ m
        a¹⁺ᵐ = a ^ suc m

-------------------------------------------------------------------------
-- Miscellaneous algebraic identities

^-distribʳ-* : ∀ m n o → (m * n) ^ o ≡ m ^ o * n ^ o
^-distribʳ-* m n zero    = refl
^-distribʳ-* m n (suc o) = begin
  (m * n) * (m * n) ^ o     ≡⟨ cong (mn *_) (^-distribʳ-* m n o) ⟩
  (m * n) * (m ^ o * n ^ o) ≡⟨ Nat.*-assoc mn mᵒ nᵒ ⟨
  (m * n * m ^ o) * n ^ o   ≡⟨ cong (_* nᵒ) (Nat.*-assoc m n mᵒ) ⟩
  (m * (n * m ^ o)) * n ^ o ≡⟨ cong ((_* nᵒ) ∘′ (m *_)) (Nat.*-comm n mᵒ) ⟩
  (m * (m ^ o * n)) * n ^ o ≡⟨ cong (_* nᵒ) (Nat.*-assoc m mᵒ n) ⟨
  (m * m ^ o * n) * n ^ o   ≡⟨ Nat.*-assoc (m * mᵒ) n nᵒ ⟩
  (m * m ^ o) * (n * n ^ o) ∎
  where open ≡-Reasoning
        mn = m * n
        nᵒ = n ^ o
        mᵒ = m ^ o

m+m≡2m : ∀ m → m + m ≡ 2 * m
m+m≡2m m = begin
  m + m     ≡⟨ cong (m +_) (Nat.*-identityˡ m) ⟨
  m + 1 * m ≡⟨⟩
  2 * m     ∎ where open ≡-Reasoning

mn+nm=2mn : ∀ m n → m * n + n * m ≡ 2 * (m * n)
mn+nm=2mn m n = begin
  m * n + n * m       ≡⟨ cong (m * n +_) (Nat.*-comm n m) ⟩
  m * n + m * n       ≡⟨ cong (m * n +_) (Nat.+-identityʳ (m * n)) ⟨
  m * n + (m * n + 0) ≡⟨⟩
  2 * (m * n)         ∎ where open ≡-Reasoning

[m+n]²≡m²+2mn+n² : ∀ m n → (m + n) ^ 2 ≡ m ^ 2 + 2 * (m * n) + n ^ 2
[m+n]²≡m²+2mn+n² m n = begin
    (m + n) ^ 2
  ≡⟨ cong ((m + n) *_) (Nat.*-identityʳ (m + n)) ⟩
    (m + n) * (m + n)
  ≡⟨ Nat.*-distribʳ-+ (m + n) m n ⟩
    m * (m + n) + n * (m + n)
  ≡⟨ cong (_+ n * (m + n)) (Nat.*-distribˡ-+ m m n) ⟩
    _
  ≡⟨ cong (λ X → m * m + m * n + X) (Nat.*-distribˡ-+ n m n) ⟩
    m * m + m * n + (n * m + n * n)
  ≡⟨ k+l+[m+n]≡k+[l+m]+n (m * m) (m * n) (n * m) ⟩
    m * m + (m * n + n * m) + n * n
  ≡⟨ cong (λ X → m * m + X + n * n) (mn+nm=2mn m n) ⟩
    m * m + 2 * (m * n) + n * n
  ≡⟨ cong (λ X → m * m + 2 * (m * n) + n * X) (Nat.*-identityʳ n) ⟨
    m * m + 2 * (m * n) + n ^ 2
  ≡⟨ cong (λ X → m * X + 2 * (m * n) + n ^ 2) (Nat.*-identityʳ m) ⟨
    m ^ 2 + 2 * (m * n) + n ^ 2 ∎
  where open ≡-Reasoning

        k+l+[m+n]≡k+[l+m]+n : ∀ k l m {n} → k + l + (m + n) ≡ k + (l + m) + n
        k+l+[m+n]≡k+[l+m]+n k l m {n} = begin
          k + l + (m + n) ≡⟨ Nat.+-assoc (k + l) m n ⟨
          k + l + m + n   ≡⟨ cong (_+ n) (Nat.+-assoc k l m) ⟩
          k + (l + m) + n ∎

m≤1+m : ∀ m → m ≤ 1 + m
m≤1+m m = Nat.m≤n⇒m≤1+n ≤-refl

m⊔1≤m⊔n⊔1 : ∀ m n → m ⊔ 1 ≤ m ⊔ n ⊔ 1
m⊔1≤m⊔n⊔1 m n = Nat.⊔-monoˡ-≤ 1 (Nat.m≤m⊔n m n)

m⊔1≤n⊔m⊔1 : ∀ m n → m ⊔ 1 ≤ n ⊔ m ⊔ 1
m⊔1≤n⊔m⊔1 m n = Nat.⊔-monoˡ-≤ 1 (Nat.m≤n⊔m n m)

1+[m+[n+1]]≡2+[m+n] : ∀ m n → 1 + (m + (n + 1)) ≡ 2 + m + n
1+[m+[n+1]]≡2+[m+n] m n = begin
  1 + (m + (n + 1)) ≡⟨ cong (1 +_) (Nat.+-assoc m n 1) ⟨
  1 + ((m + n) + 1) ≡⟨ cong (1 +_) (Nat.+-comm (m + n) 1) ⟩
  2 + (m + n)       ∎ where open ≡-Reasoning
