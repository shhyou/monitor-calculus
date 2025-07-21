{-# OPTIONS --safe --without-K #-}

open import Annotation.Language

module Contract.Vectorized (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; _≗_; subst; subst₂; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _∎; step-≡-⟨; step-≡-⟩; step-≡-∣)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; uncurry)

open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Vec.Base as Vec
  using (Vec; []; _∷_; head; tail; _∷ʳ_; init; last; map; reverse; _++_; zipWith)
import Data.Vec.Properties as Vec

open import Function.Base using (_∘_)

open import Utils.Misc
import Data.VecProperties as Vec⁺
open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
open AnnTerm 𝒜 using (Ann; State)

private variable
  m : ℕ
  Δ Δ′ : TCtxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ

-- vectorized renaming and substitution

sκsrename :
  Vec (SCtc1N Δ τ) m →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  Vec (SCtc1N Δ′ (trename τ ren)) m
sκsrename [] ren = []
sκsrename (sκ ∷ sκs) ren = sκrename sκ ren ∷ sκsrename sκs ren

sκsext :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m) →
  (a : tt ∈ (tt ∷ Δ)) → Vec (SCtc1N (tt ∷ Δ′) (text σ a)) m
sκsext {m = zero}  σκs a = []
sκsext {m = suc m} σκs a = sκext (head ∘ σκs) a ∷ sκsext (tail ∘ σκs) a

sκsext-≗ :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκs σκs′ : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m} →
  (∀ a → σκs a ≡ σκs′ a) →
  (a : tt ∈ (tt ∷ Δ)) →
  sκsext σκs a ≡ sκsext σκs′ a
sκsext-≗ {m = zero}  {σκs = σκs} {σκs′} eq a = refl
sκsext-≗ {m = suc m} {σκs = σκs} {σκs′} eq a rewrite sκsext-≗ (cong tail ∘ eq) a =
  cong (_∷ sκsext (tail ∘ σκs′) a) (sκext-≗ (cong head ∘ eq) a)

-- the computation rule of ext, vectorized version

sκsext-rename :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m) →
  (x∈Δ : tt ∈ Δ) →
  sκsext σκs (there x∈Δ) ≡ sκsrename (σκs x∈Δ) there
sκsext-rename {m = zero}  σκs x∈Δ with σκs x∈Δ
... | [] = refl
sκsext-rename {m = suc m} σκs x∈Δ with sκsext-rename (tail ∘ σκs) x∈Δ
... | tail-eq with σκs x∈Δ
... | sκ′ ∷ sκs′ = cong (sκrename sκ′ there ∷_) tail-eq

sκssubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  Vec (SCtc1N Δ τ) m →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m) →
  Vec (SCtc1N Δ′ (tsubst τ σ)) m
sκssubst []         σκs = []
sκssubst (sκ ∷ sκs) σκs = sκsubst sκ (head ∘ σκs) ∷ sκssubst sκs (tail ∘ σκs)

sκssubst-≗ :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκs σκs′ : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m} →
  (sκs : Vec (SCtc1N Δ τ) m) →
  (∀ a → σκs a ≡ σκs′ a) →
  sκssubst sκs σκs ≡ sκssubst sκs σκs′
sκssubst-≗                    []         eq = refl
sκssubst-≗ {σκs = σκs} {σκs′} (sκ ∷ sκs) eq rewrite sκssubst-≗ sκs (cong tail ∘ eq) =
  cong (_∷ sκssubst sκs (tail ∘ σκs′)) (sκsubst-≗ sκ (λ a → cong head (eq a)))

sκssubst-map :
  {σ : tt ∈ Δ → TyN Δ′} →
  (make-σκ : SCtc1N Δ τ → (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)) →
  (sκs : Vec (SCtc1N Δ τ) m) →
  map (λ sκ → sκsubst sκ (λ x → make-σκ sκ x)) sκs ≡
  sκssubst sκs (λ x → map (λ sκ → make-σκ sκ x) sκs)
sκssubst-map make-σκ []         = refl
sκssubst-map make-σκ (sκ ∷ sκs) = cong (sκsubst sκ (make-σκ sκ) ∷_) (sκssubst-map make-σκ sκs)




-- Commutativity of reverse and rename

sκsrename-∷ʳ-comm :
  (sκs : Vec (SCtc1N Δ τ) m) →
  (sκ : SCtc1N Δ τ) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  sκsrename (sκs ∷ʳ sκ) ren ≡ sκsrename sκs ren ∷ʳ sκrename sκ ren
sκsrename-∷ʳ-comm [] sκ′ ren = refl
sκsrename-∷ʳ-comm (sκ ∷ sκs) sκ′ ren = cong (sκrename sκ ren ∷_) (sκsrename-∷ʳ-comm sκs sκ′ ren)

sκsrename-reverse-comm :
  (sκs : Vec (SCtc1N Δ τ) m) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  reverse (sκsrename sκs ren) ≡ sκsrename (reverse sκs) ren
sκsrename-reverse-comm [] ren = refl
sκsrename-reverse-comm (sκ ∷ sκs) ren
  rewrite Vec.reverse-∷ (sκrename sκ ren) (sκsrename sκs ren)
        | Vec.reverse-∷ sκ sκs
        | sκsrename-∷ʳ-comm (reverse sκs) sκ ren
  = cong (_∷ʳ sκrename sκ ren) (sκsrename-reverse-comm sκs ren)




-- Commutativity of rename and constructors

sκsrename-*/c-comm :
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂ : Vec (SCtc1N Δ τ₂) m) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  sκsrename (zipWith _*/c_ sκs₁ sκs₂) ren ≡
    zipWith _*/c_ (sκsrename sκs₁ ren) (sκsrename sκs₂ ren)
sκsrename-*/c-comm []           []           ren = refl
sκsrename-*/c-comm (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) ren =
  cong  ((sκrename sκ₁ ren */c sκrename sκ₂ ren) ∷_)
        (sκsrename-*/c-comm sκs₁ sκs₂ ren)

sκsrename-+/c-comm :
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂ : Vec (SCtc1N Δ τ₂) m) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  sκsrename (zipWith _+/c_ sκs₁ sκs₂) ren ≡
    zipWith _+/c_ (sκsrename sκs₁ ren) (sκsrename sκs₂ ren)
sκsrename-+/c-comm []           []           ren = refl
sκsrename-+/c-comm (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) ren =
  cong  ((sκrename sκ₁ ren +/c sκrename sκ₂ ren) ∷_)
        (sκsrename-+/c-comm sκs₁ sκs₂ ren)

sκsrename-box/c-comm :
  (sκs : Vec (SCtc1N Δ τ) m) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  sκsrename (map box/c sκs) ren ≡
    map box/c (sκsrename sκs ren)
sκsrename-box/c-comm []         ren = refl
sκsrename-box/c-comm (sκ ∷ sκs) ren =
  cong (box/c (sκrename sκ ren) ∷_) (sκsrename-box/c-comm sκs ren)

sκsrename-→/c-comm :
  (sκsₐ : Vec (SCtc1N Δ τₐ) m) →
  (sκsᵣ : Vec (SCtc1N Δ τᵣ) m) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  sκsrename (zipWith _→/c_ sκsₐ sκsᵣ) ren ≡
    zipWith _→/c_ (sκsrename sκsₐ ren) (sκsrename sκsᵣ ren)
sκsrename-→/c-comm []           []           ren = refl
sκsrename-→/c-comm (sκₐ ∷ sκsₐ) (sκᵣ ∷ sκsᵣ) ren =
  cong  ((sκrename sκₐ ren →/c sκrename sκᵣ ren) ∷_)
        (sκsrename-→/c-comm sκsₐ sκsᵣ ren)

sκsrename-μ/c-comm :
  (sκs : Vec (SCtc1N (tt ∷ Δ) τ) m) →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  sκsrename (map μ/c_ sκs) ren ≡
    map μ/c_ (sκsrename sκs (pext ren))
sκsrename-μ/c-comm []         ren = refl
sκsrename-μ/c-comm (sκ ∷ sκs) ren =
  cong (μ/c (sκrename sκ (pext ren)) ∷_) (sκsrename-μ/c-comm sκs ren)




-- Commutativity of reverse and ext

sκsext-∷ʳ :
  {σ : tt ∈ Δ → TyN Δ′} →
  (rev-σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) (suc m)) →
  (a : tt ∈ (tt ∷ Δ)) →
  sκsext rev-σκs a ≡ sκsext (init ∘ rev-σκs) a ∷ʳ sκext (last ∘ rev-σκs) a
sκsext-∷ʳ {m = zero}  rev-σκs a = cong (_∷ []) (sκext-≗ (Vec⁺.singleton-head-last ∘ rev-σκs) a)
sκsext-∷ʳ {m = suc m} rev-σκs a =
  begin
    sκsext rev-σκs a
  ≡⟨⟩
    sκext (head ∘ rev-σκs) a ∷ (sκsext (tail ∘ rev-σκs) a)
  ≡⟨ cong (sκext (head ∘ rev-σκs) a ∷_)
          (sκsext-∷ʳ (tail ∘ rev-σκs) a) ⟩
    sκext (head ∘ rev-σκs) a ∷ (sκsext (init ∘ tail ∘ rev-σκs) a ∷ʳ sκext (last ∘ tail ∘ rev-σκs) a)
  ≡⟨ cong ((sκext (head ∘ rev-σκs) a ∷_) ∘ (sκsext (init ∘ tail ∘ rev-σκs) a ∷ʳ_))
          (sκext-≗ (sym ∘ Vec⁺.last-tail ∘ rev-σκs) a) ⟩
    sκext (head ∘ rev-σκs) a ∷ (sκsext (init ∘ tail ∘ rev-σκs) a ∷ʳ sκext (last ∘ rev-σκs) a)
  ≡⟨ cong ((sκext (head ∘ rev-σκs) a ∷_) ∘ (_∷ʳ sκext (last ∘ rev-σκs) a))
          (sκsext-≗ (Vec⁺.init-tail ∘ rev-σκs) a) ⟩
    sκext (head ∘ rev-σκs) a ∷ (sκsext (tail ∘ init ∘ rev-σκs) a ∷ʳ sκext (last ∘ rev-σκs) a)
  ≡⟨ cong (_∷ (sκsext (tail ∘ init ∘ rev-σκs) a ∷ʳ sκext (last ∘ rev-σκs) a))
          (sκext-≗ (Vec⁺.head-init ∘ rev-σκs) a) ⟩
    sκext (head ∘ init ∘ rev-σκs) a ∷ (sκsext (tail ∘ init ∘ rev-σκs) a ∷ʳ sκext (last ∘ rev-σκs) a)
  ≡⟨⟩
    (sκext (head ∘ init ∘ rev-σκs) a ∷ sκsext (tail ∘ init ∘ rev-σκs) a) ∷ʳ sκext (last ∘ rev-σκs) a
  ≡⟨⟩
    (sκsext (init ∘ rev-σκs) a) ∷ʳ sκext (last ∘ rev-σκs) a
  ∎

sκsext-reverse-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m) →
  (a : tt ∈ (tt ∷ Δ)) →
    (reverse ∘ sκsext σκs) a ≡ sκsext (reverse ∘ σκs) a
sκsext-reverse-comm {m = zero}  σκs a = refl
sκsext-reverse-comm {m = suc m} σκs a
  rewrite Vec.reverse-∷ (sκext (head ∘ σκs) a) (sκsext (tail ∘ σκs) a)
        | sκsext-reverse-comm (tail ∘ σκs) a
        | sκsext-≗ (Vec⁺.reverse-tail ∘ σκs) a
        | sκext-≗ (Vec⁺.reverse-head-last ∘ σκs) a
  = sym (sκsext-∷ʳ (reverse ∘ σκs) a)




-- Commutativity of reverse and subst

sκssubst-∷ʳ-comm : ∀ {m Δ Δ′ τ} →
  {σ : tt ∈ Δ → TyN Δ′} →
  (rev-sκs : Vec (SCtc1N Δ τ) m) →
  (sκ : SCtc1N Δ τ) →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) (suc m)) →
  sκssubst (rev-sκs ∷ʳ sκ) σκs ≡
    sκssubst rev-sκs (init ∘ σκs) ∷ʳ sκsubst sκ (last ∘ σκs)
sκssubst-∷ʳ-comm [] sκ σκs = cong (_∷ []) (sκsubst-≗ sκ (Vec⁺.singleton-head-last ∘ σκs))
sκssubst-∷ʳ-comm (rsκ ∷ rsκs) sκ σκs
  rewrite sκssubst-∷ʳ-comm rsκs sκ (tail ∘ σκs)
  = begin
      sκsubst rsκ (head ∘ σκs) ∷ (sκssubst rsκs (init ∘ tail ∘ σκs) ∷ʳ sκsubst sκ (last ∘ tail ∘ σκs))
    ≡⟨ cong ((sκsubst rsκ (head ∘ σκs) ∷_) ∘ (sκssubst rsκs (init ∘ tail ∘ σκs) ∷ʳ_))
            (sκsubst-≗ sκ (sym ∘ Vec⁺.last-tail ∘ σκs)) ⟩
      sκsubst rsκ (head ∘ σκs) ∷ (sκssubst rsκs (init ∘ tail ∘ σκs) ∷ʳ sκsubst sκ (last ∘ σκs))
    ≡⟨ cong ((sκsubst rsκ (head ∘ σκs) ∷_) ∘ (_∷ʳ sκsubst sκ (last ∘ σκs)))
            (sκssubst-≗ rsκs (Vec⁺.init-tail ∘ σκs)) ⟩
      sκsubst rsκ (head ∘ σκs) ∷ (sκssubst rsκs (tail ∘ init ∘ σκs) ∷ʳ sκsubst sκ (last ∘ σκs))
    ≡⟨ cong (_∷ (sκssubst rsκs (tail ∘ init ∘ σκs) ∷ʳ sκsubst sκ (last ∘ σκs)))
            (sκsubst-≗ rsκ (Vec⁺.head-init ∘ σκs)) ⟩
      sκsubst rsκ (head ∘ init ∘ σκs) ∷ (sκssubst rsκs (tail ∘ init ∘ σκs) ∷ʳ sκsubst sκ (last ∘ σκs))
    ∎

sκssubst-reverse-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (sκs : Vec (SCtc1N Δ τ) m) →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m) →
  reverse (sκssubst sκs σκs) ≡
    sκssubst (reverse sκs) (reverse ∘ σκs)
sκssubst-reverse-comm [] σκs = refl
sκssubst-reverse-comm (sκ ∷ sκs) σκs
  rewrite Vec.reverse-∷ (sκsubst sκ (head ∘ σκs)) (sκssubst sκs (tail ∘ σκs))
        | Vec.reverse-∷ sκ sκs
        | sκssubst-∷ʳ-comm (reverse sκs) sκ (reverse ∘ σκs)
  = begin
      reverse (sκssubst sκs (tail ∘ σκs)) ∷ʳ sκsubst sκ (head ∘ σκs)
    ≡⟨ cong (_∷ʳ sκsubst sκ (head ∘ σκs)) (sκssubst-reverse-comm sκs (tail ∘ σκs)) ⟩
      sκssubst (reverse sκs) (reverse ∘ tail ∘ σκs) ∷ʳ sκsubst sκ (head ∘ σκs)
    ≡⟨ cong (_∷ʳ sκsubst sκ (head ∘ σκs))
            (sκssubst-≗ (reverse sκs) (Vec⁺.reverse-tail ∘ σκs)) ⟩
      sκssubst (reverse sκs) (init ∘ reverse ∘ σκs) ∷ʳ sκsubst sκ (head ∘ σκs)
    ≡⟨ cong (sκssubst (reverse sκs) (init ∘ reverse ∘ σκs) ∷ʳ_)
            (sκsubst-≗ sκ (Vec⁺.reverse-head-last ∘ σκs)) ⟩
      sκssubst (reverse sκs) (init ∘ reverse ∘ σκs) ∷ʳ sκsubst sκ (last ∘ reverse ∘ σκs)
    ∎




-- Commutativity of subst and constructors

sκssubst-a-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (a : tt ∈ Δ) →
  (sκs : Vec (SCtc1N Δ (` a)) m) →
  (σκs : (a′ : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a′)) m) →
  sκssubst sκs σκs ≡ σκs a
sκssubst-a-comm a [] σκs with σκs a
... | [] = refl
sκssubst-a-comm a (` .a ∷ sκs) σκs with sκssubst-a-comm a sκs (tail ∘ σκs)
... | tail-eq with σκs a
... | sκ′ ∷ sκs′ = cong (sκ′ ∷_) tail-eq

sκssubst-*/c-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂  : Vec (SCtc1N Δ τ₂) m) →
  (σκs : (a′ : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a′)) m) →
  sκssubst (zipWith _*/c_ sκs₁ sκs₂) σκs ≡
    zipWith _*/c_ (sκssubst sκs₁ σκs) (sκssubst sκs₂ σκs)
sκssubst-*/c-comm []           []           σκs = refl
sκssubst-*/c-comm (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) σκs =
  cong  ((sκsubst sκ₁ (head ∘ σκs) */c sκsubst sκ₂ (head ∘ σκs)) ∷_)
        (sκssubst-*/c-comm sκs₁ sκs₂ (tail ∘ σκs))

sκssubst-+/c-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂  : Vec (SCtc1N Δ τ₂) m) →
  (σκs : (a′ : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a′)) m) →
  sκssubst (zipWith _+/c_ sκs₁ sκs₂) σκs ≡
    zipWith _+/c_ (sκssubst sκs₁ σκs) (sκssubst sκs₂ σκs)
sκssubst-+/c-comm []           []           σκs = refl
sκssubst-+/c-comm (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) σκs =
  cong  ((sκsubst sκ₁ (head ∘ σκs) +/c sκsubst sκ₂ (head ∘ σκs)) ∷_)
        (sκssubst-+/c-comm sκs₁ sκs₂ (tail ∘ σκs))

sκssubst-box/c-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (sκs : Vec (SCtc1N Δ τ) m) →
  (σκs : (a′ : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a′)) m) →
  sκssubst (map box/c sκs) σκs ≡
    map box/c (sκssubst sκs σκs)
sκssubst-box/c-comm []         σκs = refl
sκssubst-box/c-comm (sκ ∷ sκs) σκs =
  cong (box/c (sκsubst sκ (head ∘ σκs)) ∷_) (sκssubst-box/c-comm sκs (tail ∘ σκs))

sκssubst-→/c-comm : ∀ {m Δ Δ′ τₐ τᵣ} →
  {σ : tt ∈ Δ → TyN Δ′} →
  (sκsₐ : Vec (SCtc1N Δ τₐ) m) →
  (sκsᵣ  : Vec (SCtc1N Δ τᵣ) m) →
  (σκs : (a′ : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a′)) m) →
  sκssubst (zipWith _→/c_ sκsₐ sκsᵣ) σκs ≡
    zipWith _→/c_ (sκssubst sκsₐ σκs) (sκssubst sκsᵣ σκs)
sκssubst-→/c-comm []           []           σκs = refl
sκssubst-→/c-comm (sκₐ ∷ sκsₐ) (sκᵣ ∷ sκsᵣ) σκs =
  cong  ((sκsubst sκₐ (head ∘ σκs) →/c sκsubst sκᵣ (head ∘ σκs)) ∷_)
        (sκssubst-→/c-comm sκsₐ sκsᵣ (tail ∘ σκs))

sκssubst-μ/c-comm :
  {σ : tt ∈ Δ → TyN Δ′} →
  (sκs : Vec (SCtc1N (tt ∷ Δ) τ) m) →
  (σκs : (a′ : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a′)) m) →
  sκssubst (map μ/c_ sκs) σκs ≡
    map μ/c_ (sκssubst sκs (sκsext σκs))
sκssubst-μ/c-comm []         σκs = refl
sκssubst-μ/c-comm (sκ ∷ sκs) σκs =
  cong (μ/c (sκsubst sκ (head ∘ sκsext σκs)) ∷_) (sκssubst-μ/c-comm sκs (tail ∘ σκs))




-- Cancellation of selectors over constructors

*/c-sκ₁-cancel :
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂ : Vec (SCtc1N Δ τ₂) m) →
  map */c-sκ₁ (zipWith _*/c_ sκs₁ sκs₂) ≡ sκs₁
*/c-sκ₁-cancel [] [] = refl
*/c-sκ₁-cancel (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) = cong (sκ₁ ∷_) (*/c-sκ₁-cancel sκs₁ sκs₂)

*/c-sκ₂-cancel :
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂ : Vec (SCtc1N Δ τ₂) m) →
  map */c-sκ₂ (zipWith _*/c_ sκs₁ sκs₂) ≡ sκs₂
*/c-sκ₂-cancel [] [] = refl
*/c-sκ₂-cancel (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) = cong (sκ₂ ∷_) (*/c-sκ₂-cancel sκs₁ sκs₂)

+/c-sκ₁-cancel :
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂ : Vec (SCtc1N Δ τ₂) m) →
  map +/c-sκ₁ (zipWith _+/c_ sκs₁ sκs₂) ≡ sκs₁
+/c-sκ₁-cancel [] [] = refl
+/c-sκ₁-cancel (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) = cong (sκ₁ ∷_) (+/c-sκ₁-cancel sκs₁ sκs₂)

+/c-sκ₂-cancel : ∀ {m Δ τ₁ τ₂}
  (sκs₁ : Vec (SCtc1N Δ τ₁) m) →
  (sκs₂ : Vec (SCtc1N Δ τ₂) m) →
  map +/c-sκ₂ (zipWith _+/c_ sκs₁ sκs₂) ≡ sκs₂
+/c-sκ₂-cancel [] [] = refl
+/c-sκ₂-cancel (sκ₁ ∷ sκs₁) (sκ₂ ∷ sκs₂) = cong (sκ₂ ∷_) (+/c-sκ₂-cancel sκs₁ sκs₂)

box/c-sκ-cancel : ∀ {m Δ τ}
  (sκs : Vec (SCtc1N Δ τ) m) →
  map box/c-sκ (map box/c sκs) ≡ sκs
box/c-sκ-cancel [] = refl
box/c-sκ-cancel (sκ ∷ sκs) = cong (sκ ∷_) (box/c-sκ-cancel sκs)

→/c-dom-sκ-cancel :
  (sκsₐ : Vec (SCtc1N Δ τₐ) m) →
  (sκsᵣ : Vec (SCtc1N Δ τᵣ) m) →
  map →/c-dom-sκ (zipWith _→/c_ sκsₐ sκsᵣ) ≡ sκsₐ
→/c-dom-sκ-cancel [] [] = refl
→/c-dom-sκ-cancel (sκₐ ∷ sκsₐ) (sκᵣ ∷ sκsᵣ) = cong (sκₐ ∷_) (→/c-dom-sκ-cancel sκsₐ sκsᵣ)

→/c-rng-sκ-cancel :
  (sκsₐ : Vec (SCtc1N Δ τₐ) m) →
  (sκsᵣ : Vec (SCtc1N Δ τᵣ) m) →
  map →/c-rng-sκ (zipWith _→/c_ sκsₐ sκsᵣ) ≡ sκsᵣ
→/c-rng-sκ-cancel [] [] = refl
→/c-rng-sκ-cancel (sκₐ ∷ sκsₐ) (sκᵣ ∷ sκsᵣ) = cong (sκᵣ ∷_) (→/c-rng-sκ-cancel sκsₐ sκsᵣ)

μ/c-sκ′-cancel :
  (sκs : Vec (SCtc1N (tt ∷ Δ) τ) m) →
  map μ/c-sκ′ (map μ/c_ sκs) ≡ sκs
μ/c-sκ′-cancel [] = refl
μ/c-sκ′-cancel (sκ ∷ sκs) = cong (sκ ∷_) (μ/c-sκ′-cancel sκs)

μ/c-sκ-cancel :
  (sκs : Vec (SCtc1N (tt ∷ Δ) τ) m) →
  map μ/c-sκ (map μ/c_ sκs) ≡ map (λ sκ → sκsubst sκ [sκ0↦ μ/c sκ ]) sκs
μ/c-sκ-cancel [] = refl
μ/c-sκ-cancel (sκ ∷ sκs) = cong (sκsubst sκ [sκ0↦ μ/c sκ ] ∷_) (μ/c-sκ-cancel sκs)
