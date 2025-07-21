{-# OPTIONS --without-K --safe #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.TimeComplexity
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (stronger? : SEPred Label 𝒜 → SEPred Label 𝒜 → Dec ⊤)
  where

open import Level using (Level; 0ℓ) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; _⊔_; _⊓_)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; ∃₂)

open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Effect.Monad using (RawMonad)

open import Function.Base using (_∘′_; _$′_)

open import Data.Tick
open import Data.RawFilter
open import Data.NatProperties

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
open SpaceEfficient.Base Label 𝒜
open AnnTerm 𝒜 hiding (State)

open SECtcTransitSteps 𝒜cctc-view stronger?

open import SpaceEfficient.Height Label 𝒜
open import SpaceEfficient.Size Label 𝒜
open import SpaceEfficient.LeafPredicate Label 𝒜
open import SpaceEfficient.Properties.Sublist Label 𝒜cctc-view stronger?

private variable
  c c₀ h k l m n : ℕ
  Δ : TCtxt
  τ : TyN Δ
  eₚ : Ann ∣ (`ℕ ∷ []) ⊢ `ℕ
  cκ cκ′ : SECtcN Δ τ

inRange : ℕ → ℕ → ℕ → Set
inRange lb ub = Product.uncurry′ _×_ ∘′ Product.< (lb ≤_) , (_≤ ub) >

cps-inRange-weaken :
  k ≤ m →
  n ≤ l →
  SECtcPreds (inRange m n ∘′ length) cκ →
  SECtcPreds (inRange k l ∘′ length) cκ
cps-inRange-weaken k≤m n≤l cps =
  cps-map (λ where (m≤len , len≤n) → ≤-trans k≤m m≤len ,′ ≤-trans len≤n n≤l) cps

-- Probably can also be expressed as pureᶠ (∃ (SECtcPreds ((1 ≤_) ∘′ length) {Δ} {`ℕ}))
SECtcNonEmptyᶠ : ∀ Δ τ → RawFilter (SECtcN Δ τ) 0ℓ
SECtcNonEmptyᶠ Δ τ = record
  { Gen = ⊤
  ; member = λ tt cκ → SECtcPreds ((1 ≤_) ∘′ length) cκ
  }

DropLinearSpec : Set
DropLinearSpec =
  Dominated (pureᶠ (Ann ∣ (`ℕ ∷ []) ⊢ `ℕ)  ×ᶠ  Σᶠ _ λ Δ → ListLenᶠ* (SCtc1N Δ `ℕ)) λ where
    (e , Δ , preds) →
      execTick (✓ drop {Δ} preds e) ,′
      length preds

JoinFlatsQuadraticSpec : Set
JoinFlatsQuadraticSpec =
  Dominated (∃ᶠ[ Δ ] ListLenᶠ* (SCtc1N Δ `ℕ) ×ᶠ ListLenᶠ* (SCtc1N Δ `ℕ)) λ where
    (Δ , preds , preds′) →
      execTick (✓ join-flats {Δ} preds preds′) ,′
      (length preds + length preds′) ^ 2

JoinExpQuadraticSpec : Set
JoinExpQuadraticSpec =
  Dominated (∃ᶠ[ Δ ] ∃ᶠ[ τ ] SECtcNonEmptyᶠ Δ τ ×ᶠ SECtcNonEmptyᶠ Δ τ) λ where
    (Δ , τ , cκ , cκ′) →
      execTick (✓ join cκ cκ′) ,′
      (leaf-size cκ ⊔ leaf-size cκ′ ⊔ 1) ^ 2 * 2 ^ (sectc-height cκ ⊔ sectc-height cκ′)

drop-linear-c₀ = 6

drop-linear-ind :
  ∀ c (_ : drop-linear-c₀ ≤ c) →
  ∀ preds (_ : 1 ≤ length preds) →
  execTick (✓ drop {Δ} preds eₚ) ≤ c * length preds
drop-linear-ind {Δ = Δ} {eₚ = e} c c₀≤c (flat l e′ ∷ []) preds-geq = begin
  execTick (✓ drop (flat l e′ ∷ []) e) ≤⟨ Nat.+-monoʳ-≤ 3 (proj₂ (tick-if (Dec.does (stronger? e e′)))) ⟩
  drop-linear-c₀                       ≤⟨ c₀≤c ⟩
  c                                    ≡⟨ Nat.*-identityʳ c ⟨
  c * length (flat {Δ = Δ} l e′ ∷ [])  ∎ where open ≤-Reasoning
drop-linear-ind {eₚ = e} c c₀≤c (flat l e′ ∷ preds@(_ ∷ _)) preds-geq = begin
  3 + execTick (if Dec.does (stronger? e e′)
                  then ✓ drop preds e
                  else do collapsedPreds ← ✓ drop preds e
                          ✓ return (flat l e′ ∷ collapsedPreds))
    ≤⟨ Nat.+-monoʳ-≤ 3 (proj₂ (tick-if (Dec.does (stronger? e e′)))) ⟩
  3 + (execTick (✓ drop preds e) ⊔ (execTick (✓ drop preds e) + 1))   ≡⟨⟩
  3 + (1 + (execTick (drop preds e) ⊔ (execTick (drop preds e) + 1))) ≡⟨⟩
  4 + (execTick (drop preds e) ⊔ (execTick (drop preds e) + 1))
    ≡⟨ cong (4 +_) (Nat.m≤n⇒m⊔n≡n (Nat.m≤m+n _ 1)) ⟩
  4 + (execTick (drop preds e) + 1)   ≡⟨ cong (4 +_) (Nat.+-comm _ 1) ⟩
  4 + suc (execTick (drop preds e))   ≤⟨ Nat.+-monoʳ-≤ 4 (drop-linear-ind c c₀≤c preds (s≤s z≤n)) ⟩
  4 + c * length preds                ≤⟨ Nat.+-monoˡ-≤ (c * length preds) (Nat.≤-trans 4≤c₀ c₀≤c) ⟩
  c + c * length preds                ≡⟨ Nat.*-suc c _ ⟨
  c * (1 + length preds)              ∎
  where open ≤-Reasoning
        open RawMonad {f = lzero} monad
        4≤c₀ = s≤s (s≤s (s≤s (s≤s z≤n)))

drop-is-linear : DropLinearSpec
drop-is-linear =
  make𝕌 $′ λ c c₀≤c →
  make𝕌 $′ λ where
    (e , Δ , preds) (_ , 1≤|preds|) →
      drop-linear-ind c c₀≤c preds 1≤|preds|

module join-flats-quadratic (drop-linear-spec : DropLinearSpec) where

  c₀/drop = 𝕌.base drop-linear-spec
  drop-linear = 𝕌.ultimately drop-linear-spec _ ≤-refl
  Δ→len₀/drop = proj₂ (𝕌.base drop-linear)

  join-flats-c₀ = 4 + c₀/drop

  join-flats-c₀-≤-trans : join-flats-c₀ ≤ c → c₀/drop ≤ c
  join-flats-c₀-≤-trans = ≤-trans (Nat.m≤n+m _ 4)

  join-flats-quadratic-ind :
    let len₀/drop = Δ→len₀/drop Δ in
    ∀ c (_ : join-flats-c₀ ≤ c) →
    ∀ preds  (_ : 1 ≤ length preds) →
    ∀ preds′ (_ : 1 ⊔ len₀/drop ≤ length preds′) →
    execTick (✓ join-flats {Δ} preds preds′) ≤ c * (length preds + length preds′) ^ 2
  join-flats-quadratic-ind {Δ = Δ} c c₀≤c (flat l e ∷ []) preds-geq preds′ preds′-geq = begin
      3 + (execTick (✓ drop preds′ e) + 1)
    ≡⟨ cong (3 +_) (Nat.+-comm _ 1) ⟩
      4 + execTick (✓ drop preds′ e)
    ≤⟨ Nat.+-monoʳ-≤ 4 drop-leq ⟩
      4 + c₀/drop * length preds′
    ≤⟨ Nat.+-monoˡ-≤ (c₀/drop * length preds′) (Nat.*-monoʳ-≤ 4 1≤preds′) ⟩
      4 * length preds′ + c₀/drop * length preds′
    ≡⟨ Nat.*-distribʳ-+ (length preds′) 4 c₀/drop ⟨
      join-flats-c₀ * length preds′
    ≤⟨ Nat.*-monoˡ-≤ (length preds′) c₀≤c ⟩
      c * length preds′
    ≡⟨ cong (c *_) (Nat.*-identityˡ _) ⟨
      c * (1 * length preds′)
    ≤⟨ Nat.*-monoʳ-≤ c (Nat.*-mono-≤ (s≤s (z≤n {length preds′})) (Nat.m≤n+m (length preds′) 1)) ⟩
      c * ((1 + length preds′) * (1 + length preds′)) -- y^2  IS  y * (y * 1)
    ≡⟨ cong ((c *_) ∘′ ((1 + length preds′) *_)) (Nat.*-identityʳ _) ⟨
      c * (1 + length preds′) ^ 2 ∎
    where open ≤-Reasoning

          len₀/drop = Δ→len₀/drop Δ
          len₀/drop≤preds′ = ≤-trans (Nat.m≤n⊔m 1 len₀/drop) preds′-geq
          1≤preds′         = ≤-trans (Nat.m≤m⊔n 1 len₀/drop) preds′-geq

          drop-leq : execTick (✓ drop preds′ e) ≤ c₀/drop * length preds′
          drop-leq = 𝕌.ultimately drop-linear (e , Δ , preds′) (tt , len₀/drop≤preds′)

  join-flats-quadratic-ind {Δ = Δ} c c₀≤c (flat l e ∷ preds@(_ ∷ _)) preds-geq preds′ preds′-geq = begin
      execTick (✓ do mergedPreds    ← ✓ join-flats preds preds′
                     collapsedPreds ← ✓ drop mergedPreds e
                     ✓ return (flat l e ∷ collapsedPreds))
    ≡⟨⟩
      1 + execTick (✓ join-flats preds preds′)
        + (execTick (✓ drop (evalTick (✓ join-flats preds preds′)) e) + 1)
    ≡⟨ cong ((1 +_) ∘′ (execTick (✓ join-flats preds preds′) +_)) (Nat.+-comm _ 1) ⟩
      1 + execTick (✓ join-flats preds preds′)
        + (1 + execTick (✓ drop (evalTick (✓ join-flats preds preds′)) e))
    ≡⟨ cong (1 +_) (Nat.+-comm (execTick (✓ join-flats preds preds′)) _) ⟩
      2 + execTick (✓ drop (evalTick (✓ join-flats preds preds′)) e)
        + execTick (✓ join-flats preds preds′)
    ≤⟨ Nat.+-monoʳ-≤ 2 (Nat.+-monoʳ-≤ _
        (join-flats-quadratic-ind c c₀≤c preds (s≤s z≤n) preds′ preds′-geq)) ⟩
      2 + execTick (✓ drop (evalTick (✓ join-flats preds preds′)) e) + c * (N + M) ^ 2
    ≤⟨ Nat.+-monoʳ-≤ 2 (Nat.+-monoˡ-≤ (c * N+M ^ 2) (begin
          _                                     ≤⟨ drop-⊆-mono-≤ (sublist-join-flats preds preds′) e ⟩
          execTick (✓ drop (preds ++ preds′) e) ≤⟨ drop-leq ⟩
          _                                     ∎)) ⟩
      2 + c₀/drop * length (preds ++ preds′) + c * (N + M) ^ 2
    ≤⟨ Nat.+-monoʳ-≤ 2 (Nat.+-monoˡ-≤ (c * N+M ^ 2) (Nat.*-monoˡ-≤ _ (join-flats-c₀-≤-trans c₀≤c))) ⟩
      2 + c * length (preds ++ preds′) + c * (N + M) ^ 2
    ≡⟨ cong (λ X → 2 + c * X + c * (N + M) ^ 2) (List.length-++ preds) ⟩
      2 + c * (N + M) + c * (N + M) ^ 2
    ≡⟨⟩
      2 + c * N+M + c * N+M ^ 2
    ≤⟨ Nat.+-monoˡ-≤ (c * N+M ^ 2) (Nat.+-monoˡ-≤ (c * N+M) 2≤c₀≤c) ⟩
      c + c * N+M + c * N+M ^ 2
    ≡⟨ cong (λ X → X + c * N+M + c * N+M ^ 2) (Nat.*-identityʳ c) ⟨
      c * 1 + c * N+M + c * N+M ^ 2
    ≡⟨ trans (Nat.*-distribˡ-+ c (1 + N+M) (N+M ^ 2)) (cong (_+ c * N+M ^ 2) (Nat.*-distribˡ-+ c 1 N+M)) ⟨
      c * (1 + N+M + N+M ^ 2)
    ≤⟨ Nat.*-monoʳ-≤ c (Nat.+-monoˡ-≤ (N+M ^ 2) (Nat.+-monoʳ-≤ (1 ^ 2) (Nat.m≤m+n N+M (N+M + 0)))) ⟩
      c * (1 + 2 * N+M + N+M ^ 2)
    ≡⟨ cong (λ X → c * (1 + 2 * X + N+M ^ 2)) (Nat.*-identityˡ N+M) ⟨
      c * (1 + 2 * (1 * N+M) + N+M ^ 2)
    ≡⟨ cong (c *_) ([m+n]²≡m²+2mn+n² 1 N+M) ⟨
      c * 1+N+Mʳ ^ 2
    ≡⟨ cong (λ X → c * X ^ 2) (Nat.+-assoc 1 N M) ⟨
      c * (1 + N + M) ^ 2 ∎
    where open ≤-Reasoning
          open RawMonad {f = lzero} monad

          N = length preds
          M = length preds′

          N+M = N + M
          1+N+Mʳ = 1 + (N + M)

          2≤c₀≤c : 2 ≤ c
          2≤c₀≤c = ≤-trans (Nat.m≤m+n 2 _) c₀≤c

          len₀/drop = Δ→len₀/drop Δ

          len₀/drop≤preds++preds′ : len₀/drop ≤ length (preds ++ preds′)
          len₀/drop≤preds++preds′ = begin
              len₀/drop
            ≤⟨ ≤-trans (Nat.m≤n⊔m 1 len₀/drop) preds′-geq ⟩
              M
            ≤⟨ Nat.m≤n+m M N ⟩
              N + M
            ≡⟨ List.length-++ preds ⟨
              length (preds ++ preds′) ∎

          drop-leq : execTick (✓ drop (preds ++ preds′) e) ≤ c₀/drop * length (preds ++ preds′)
          drop-leq = 𝕌.ultimately drop-linear (e , Δ , preds ++ preds′) (tt , len₀/drop≤preds++preds′)

  join-flats-is-quadratic : JoinFlatsQuadraticSpec
  join-flats-is-quadratic =
    make𝕌 $′ λ c c₀≤c →
    make𝕌 $′ λ where
      (Δ , preds , preds′) (preds-geq , preds′-geq) →
        join-flats-quadratic-ind c c₀≤c preds preds-geq preds′ preds′-geq

-- The modular spec approach is causing trouble with the constants
-- over the polymorphic filter! (i.e. ∀ Δ → RawFilter (ListLenᶠ* (SCtc1N Δ `ℕ)))
module join-expquad (join-flats-quadratic-spec/unused : JoinFlatsQuadraticSpec) where

  open join-flats-quadratic drop-is-linear using (join-flats-is-quadratic)
  join-flats-quadratic-spec = join-flats-is-quadratic

  c₀/join-flats = 𝕌.base join-flats-quadratic-spec
  join-flats-quadratic = 𝕌.ultimately join-flats-quadratic-spec _ ≤-refl

  c₁      : ℕ
  2≤c₁    : 2 ≤ c₁
  b       : ℕ
  2≤b     : 2 ≤ b

  join-exp-ind-bound : ∀ (c U h : ℕ) → ℕ
  join-exp-ind-bound c U h = c * U ^ 2 * 2 ^ h + b * (∑[ i < h ] 2 ^ i)

  join-base-c₀ = c₁ + c₀/join-flats * 4
  join-c₀ = join-base-c₀ + b * 2

  2≤join-base-c₀ : 2 ≤ join-base-c₀
  2≤join-base-c₀ = ≤-trans 2≤c₁ (Nat.m≤m+n c₁ (c₀/join-flats * 4))

  2≤join-c₀ : 2 ≤ join-c₀
  2≤join-c₀ = begin
    2                    ≡⟨⟩
    2 * 1                ≤⟨ Nat.*-mono-≤ 2≤b (s≤s (z≤n {1})) ⟩
    b * 2                ≤⟨ Nat.m≤n+m (b * 2) join-base-c₀ ⟩
    join-base-c₀ + b * 2 ≡⟨⟩
    join-c₀              ∎ where open ≤-Reasoning

  c₁ = 2
  2≤c₁ = s≤s (s≤s z≤n)
  b = 2
  2≤b = ≤-refl

  join-exp-base :
    ∀ c (_ : join-base-c₀ ≤ c) →
    ∀ U (_ : 1 ≤ U) →
    ∀ (_ : SECtcMaxH cκ 0)
      (_ : SECtcPreds (inRange 1 U ∘′ length) cκ) →
    ∀ (_ : SECtcMaxH cκ′ 0)
      (_ : SECtcPreds (inRange 1 U ∘′ length) cκ′) →
    execTick (✓ join cκ cκ′) ≤ c * (U ^ 2)
  join-exp-base c c₀≤c U 1≤U (` a)  cps-len (` a)  cps-len′ = Nat.*-mono-≤ 2≤c₀≤c 1²≤U²
    where 2≤c₀≤c = ≤-trans 2≤join-base-c₀ c₀≤c; 1²≤U²  = Nat.^-monoˡ-≤ 2 1≤U
  join-exp-base c c₀≤c U 1≤U 1/h    cps-len 1/h    cps-len′ = Nat.*-mono-≤ 2≤c₀≤c 1²≤U²
    where 2≤c₀≤c = ≤-trans 2≤join-base-c₀ c₀≤c; 1²≤U²  = Nat.^-monoˡ-≤ 2 1≤U
  join-exp-base c c₀≤c U 1≤U
    flat/h (flat/ps {preds = preds}  cps-len)
    flat/h (flat/ps {preds = preds′} cps-len′) = begin
        1 + (execTick (✓ join-flats preds preds′) + 1)
      ≡⟨ cong (1 +_) (Nat.+-comm _ 1) ⟩
        2 + execTick (✓ join-flats preds preds′)
      ≤⟨ Nat.+-monoʳ-≤ 2 join-leq ⟩
        2 + c₀/join-flats * (length preds + length preds′) ^ 2
      ≤⟨ Nat.+-monoʳ-≤ 2
          (Nat.*-monoʳ-≤ c₀/join-flats
            (Nat.^-monoˡ-≤ 2
              (Nat.+-mono-≤ |preds|≤U |preds′|≤U))) ⟩
        2 + c₀/join-flats * (U + U) ^ 2
      ≡⟨ cong ((2 +_) ∘′ (c₀/join-flats *_)) (EQR.begin
            (U + U) ^ 2 EQR.≡⟨ cong ((_^ 2) ∘′ (U +_)) (Nat.*-identityˡ U) ⟨
            (2 * U) ^ 2 EQR.≡⟨ ^-distribʳ-* 2 U 2 ⟩
            4 * U²   EQR.∎) ⟩
        2 + c₀/join-flats * (4 * U²)
      ≡⟨ cong (2 +_) (Nat.*-assoc c₀/join-flats 4 U²) ⟨
        2 + (c₀/join-flats * 4) * U²
      ≡⟨ cong (_+ (c₀/join-flats * 4) * U²) (Nat.*-identityʳ 2) ⟨
        2 * 1 + (c₀/join-flats * 4) * U²
      ≤⟨ Nat.+-monoˡ-≤ ((c₀/join-flats * 4) * U²) (Nat.*-mono-≤ 2≤c₁ 1²≤U²) ⟩
        c₁ * U² + (c₀/join-flats * 4) * U²
      ≡⟨ Nat.*-distribʳ-+ U² c₁ (c₀/join-flats * 4) ⟨
        (c₁ + c₀/join-flats * 4) * U²
      ≤⟨ Nat.*-monoˡ-≤ U² c₀≤c ⟩
        c * U² ∎
      where open ≤-Reasoning
            module EQR = ≡-Reasoning

            U² = U ^ 2

            1²≤U² = Nat.^-monoˡ-≤ 2 1≤U

            1≤|preds|  = subst (1 ≤_) (List.length-map flat-pred preds)  (proj₁ cps-len)
            1≤|preds′| = subst (1 ≤_) (List.length-map flat-pred preds′) (proj₁ cps-len′)
            |preds|≤U  = subst (_≤ U) (List.length-map flat-pred preds)  (proj₂ cps-len)
            |preds′|≤U = subst (_≤ U) (List.length-map flat-pred preds′) (proj₂ cps-len′)

            join-leq : execTick (✓ join-flats preds preds′) ≤
                        c₀/join-flats * (length preds + length preds′) ^ 2
            join-leq = 𝕌.ultimately join-flats-quadratic (_ , preds ,′ preds′)
                          (1≤|preds| , 1≤|preds′|)

  join-exp-ind-case-base : ∀ c U h →
    c * U ^ 2 ≤ join-exp-ind-bound c U h
  join-exp-ind-case-base c U h = begin
    c * U²          ≡⟨ Nat.*-identityʳ _ ⟨
    c * U² * 1      ≤⟨ Nat.*-monoʳ-≤ (c * U²) 1≤2ʰ ⟩
    c * U² * 2ʰ     ≤⟨ Nat.m≤m+n (c * U² * 2ʰ) _ ⟩
    join-exp-ind-bound c U h ∎
    where open ≤-Reasoning
          2ʰ   = 2 ^ h
          U²   = U ^ 2
          1≤2ʰ : 1 ≤ 2ʰ
          1≤2ʰ = Nat.^-monoʳ-≤ 2 (z≤n {h})

  join-exp-ind-case-one : ∀ c U h →
    join-exp-ind-bound c U h + 2 ≤ join-exp-ind-bound c U (suc h)
  join-exp-ind-case-one c U h = begin
    join-exp-ind-bound c U h + 2                      ≡⟨ Nat.+-assoc (c * U² * 2ʰ) _ 2 ⟩
    c * U² * 2ʰ + (b * ∑ᵢ2ⁱ + 2)
      ≤⟨ Nat.+-monoˡ-≤ _ (Nat.*-monoʳ-≤ (c * U²) (Nat.^-monoʳ-≤ 2 (Nat.n≤1+n h))) ⟩
    c * U² * (2 ^ suc h) + (b * ∑ᵢ2ⁱ + 2)             ≡⟨ cong (c * U² * (2 ^ suc h) +_) (Nat.+-comm _ 2) ⟩
    c * U² * (2 ^ suc h) + (2 + b * ∑ᵢ2ⁱ)
      ≤⟨ Nat.+-monoʳ-≤ (c * U² * (2 ^ suc h)) (Nat.+-monoˡ-≤ (b * ∑ᵢ2ⁱ)
          (Nat.*-mono-≤ 2≤b (s≤s (z≤n {0})))) ⟩
    c * U² * (2 ^ suc h) + (b * 1 + b * ∑ᵢ2ⁱ)
      ≡⟨ cong (c * U² * (2 ^ suc h) +_) (Nat.*-distribˡ-+ b 1 ∑ᵢ2ⁱ) ⟨
    c * U² * (2 ^ suc h) + b * (1 + ∑ᵢ2ⁱ)
      ≤⟨ Nat.+-monoʳ-≤ (c * U² * (2 ^ suc h)) (Nat.*-monoʳ-≤ b (Nat.+-monoˡ-≤ ∑ᵢ2ⁱ
          1≤2ʰ)) ⟩
    c * U² * (2 ^ suc h) + b * (2ʰ + ∑ᵢ2ⁱ)            ≡⟨⟩
    c * U² * (2 ^ suc h) + b * (∑[ i < suc h ] 2 ^ i) ≡⟨⟩
    join-exp-ind-bound c U (suc h)                    ∎
    where open ≤-Reasoning
          2ʰ   = 2 ^ h
          U²   = U ^ 2
          1≤2ʰ : 1 ≤ 2ʰ
          1≤2ʰ = Nat.^-monoʳ-≤ 2 (z≤n {h})
          ∑ᵢ2ⁱ = ∑[ i < h ] 2 ^ i

  join-exp-ind-case-two : ∀ c U h →
    2 + (join-exp-ind-bound c U h + join-exp-ind-bound c U h) ≤ join-exp-ind-bound c U (suc h)
  join-exp-ind-case-two c U h = begin
    2 + (join-exp-ind-bound c U h + join-exp-ind-bound c U h)
      ≡⟨ cong (2 +_) (m+m≡2m (join-exp-ind-bound c U h)) ⟩
    2 + 2 * join-exp-ind-bound c U h                  ≡⟨ Nat.+-comm 2 _ ⟩
    2 * join-exp-ind-bound c U h + 2                  ≡⟨⟩
    2 * (c * U² * 2ʰ + b * ∑ᵢ2ⁱ) + 2                  ≤⟨ Nat.+-monoʳ-≤ _ 2≤b ⟩
    2 * (c * U² * 2ʰ + b * ∑ᵢ2ⁱ) + b                  ≤⟨ geometry-sum _ (c * U²) 2 b h ≤-refl ⟩
    c * U² * (2 ^ suc h) + b * (∑[ i < suc h ] 2 ^ i) ≡⟨⟩
    join-exp-ind-bound c U (suc h)                    ∎
    where open ≤-Reasoning
          2ʰ   = 2 ^ h
          U²   = U ^ 2
          ∑ᵢ2ⁱ = ∑[ i < h ] 2 ^ i

  join-exp-ind :
    ∀ c (_ : join-base-c₀ ≤ c) →
    ∀ U (_ : 1 ≤ U) →
    ∀ (_ : SECtcMaxH cκ  h)
      (_ : SECtcPreds (inRange 1 U ∘′ length) cκ) →
    ∀ (_ : SECtcMaxH cκ′ h)
      (_ : SECtcPreds (inRange 1 U ∘′ length) cκ′) →
    execTick (✓ join cκ cκ′) ≤ join-exp-ind-bound c U h
  join-exp-ind {cκ = cκ} {h = h} {cκ′ = cκ′} c c₀≤c U 1≤U (` a) cps-len (` a) cps-len′ = begin
    execTick (✓ join cκ cκ′)  ≤⟨ join-exp-base c c₀≤c U 1≤U (` a) cps-len (` a) cps-len′ ⟩
    _                         ≤⟨ join-exp-ind-case-base c U h ⟩
    join-exp-ind-bound c U h  ∎ where open ≤-Reasoning
  join-exp-ind {cκ = cκ} {h = h} {cκ′ = cκ′} c c₀≤c U 1≤U 1/h cps-len 1/h cps-len′ = begin
    execTick (✓ join cκ cκ′)  ≤⟨ join-exp-base c c₀≤c U 1≤U 1/h cps-len 1/h cps-len′ ⟩
    _                         ≤⟨ join-exp-ind-case-base c U h ⟩
    join-exp-ind-bound c U h  ∎ where open ≤-Reasoning
  join-exp-ind {cκ = cκ} {h = h} {cκ′ = cκ′} c c₀≤c U 1≤U flat/h cps-len flat/h cps-len′ = begin
    execTick (✓ join cκ cκ′)  ≤⟨ join-exp-base c c₀≤c U 1≤U flat/h cps-len flat/h cps-len′ ⟩
    _                         ≤⟨ join-exp-ind-case-base c U h ⟩
    join-exp-ind-bound c U h  ∎ where open ≤-Reasoning
  join-exp-ind {cκ = cκ₁ */cc cκ₂} {h = suc h} {cκ′ = cκ₁′ */cc cκ₂′} c c₀≤c U 1≤U
    (cmh₁ */h cmh₂) cps-len (cmh₁′ */h cmh₂′) cps-len′
    = begin
        1 + execTick (do cκ ← ✓ join cκ₁ cκ₁′; cκ′ ← ✓ join cκ₂ cκ₂′; ✓ return (cκ */cc cκ′))
      ≡⟨⟩
        1 + (execTick (✓ join cκ₁ cκ₁′) + (execTick (✓ join cκ₂ cκ₂′) + 1))
      ≡⟨ 1+[m+[n+1]]≡2+[m+n] (execTick (✓ join cκ₁ cκ₁′)) (execTick (✓ join cκ₂ cκ₂′)) ⟩
        2 + (execTick (✓ join cκ₁ cκ₁′) + execTick (✓ join cκ₂ cκ₂′))
      ≤⟨ Nat.+-monoʳ-≤ 2 (begin
          _ ≤⟨ Nat.+-monoˡ-≤ _
                (join-exp-ind c c₀≤c U 1≤U cmh₁ (cps-*₁ cps-len) cmh₁′ (cps-*₁ cps-len′)) ⟩
          _ ≤⟨ Nat.+-monoʳ-≤ _
                (join-exp-ind c c₀≤c U 1≤U cmh₂ (cps-*₂ cps-len) cmh₂′ (cps-*₂ cps-len′)) ⟩
          _ ∎) ⟩
        2 + (join-exp-ind-bound c U h + join-exp-ind-bound c U h)
      ≤⟨ join-exp-ind-case-two c U h ⟩
        join-exp-ind-bound c U (suc h) ∎
      where open ≤-Reasoning; open RawMonad {f = lzero} monad
  join-exp-ind {cκ = cκ₁ +/cc cκ₂} {h = suc h} {cκ′ = cκ₁′ +/cc cκ₂′} c c₀≤c U 1≤U
    (cmh₁ +/h cmh₂) cps-len (cmh₁′ +/h cmh₂′) cps-len′
    = begin
        1 + execTick (do cκ ← ✓ join cκ₁ cκ₁′; cκ′ ← ✓ join cκ₂ cκ₂′; ✓ return (cκ +/cc cκ′))
      ≡⟨⟩
        1 + (execTick (✓ join cκ₁ cκ₁′) + (execTick (✓ join cκ₂ cκ₂′) + 1))
      ≡⟨ 1+[m+[n+1]]≡2+[m+n] (execTick (✓ join cκ₁ cκ₁′)) (execTick (✓ join cκ₂ cκ₂′)) ⟩
        2 + (execTick (✓ join cκ₁ cκ₁′) + execTick (✓ join cκ₂ cκ₂′))
      ≤⟨ Nat.+-monoʳ-≤ 2 (begin
          _ ≤⟨ Nat.+-monoˡ-≤ _
                (join-exp-ind c c₀≤c U 1≤U cmh₁ (cps-+₁ cps-len) cmh₁′ (cps-+₁ cps-len′)) ⟩
          _ ≤⟨ Nat.+-monoʳ-≤ _
                (join-exp-ind c c₀≤c U 1≤U cmh₂ (cps-+₂ cps-len) cmh₂′ (cps-+₂ cps-len′)) ⟩
          _ ∎) ⟩
        2 + (join-exp-ind-bound c U h + join-exp-ind-bound c U h)
      ≤⟨ join-exp-ind-case-two c U h ⟩
        join-exp-ind-bound c U (suc h) ∎
      where open ≤-Reasoning; open RawMonad {f = lzero} monad
  join-exp-ind {cκ = box/cc cκ} {h = suc h} {cκ′ = box/cc cκ′} c c₀≤c U 1≤U
    (box/h cmh) cps-len (box/h cmh′) cps-len′
    = begin
        1 + execTick (do cκ″ ← ✓ join cκ cκ′; ✓ return (box/cc cκ″))
      ≡⟨⟩
        1 + (execTick (✓ join cκ cκ′) + 1)
      ≡⟨ Nat.+-suc (execTick (✓ join cκ cκ′)) 1 ⟨
        execTick (✓ join cκ cκ′) + 2
      ≤⟨ Nat.+-monoˡ-≤ 2
          (join-exp-ind c c₀≤c U 1≤U cmh (cps-box cps-len) cmh′ (cps-box cps-len′)) ⟩
        join-exp-ind-bound c U h + 2
      ≤⟨ join-exp-ind-case-one c U h ⟩
        join-exp-ind-bound c U (suc h) ∎
      where open ≤-Reasoning; open RawMonad {f = lzero} monad
  join-exp-ind {cκ = cκₐ →/cc cκᵣ} {h = suc h} {cκ′ = cκₐ′ →/cc cκᵣ′} c c₀≤c U 1≤U
    (cmhₐ →/h cmhᵣ) cps-len (cmhₐ′ →/h cmhᵣ′) cps-len′
    = begin
        1 + execTick (do cκ ← ✓ join cκₐ′ cκₐ; cκ′ ← ✓ join cκᵣ cκᵣ′; ✓ return (cκ →/cc cκ′))
      ≡⟨⟩
        1 + (execTick (✓ join cκₐ′ cκₐ) + (execTick (✓ join cκᵣ cκᵣ′) + 1))
      ≡⟨ 1+[m+[n+1]]≡2+[m+n] (execTick (✓ join cκₐ′ cκₐ)) (execTick (✓ join cκᵣ cκᵣ′)) ⟩
        2 + (execTick (✓ join cκₐ′ cκₐ) + execTick (✓ join cκᵣ cκᵣ′))
      ≤⟨ Nat.+-monoʳ-≤ 2 (begin
          _ ≤⟨ Nat.+-monoˡ-≤ _
                (join-exp-ind c c₀≤c U 1≤U cmhₐ′ (cps-dom cps-len′) cmhₐ (cps-dom cps-len)) ⟩
          _ ≤⟨ Nat.+-monoʳ-≤ _
                (join-exp-ind c c₀≤c U 1≤U cmhᵣ (cps-rng cps-len) cmhᵣ′ (cps-rng cps-len′)) ⟩
          _ ∎) ⟩
        2 + (join-exp-ind-bound c U h + join-exp-ind-bound c U h)
      ≤⟨ join-exp-ind-case-two c U h ⟩
        join-exp-ind-bound c U (suc h) ∎
      where open ≤-Reasoning; open RawMonad {f = lzero} monad
  join-exp-ind {cκ = μ/cc cκ} {h = suc h} {cκ′ = μ/cc cκ′} c c₀≤c U 1≤U
    (μ/h cmh) cps-len (μ/h cmh′) cps-len′
    = begin
        1 + execTick (do cκ″ ← ✓ join cκ cκ′; ✓ return (μ/cc cκ″))
      ≡⟨⟩
        1 + (execTick (✓ join cκ cκ′) + 1)
      ≡⟨ Nat.+-suc (execTick (✓ join cκ cκ′)) 1 ⟨
        execTick (✓ join cκ cκ′) + 2
      ≤⟨ Nat.+-monoˡ-≤ 2 (join-exp-ind c c₀≤c U 1≤U cmh (cps-μ′ cps-len) cmh′ (cps-μ′ cps-len′)) ⟩
        join-exp-ind-bound c U h + 2
      ≤⟨ join-exp-ind-case-one c U h ⟩
        join-exp-ind-bound c U (suc h) ∎
      where open ≤-Reasoning; open RawMonad {f = lzero} monad

  join-exp-expquad :
    ∀ c (_ : join-c₀ ≤ c) →
    ∀ U (_ : 1 ≤ U) →
    ∀ (_ : SECtcMaxH cκ  h)
      (_ : SECtcPreds (inRange 1 U ∘′ length) cκ) →
    ∀ (_ : SECtcMaxH cκ′ h)
      (_ : SECtcPreds (inRange 1 U ∘′ length) cκ′) →
    execTick (✓ join cκ cκ′) ≤ c * U ^ 2 * 2 ^ h
  join-exp-expquad {cκ = cκ} {h} {cκ′} c c₀≤c U 1≤U cmh cps-len cmh′ cps-len′ = begin
    execTick (✓ join cκ cκ′)
      ≤⟨ join-exp-ind join-base-c₀ ≤-refl U 1≤U cmh cps-len cmh′ cps-len′ ⟩
    join-exp-ind-bound join-base-c₀ U h  ≡⟨⟩
    join-base-c₀ * U² * 2ʰ + b * ∑ᵢ2ⁱ
      ≤⟨ Nat.+-monoʳ-≤ (join-base-c₀ * U² * 2ʰ) (begin
            b * ∑ᵢ2ⁱ            ≤⟨ Nat.*-monoʳ-≤ b (∑-^-≤-^ h 2 ≤-refl) ⟩
            b * (2 ^ suc h)     ≡⟨ Nat.*-assoc b 2 2ʰ ⟨
            (b * 2) * 2ʰ        ≡⟨ cong (b * 2 *_) (Nat.*-identityˡ 2ʰ) ⟨
            (b * 2) * (1 * 2ʰ)  ≤⟨ Nat.*-monoʳ-≤ (b * 2) (Nat.*-monoˡ-≤ 2ʰ 1²≤U²) ⟩
            (b * 2) * (U² * 2ʰ) ∎) ⟩
    join-base-c₀ * U² * 2ʰ   + (b * 2) * (U² * 2ʰ)
      ≡⟨ cong (_+ (b * 2) * (U² * 2ʰ)) (Nat.*-assoc join-base-c₀ U² 2ʰ) ⟩
    join-base-c₀ * (U² * 2ʰ) + (b * 2) * (U² * 2ʰ) ≡⟨ Nat.*-distribʳ-+ (U² * 2ʰ) join-base-c₀ (b * 2) ⟨
    (join-base-c₀ + b * 2) * (U² * 2ʰ)             ≤⟨ Nat.*-monoˡ-≤ (U² * 2ʰ) c₀≤c ⟩
    c * (U² * 2ʰ)                                  ≡⟨ Nat.*-assoc c U² 2ʰ ⟨
    c * U² * 2ʰ ∎
    where open ≤-Reasoning
          2ʰ    = 2 ^ h
          U²    = U ^ 2
          ∑ᵢ2ⁱ  = ∑[ i < h ] 2 ^ i

          1²≤U² = Nat.^-monoˡ-≤ 2 1≤U

  -- This can be proven by combining SpaceEfficient.Properties.Size.sectc→cps-leaf-size
  -- with a few abstractions (e.g. cps-map₂ and cps-inRange-weaken)
  nonempty∧leaf-size⇒sectc-preds :
    SECtcPreds ((1 ≤_) ∘′ length) cκ →
    SECtcPreds (inRange 1 (leaf-size cκ ⊔ 1) ∘′ length) cκ
  nonempty∧leaf-size⇒sectc-preds (` a)                  = ` a
  nonempty∧leaf-size⇒sectc-preds 1/ps                   = 1/ps
  nonempty∧leaf-size⇒sectc-preds (flat/ps {preds = preds} 1≤len) =
    flat/ps ( 1≤len ,′
              ≤-trans (Nat.≤-reflexive (List.length-map flat-pred preds)) (Nat.m≤m⊔n (length preds) 1) )
  nonempty∧leaf-size⇒sectc-preds {cκ = cκ₁ */cc cκ₂} (cps-ne₁ */ps cps-ne₂) =
    (cps-inRange-weaken ≤-refl
                        (m⊔1≤m⊔n⊔1 (leaf-size cκ₁) (leaf-size cκ₂))
                        (nonempty∧leaf-size⇒sectc-preds cps-ne₁))
    */ps
    (cps-inRange-weaken ≤-refl
                        (m⊔1≤n⊔m⊔1 (leaf-size cκ₂) (leaf-size cκ₁))
                        (nonempty∧leaf-size⇒sectc-preds cps-ne₂))
  nonempty∧leaf-size⇒sectc-preds {cκ = cκ₁ +/cc cκ₂} (cps-ne₁ +/ps cps-ne₂) =
    (cps-inRange-weaken ≤-refl
                        (m⊔1≤m⊔n⊔1 (leaf-size cκ₁) (leaf-size cκ₂))
                        (nonempty∧leaf-size⇒sectc-preds cps-ne₁))
    +/ps
    (cps-inRange-weaken ≤-refl
                        (m⊔1≤n⊔m⊔1 (leaf-size cκ₂) (leaf-size cκ₁))
                        (nonempty∧leaf-size⇒sectc-preds cps-ne₂))
  nonempty∧leaf-size⇒sectc-preds (box/ps cps-ne)        =
    box/ps (nonempty∧leaf-size⇒sectc-preds cps-ne)
  nonempty∧leaf-size⇒sectc-preds {cκ = cκₐ →/cc cκᵣ} (cps-neₐ →/ps cps-neᵣ) =
    (cps-inRange-weaken ≤-refl
                        (m⊔1≤m⊔n⊔1 (leaf-size cκₐ) (leaf-size cκᵣ))
                        (nonempty∧leaf-size⇒sectc-preds cps-neₐ))
    →/ps
    (cps-inRange-weaken ≤-refl
                        (m⊔1≤n⊔m⊔1 (leaf-size cκᵣ) (leaf-size cκₐ))
                        (nonempty∧leaf-size⇒sectc-preds cps-neᵣ))
  nonempty∧leaf-size⇒sectc-preds (μ/ps cps-ne)          =
    μ/ps (nonempty∧leaf-size⇒sectc-preds cps-ne)

  join-is-exp-quadratic : JoinExpQuadraticSpec
  join-is-exp-quadratic =
    make𝕌 $′ λ c c₀≤c →
    make𝕌 $′ λ where
      (Δ , τ , cκ , cκ′) (cps-ne , cps-ne′) →
        let U = leaf-size cκ ⊔ leaf-size cκ′ ⊔ 1
            h = sectc-height cκ ⊔ sectc-height cκ′
        in begin
          execTick (✓ join cκ cκ′)
        ≤⟨ join-exp-expquad c c₀≤c
                            U (Nat.m≤n⊔m _ 1)
                            (cmh-weaken (Nat.m≤m⊔n (sectc-height cκ) (sectc-height cκ′)) (sectc→cmh cκ))
                            (cps-inRange-weaken ≤-refl
                                                (m⊔1≤m⊔n⊔1 (leaf-size cκ) (leaf-size cκ′))
                                                (nonempty∧leaf-size⇒sectc-preds cps-ne))
                            (cmh-weaken (Nat.m≤n⊔m (sectc-height cκ) (sectc-height cκ′)) (sectc→cmh cκ′))
                            (cps-inRange-weaken ≤-refl
                                                (m⊔1≤n⊔m⊔1 (leaf-size cκ′) (leaf-size cκ))
                                                (nonempty∧leaf-size⇒sectc-preds cps-ne′)) ⟩
          c * (U ^ 2) * (2 ^ h)
        ≡⟨ Nat.*-assoc c (U ^ 2) (2 ^ h) ⟩
          c * ((U ^ 2) * (2 ^ h))
        ∎
    where open ≤-Reasoning
