{-# OPTIONS --without-K --safe #-}

module Syntax.Term where

open import Syntax.Type

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Agda.Builtin.FromNat

private variable
  Ann : Ty → Set

  Γ Γ′ : Ctxt
  τ τ′ τₐ τᵣ τ₁ τ₂ : Ty

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

infix 60 `_
infixl 40 _·_
infixr 23 _`,_
infixr 20 _⨟_

infix 50 [x0↦_]
infix 50 [x0↦_&&x1↦_]

AnnSig : Set₁
AnnSig = Ty → Set

mutual
  Expr : (Ann : AnnSig) → Ctxt × Ty → Set
  Expr Ann (Γ , τ) = Ann ∣ Γ ⊢ τ

  syntax isval Ann τ v = Ann ∣ v isvalof τ
  syntax ismonctor Ann τ e = Ann ∣ e ismonctorof τ

  data _∣_⊢_ Ann : (Γ : Ctxt) → (τ : Ty) → Set where
      proxy  : ∀ {e} →
               (A : Ann τ) →
               (em : Ann ∣ e ismonctorof τ) →
               ----------------------------
               Ann ∣ Γ ⊢ τ

      B#_⟪_⟫ : (A : Ann τ) →
               Ann ∣ [] ⊢ τ →
               ------------
               Ann ∣ Γ ⊢ τ

      ⋆ : Ann ∣ Γ ⊢ `1

      `z : Ann ∣ Γ ⊢ `ℕ

      `s : Ann ∣ Γ ⊢ `ℕ →
           ------------
           Ann ∣ Γ ⊢ `ℕ

      foldN : Ann ∣ Γ ⊢ `ℕ →
              Ann ∣ Γ ⊢ τ →
              Ann ∣ (`ℕ ∷ τ ∷ Γ) ⊢ τ →
              ----------------------
              Ann ∣ Γ ⊢ τ

      assert : Ann ∣ Γ ⊢ `ℕ →
               ------------
               Ann ∣ Γ ⊢ `1

      _`,_ : Ann ∣ Γ ⊢ τ₁ →
             Ann ∣ Γ ⊢ τ₂ →
             --------------------
             Ann ∣ Γ ⊢ (τ₁ `* τ₂)

      π₁ :   Ann ∣ Γ ⊢ (τ₁ `* τ₂) →
             --------------------
             Ann ∣ Γ ⊢ τ₁

      π₂ :   Ann ∣ Γ ⊢ (τ₁ `* τ₂) →
             --------------------
             Ann ∣ Γ ⊢ τ₂

      inl :        Ann ∣ Γ ⊢ τ₁ →
                   --------------------
                   Ann ∣ Γ ⊢ (τ₁ `+ τ₂)

      inr :        Ann ∣ Γ ⊢ τ₂ →
                   --------------------
                   Ann ∣ Γ ⊢ (τ₁ `+ τ₂)

      case_of_∣_ : Ann ∣ Γ ⊢ (τ₁ `+ τ₂) →
                   Ann ∣ (τ₁ ∷ Γ) ⊢ τ →
                   Ann ∣ (τ₂ ∷ Γ) ⊢ τ →
                   --------------------
                   Ann ∣ Γ ⊢ τ

      box :   Ann ∣ Γ ⊢ τ →
              ---------------
              Ann ∣ Γ ⊢ Box τ

      unbox : Ann ∣ Γ ⊢ Box τ →
              ---------------
              Ann ∣ Γ ⊢ τ

      `_  : (y : τ ∈ Γ) →
            -------------
            Ann ∣ Γ ⊢ τ

      ƛ_  : Ann ∣ (τₐ ∷ Γ) ⊢ τᵣ →
            --------------------
            Ann ∣ Γ ⊢ (τₐ `→ τᵣ)

      _·_ : Ann ∣ Γ ⊢ (τₐ `→ τᵣ) →
            Ann ∣ Γ ⊢ τₐ →
            --------------------
            Ann ∣ Γ ⊢ τᵣ

      unroll : ∀ {τ} →
               Ann ∣ Γ ⊢ μ τ →
               --------------------
               Ann ∣ Γ ⊢ tsubst τ [t0↦ μ τ ]

      roll :   ∀ τ →
               Ann ∣ Γ ⊢ tsubst τ [t0↦ μ τ ] →
               -----------------------------
               Ann ∣ Γ ⊢ μ τ

      fix : Ann ∣ (τ ∷ Γ) ⊢ τ →
            -----------------
            Ann ∣ Γ ⊢ τ

      _⨟_ : Ann ∣ Γ ⊢ τ →
            Ann ∣ Γ ⊢ τ₁ →
            ------------
            Ann ∣ Γ ⊢ τ₁

  data ismonctor Ann : (τ : Ty) → (Ann ∣ [] ⊢ τ) → Set where
      box/m : ∀ e → ismonctor Ann (Box τ) (box e)
      ƛ/m_ : ∀ e → ismonctor Ann (τₐ `→ τᵣ) (ƛ e)

  data isval Ann : (τ : Ty) → (Ann ∣ [] ⊢ τ) → Set where
      proxy/v : ∀ {τ e} →
        (A : Ann τ) →
        (em : ismonctor Ann τ e) →
        isval Ann τ (proxy A em)

      ⋆/v :
        isval Ann `1 ⋆

      z/v :
        isval Ann `ℕ `z

      s/v : ∀ {n} →
        isval Ann `ℕ n →
        isval Ann `ℕ (`s n)

      _`,/v_ : ∀ {v₁ v₂} →
        isval Ann τ₁ v₁ →
        isval Ann τ₂ v₂ →
        isval Ann (τ₁ `* τ₂) (v₁ `, v₂)

      inl/v : ∀ {v} →
        isval Ann τ₁ v →
        isval Ann (τ₁ `+ τ₂) (inl v)

      inr/v : ∀ {v} →
        isval Ann τ₂ v →
        isval Ann (τ₁ `+ τ₂) (inr v)

      roll/v : ∀ {τ v} →
        isval Ann (tsubst τ [t0↦ μ τ ]) v →
        isval Ann (μ τ) (roll τ v)

      box/v : ∀ {v} →
        isval Ann τ v →
        isval Ann (Box τ) (box v)

      ƛ/v_ : ∀ e →
        isval Ann (τₐ `→ τᵣ) (ƛ e)

⌊_⌋m : ∀ {e} → Ann ∣ e ismonctorof τ  →  Ann ∣ [] ⊢ τ
⌊_⌋m {e = e} em = e

⌊_⌋v : ∀ {v} → Ann ∣ v isvalof τ  →  Ann ∣ [] ⊢ τ
⌊_⌋v {v = v} iv = v

`ℕfromNat : ℕ → Ann ∣ Γ ⊢ `ℕ
`ℕfromNat 0 = `z
`ℕfromNat (suc n) = `s (`ℕfromNat n)

instance
  NumTerm1 : Number (Ann ∣ Γ ⊢ `ℕ)
  NumTerm1 .Number.Constraint _ = ⊤
  NumTerm1 .Number.fromNat    n = `ℕfromNat n

x0mapsto [x0↦_] : Ann ∣ Γ ⊢ τ → ∀ {τ′} → τ′ ∈ (τ ∷ Γ) → Ann ∣ Γ ⊢ τ′
x0mapsto e (here refl)  = e
x0mapsto e (there τ′∈Γ) = ` τ′∈Γ
[x0↦_] = x0mapsto

x0x1mapsto [x0↦_&&x1↦_] :
  Ann ∣ Γ ⊢ τ →
  Ann ∣ Γ ⊢ τ′ →
  ∀ {τ″} → τ″ ∈ (τ ∷ τ′ ∷ Γ) → Ann ∣ Γ ⊢ τ″
x0x1mapsto e0 e1 (here refl) = e0
x0x1mapsto e0 e1 (there (here refl)) = e1
x0x1mapsto e0 e1 (there (there τ″∈Γ)) = ` τ″∈Γ
[x0↦_&&x1↦_] = x0x1mapsto

erename : Ann ∣ Γ ⊢ τ → (ren : ∀ {τ} → τ ∈ Γ → τ ∈ Γ′) → Ann ∣ Γ′ ⊢ τ
erename (B# A ⟪ e ⟫) ren = B# A ⟪ e ⟫
erename (proxy A em) ren = proxy A em
erename ⋆ ren = ⋆
erename `z ren = `z
erename (`s e) ren = `s (erename e ren)
erename (foldN e ez es) ren = foldN (erename e ren) (erename ez ren) (erename es (pext (pext ren)))
erename (assert e) ren = assert (erename e ren)
erename (e₁ `, e₂) ren = erename e₁ ren `, erename e₂ ren
erename (π₁ e) ren = π₁ (erename e ren)
erename (π₂ e) ren = π₂ (erename e ren)
erename (inl e) ren = inl (erename e ren)
erename (inr e) ren = inr (erename e ren)
erename (case e of e₁ ∣ e₂) ren = case erename e ren of erename e₁ (pext ren) ∣ erename e₂ (pext ren)
erename (box v) ren = box (erename v ren)
erename (unbox v) ren = unbox (erename v ren)
erename (` y) ren = ` (ren y)
erename (ƛ e) ren = ƛ (erename e (pext ren))
erename (e · eₐ) ren = erename e ren · erename eₐ ren
erename (unroll e) ren = unroll (erename e ren)
erename (roll τ e) ren = roll τ (erename e ren)
erename (fix e) ren = fix (erename e (pext ren))
erename (e ⨟ e₁) ren = erename e ren ⨟ erename e₁ ren

eext : (∀ {τ′} → τ′ ∈ Γ → Ann ∣ Γ′ ⊢ τ′) →
       ∀ {τ′} → τ′ ∈ τ ∷ Γ → Ann ∣ (τ ∷ Γ′) ⊢ τ′
eext σ (here refl) = ` here refl
eext σ (there τ∈Γ) = erename (σ τ∈Γ) there

esubst : Ann ∣ Γ ⊢ τ → (σ : ∀ {τ} → τ ∈ Γ → Ann ∣ Γ′ ⊢ τ) → Ann ∣ Γ′ ⊢ τ
esubst (B# A ⟪ e ⟫) σ = B# A ⟪ e ⟫
esubst (proxy A em) σ = proxy A em
esubst ⋆ σ = ⋆
esubst `z σ = `z
esubst (`s e) σ = `s (esubst e σ)
esubst (foldN e ez es) σ = foldN (esubst e σ) (esubst ez σ) (esubst es (eext (eext σ)))
esubst (assert e) σ = assert (esubst e σ)
esubst (e₁ `, e₂) σ = esubst e₁ σ `, esubst e₂ σ
esubst (π₁ e) σ = π₁ (esubst e σ)
esubst (π₂ e) σ = π₂ (esubst e σ)
esubst (inl e) σ = inl (esubst e σ)
esubst (inr e) σ = inr (esubst e σ)
esubst (case e of e₁ ∣ e₂) σ = case esubst e σ of esubst e₁ (eext σ) ∣ esubst e₂ (eext σ)
esubst (box v) σ = box (esubst v σ)
esubst (unbox v) σ = unbox (esubst v σ)
esubst (` y) σ = σ y
esubst (ƛ e) σ = ƛ (esubst e (eext σ))
esubst (e · eₐ) σ = esubst e σ · esubst eₐ σ
esubst (unroll e) σ = unroll (esubst e σ)
esubst (roll τ e) σ = roll τ (esubst e σ)
esubst (fix e) σ = fix (esubst e (eext σ))
esubst (e ⨟ e₁) σ = esubst e σ ⨟ esubst e₁ σ
