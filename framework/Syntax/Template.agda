{-# OPTIONS --without-K --safe #-}

module Syntax.Template where

open import Syntax.Type
open import Syntax.Term

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

infix 60 #_

AnnEnv : (Ann : AnnSig) → List Ty → Set
AnnEnv Ann Ψ = ∀ {τ} → τ ∈ Ψ → Ann τ

MEnv : (Ann : AnnSig) (Δ : List (Ctxt × Ty)) → Set
MEnv Ann Δ = ∀ {x} → x ∈ Δ → Expr Ann x

record MetaVar (Ann : AnnSig) (Ψ : List Ty) (Δ : List (Ctxt × Ty)) : Set where
  inductive; no-eta-equality
  constructor mkMV
  field
    annEnvᵗ : AnnEnv Ann Ψ
    termEnvᵗ : MEnv Ann Δ
open MetaVar public

mutual
  syntax ismonctorofᵗ Ann Ψ Δ τ eᵗ = Ann ⨟ Ψ ⨟ Δ ∣ eᵗ ismonctorofᵗ τ

  data _⨟_⨟_∣_⊢_ Ann Ψ Δ : (Γ : Ctxt) → (τ : Ty) → Set where
    #_ : (y : (Γ ,′ τ) ∈ Δ) →
         -------------------
         Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    proxy/t : (a : τ ∈ Ψ) →
              ∀ eᵗ →
              (emᵗ : Ann ⨟ Ψ ⨟ Δ ∣ eᵗ ismonctorofᵗ τ) →
              Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    B#_⟪_⟫ : (a : τ ∈ Ψ) →
             Ann ⨟ Ψ ⨟ Δ ∣ [] ⊢ τ →
             --------------------
             Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    ⋆ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `1

    `z : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ

    `s : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ →
         --------------------
         Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ

    foldN : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ →
            Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ →
            Ann ⨟ Ψ ⨟ Δ ∣ (`ℕ ∷ τ ∷ Γ) ⊢ τ →
            ------------------------------
            Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    assert : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ →
             --------------------
             Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `1

    _`,_ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁ →
           Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₂ →
           ----------------------------
           Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `* τ₂)

    π₁ :   Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `* τ₂) →
           ----------------------------
           Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁

    π₂ :   Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `* τ₂) →
           ----------------------------
           Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₂

    inl :        Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁ →
                 ----------------------------
                 Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `+ τ₂)

    inr :        Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₂ →
                 ----------------------------
                 Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `+ τ₂)

    case_of_∣_ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `+ τ₂) →
                 Ann ⨟ Ψ ⨟ Δ ∣ (τ₁ ∷ Γ) ⊢ τ →
                 Ann ⨟ Ψ ⨟ Δ ∣ (τ₂ ∷ Γ) ⊢ τ →
                 ----------------------------
                 Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    box :   Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ →
            -----------------------
            Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ Box τ

    unbox : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ Box τ →
            -----------------------
            Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    `_ :  (y : τ ∈ Γ) →
          --------------------
          Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    ƛ_ :  Ann ⨟ Ψ ⨟ Δ ∣ (τₐ ∷ Γ) ⊢ τᵣ →
          ----------------------------
          Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τₐ `→ τᵣ)

    _·_ : (e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τₐ `→ τᵣ) →
          (eₐ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τₐ) →
          --------------------------------
          Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τᵣ

    unroll : ∀ {τ} →
             Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ μ τ →
             -------------------------------------
             Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ tsubst τ [t0↦ μ τ ]

    roll :   ∀ τ →
             Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ tsubst τ [t0↦ μ τ ] →
             -------------------------------------
             Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ μ τ

    fix : Ann ⨟ Ψ ⨟ Δ ∣ (τ ∷ Γ) ⊢ τ →
          -------------------------
          Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ

    _⨟_ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ →
          Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁ →
          --------------------
          Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁

  data ismonctorofᵗ Ann Ψ Δ : (τ : Ty) → (Ann ⨟ Ψ ⨟ Δ ∣ [] ⊢ τ) → Set where
    box/m : ∀ eᵗ → ismonctorofᵗ Ann Ψ Δ (Box τ) (box eᵗ)
    ƛ/m_ : ∀ eᵗ → ismonctorofᵗ Ann Ψ Δ (τₐ `→ τᵣ) (ƛ eᵗ)

  esubstᵗ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ → MetaVar Ann Ψ Δ → Ann ∣ Γ ⊢ τ
  esubstᵗ (# y) ϑ = termEnvᵗ ϑ y
  esubstᵗ (B# a ⟪ e ⟫) ϑ = B# (annEnvᵗ ϑ a) ⟪ esubstᵗ e ϑ ⟫
  esubstᵗ (proxy/t a e emᵗ) ϑ = proxy (annEnvᵗ ϑ a) (monctorsubstᵗ emᵗ ϑ)
  esubstᵗ ⋆ ϑ = ⋆
  esubstᵗ `z ϑ = `z
  esubstᵗ (`s e) ϑ = `s (esubstᵗ e ϑ)
  esubstᵗ (foldN e ez es) ϑ = foldN (esubstᵗ e ϑ) (esubstᵗ ez ϑ) (esubstᵗ es ϑ)
  esubstᵗ (assert e) ϑ = assert (esubstᵗ e ϑ)
  esubstᵗ (e₁ `, e₂) ϑ = esubstᵗ e₁ ϑ `, esubstᵗ e₂ ϑ
  esubstᵗ (π₁ e) ϑ = π₁ (esubstᵗ e ϑ)
  esubstᵗ (π₂ e) ϑ = π₂ (esubstᵗ e ϑ)
  esubstᵗ (inl e) ϑ = inl (esubstᵗ e ϑ)
  esubstᵗ (inr e) ϑ = inr (esubstᵗ e ϑ)
  esubstᵗ (case e of e₁ ∣ e₂) ϑ = case esubstᵗ e ϑ of esubstᵗ e₁ ϑ ∣ esubstᵗ e₂ ϑ
  esubstᵗ (box v) ϑ = box (esubstᵗ v ϑ)
  esubstᵗ (unbox v) ϑ = unbox (esubstᵗ v ϑ)
  esubstᵗ (` y) ϑ = ` y
  esubstᵗ (ƛ e) ϑ = ƛ (esubstᵗ e ϑ)
  esubstᵗ (e · eₐ) ϑ = esubstᵗ e ϑ · esubstᵗ eₐ ϑ
  esubstᵗ (unroll e) ϑ = unroll (esubstᵗ e ϑ)
  esubstᵗ (roll τ e) ϑ = roll τ (esubstᵗ e ϑ)
  esubstᵗ (fix e) ϑ = fix (esubstᵗ e ϑ)
  esubstᵗ (e ⨟ e₁) ϑ = esubstᵗ e ϑ ⨟ esubstᵗ e₁ ϑ

  monctorsubstᵗ : ∀ {eᵗ} →
    Ann ⨟ Ψ ⨟ Δ ∣ eᵗ ismonctorofᵗ τ → (ϑ : MetaVar Ann Ψ Δ) → Ann ∣ (esubstᵗ eᵗ ϑ) ismonctorof τ
  monctorsubstᵗ (box/m eᵗ) ϑ = box/m (esubstᵗ eᵗ ϑ)
  monctorsubstᵗ (ƛ/m eᵗ) ϑ = ƛ/m (esubstᵗ eᵗ ϑ)


record TermTmpl Ann Δ τ : Set where
    inductive
    constructor mkTermTmpl
    field
      annCtxt : List Ty
      exprᵗ : Ann ⨟ annCtxt ⨟ Δ ∣ [] ⊢ τ
    TermTAnnEnv = AnnEnv Ann annCtxt
open TermTmpl public

record Term Ann {Δ} {τ}
  (termTmpl : TermTmpl Ann Δ τ)
  (termEnv : MEnv Ann Δ)
  (e : Ann ∣ [] ⊢ τ)
  : Set where
    inductive; no-eta-equality; pattern
    constructor mkTerm
    field anns : TermTAnnEnv termTmpl
    metaVars = mkMV anns termEnv
    substedExpr = esubstᵗ (exprᵗ termTmpl) metaVars

    field subst-eq : e ≡ substedExpr


record IsSatDownwardClosed {Ann Ψ Δ}
  (P : ∀ {Γ τ} → Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ → Set)
  : Set where
    field
      proxy↓ : ∀ {Γ} →
        {a : τ ∈ Ψ} →
        ∀ {eᵗ} {emᵗ : Ann ⨟ Ψ ⨟ Δ ∣ eᵗ ismonctorofᵗ τ} →
        P {Γ = Γ} (proxy/t a eᵗ emᵗ) →
        P eᵗ
      B↓ : ∀ {Γ} →
        {a : τ ∈ Ψ} →
        {e : Ann ⨟ Ψ ⨟ Δ ∣ [] ⊢ τ} →
        P {Γ = Γ} (B# a ⟪ e ⟫) →
        P e
      `s↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ} → P (`s e) → P e
      foldN↓ :
        {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ} →
        {ez : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ} →
        {es : Ann ⨟ Ψ ⨟ Δ ∣ (`ℕ ∷ τ ∷ Γ) ⊢ τ} →
        P (foldN e ez es) →
        P e × P ez × P es
      assert↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ `ℕ} → P (assert e) → P e
      cons↓ :
        {e₁ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁} →
        {e₂ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₂} →
        P (e₁ `, e₂) →
        P e₁ × P e₂
      π₁↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `* τ₂)} → P (π₁ e) → P e
      π₂↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `* τ₂)} → P (π₂ e) → P e
      inl↓ : ∀ {τ₁ τ₂} {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁} → P (inl {τ₁ = τ₁} {τ₂} e) → P e
      inr↓ : ∀ {τ₁ τ₂} {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₂} → P (inr {τ₂ = τ₂} {τ₁} e) → P e
      case↓ :
        {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ (τ₁ `+ τ₂)} →
        {e₁ : Ann ⨟ Ψ ⨟ Δ ∣ (τ₁ ∷ Γ) ⊢ τ} →
        {e₂ : Ann ⨟ Ψ ⨟ Δ ∣ (τ₂ ∷ Γ) ⊢ τ} →
        P (case e of e₁ ∣ e₂) →
        P e × P e₁ × P e₂
      box↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ} → P (box e) → P e
      unbox↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ Box τ} → P (unbox e) → P e
      ƛ↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ (τₐ ∷ Γ) ⊢ τᵣ} → P (ƛ e) → P e
      app↓ :
        {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τₐ `→ τᵣ} →
        {eₐ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τₐ} →
        P (e · eₐ) →
        P e × P eₐ
      unroll↓ : ∀ {τ} → {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ μ τ} → P (unroll e) → P e
      roll↓ : ∀ {τ} → {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ tsubst τ [t0↦ μ τ ]} → P (roll τ e) → P e
      fix↓ : {e : Ann ⨟ Ψ ⨟ Δ ∣ (τ ∷ Γ) ⊢ τ} → P (fix e) → P e
      seq↓ :
        {e : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ} →
        {e₁ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ₁} →
        P (e ⨟ e₁) →
        P e × P e₁

trivialIsSatDownwardClosed : ∀ {Ann} → IsSatDownwardClosed {Ann} {Ψ} {Δ} (λ eᵗ → ⊤)
trivialIsSatDownwardClosed = record
  { proxy↓ = λ _ → tt
  ; B↓ = λ _ → tt
  ; `s↓ = λ _ → tt
  ; foldN↓ = λ _ → tt ,′ tt ,′ tt
  ; assert↓ = λ _ → tt
  ; cons↓ = λ _ → tt ,′ tt
  ; π₁↓ = λ _ → tt
  ; π₂↓ = λ _ → tt
  ; inl↓ = λ _ → tt
  ; inr↓ = λ _ → tt
  ; case↓ = λ _ → tt ,′ tt ,′ tt
  ; box↓ = λ _ → tt
  ; unbox↓ = λ _ → tt
  ; ƛ↓ = λ _ → tt
  ; app↓ = λ _ → tt ,′ tt
  ; unroll↓ = λ _ → tt
  ; roll↓ = λ _ → tt
  ; fix↓ = λ _ → tt
  ; seq↓ = λ _ → tt ,′ tt
  }
