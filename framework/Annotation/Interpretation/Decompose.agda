{-# OPTIONS --without-K --no-infer-absurd-clauses --safe #-}

module Annotation.Interpretation.Decompose where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Interpretation.Base
open import Annotation.Interpretation.MetaVar

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; trans; subst; cong)

open import Function.Base using (const; id)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.Maybe.Base using (Maybe; nothing; just)

open import Data.List.Base using (List; []; _∷_; length; lookup)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ : Ty


SatIx⇒TermIx : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix ϑ mvix} →
    (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
    {esat : ℐ ⊨[ ix ] esubstᵗ eᵗ ϑ} →
    IsSatIx eᵗ (ix , esat) mvix ix →
    IsTermIx eᵗ tt mvix ix
SatIx⇒TermIx (# y) intrix rewrite intrix = id
SatIx⇒TermIx (proxy/t a e emᵗ) {proxy/i em ix ix′ ix◁ix′ psat esat} ((ix◁ctxt , refl) , intrix) =
  ix◁ctxt ,′ SatIx⇒TermIx e intrix
SatIx⇒TermIx (B# a ⟪ e ⟫) {B/i ix ix′ ix◁ix′ bsat esat} ((ix◁ctxt , refl) , intrix) =
  ix◁ctxt ,′ SatIx⇒TermIx e intrix
SatIx⇒TermIx ⋆ intrix = tt
SatIx⇒TermIx `z intrix = tt
SatIx⇒TermIx (`s e) {`s esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (foldN e ez es) {foldN esat ezsat essat} (intrix , intrixz , intrixs) =
  SatIx⇒TermIx e intrix ,′
  SatIx⇒TermIx ez intrixz ,′
  SatIx⇒TermIx es intrixs
SatIx⇒TermIx (assert e) {assert esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (e₁ `, e₂) {esat₁ `, esat₂} (intrix₁ , intrix₂) =
  SatIx⇒TermIx e₁ intrix₁ ,′
  SatIx⇒TermIx e₂ intrix₂
SatIx⇒TermIx (π₁ e) {π₁ esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (π₂ e) {π₂ esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (inl e) {inl esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (inr e) {inr esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (case e of e₁ ∣ e₂) {case esat of esat₁ ∣ esat₂} (intrix , intrix₁ , intrix₂) =
  SatIx⇒TermIx e intrix ,′
  SatIx⇒TermIx e₁ intrix₁ ,′
  SatIx⇒TermIx e₂ intrix₂
SatIx⇒TermIx (box e) {box esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (unbox e) {unbox esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (` y) intrix = tt
SatIx⇒TermIx (ƛ e) {ƛ esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (e · eₐ) {esat · esatₐ} (intrix , intrixₐ) =
  SatIx⇒TermIx e intrix ,′
  SatIx⇒TermIx eₐ intrixₐ
SatIx⇒TermIx (unroll e) {unroll esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (roll τ e) {roll .τ esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (fix e) {fix esat} intrix = SatIx⇒TermIx e intrix
SatIx⇒TermIx (e ⨟ e₁) {esat ⨟ esat₁} (intrix , intrix₁) =
  SatIx⇒TermIx e intrix ,′
  SatIx⇒TermIx e₁ intrix₁


⊨⇒BoundarySat : {ℐ : AnnIntr {𝒜} 𝒯} →
  (eᵗ : (ATAnn 𝒜) ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  ∀ {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} {ix} →
    {mvix : MetaVarIx ℐ ϑ} →
    (esat : ℐ ⊨[ ix ] esubstᵗ eᵗ ϑ) →
    IsSatIx eᵗ (ix , esat) mvix ix →
    BoundarySat eᵗ tt mvix ix
⊨⇒BoundarySat (# y) ℐ⊨e intrix = tt
⊨⇒BoundarySat (proxy/t a e emᵗ) (proxy/i em ix ix′ ix◁ix′ psat ℐ⊨e) ((refl , refl) , intrix) =
  (ix◁ix′ , psat) ,′
  ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (B# a ⟪ e ⟫) (B/i ix ix′ ix◁ix′ bsat ℐ⊨e) ((refl , refl) , intrix) =
  (ix◁ix′ , bsat) ,′
  ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat ⋆ ℐ⊨e intrix = tt
⊨⇒BoundarySat `z ℐ⊨e intrix = tt
⊨⇒BoundarySat (`s e) (`s ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (foldN e ez es) (foldN ℐ⊨e ℐ⊨ez ℐ⊨es) (intrix , intrixz , intrixs) =
  ⊨⇒BoundarySat e ℐ⊨e intrix ,′
  ⊨⇒BoundarySat ez ℐ⊨ez intrixz ,′
  ⊨⇒BoundarySat es ℐ⊨es intrixs
⊨⇒BoundarySat (assert e) (assert ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (e₁ `, e₂) (ℐ⊨e₁ `, ℐ⊨e₂) (intrix₁ , intrix₂) =
  ⊨⇒BoundarySat e₁ ℐ⊨e₁ intrix₁ ,′
  ⊨⇒BoundarySat e₂ ℐ⊨e₂ intrix₂
⊨⇒BoundarySat (π₁ e) (π₁ ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (π₂ e) (π₂ ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (inl e) (inl ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (inr e) (inr ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (case e of e₁ ∣ e₂) (case ℐ⊨e of ℐ⊨e₁ ∣ ℐ⊨e₂) (intrix , intrix₁ , intrix₂) =
  ⊨⇒BoundarySat e ℐ⊨e intrix ,′
  ⊨⇒BoundarySat e₁ ℐ⊨e₁ intrix₁ ,′
  ⊨⇒BoundarySat e₂ ℐ⊨e₂ intrix₂
⊨⇒BoundarySat (box e) (box ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (unbox e) (unbox ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (` y) ℐ⊨e intrix = tt
⊨⇒BoundarySat (ƛ e) (ƛ ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (e · eₐ) (ℐ⊨e · ℐ⊨eₐ) (intrix , intrixₐ) =
  ⊨⇒BoundarySat e ℐ⊨e intrix ,′
  ⊨⇒BoundarySat eₐ ℐ⊨eₐ intrixₐ
⊨⇒BoundarySat (unroll e) (unroll ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (roll τ e) (roll .τ ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (fix e) (fix ℐ⊨e) intrix = ⊨⇒BoundarySat e ℐ⊨e intrix
⊨⇒BoundarySat (e ⨟ e₁) (ℐ⊨e ⨟ ℐ⊨e₁) (intrix , intrix₁) =
  ⊨⇒BoundarySat e ℐ⊨e intrix ,′
  ⊨⇒BoundarySat e₁ ℐ⊨e₁ intrix₁


isubstᵗ : {ℐ : AnnIntr {𝒜} 𝒯} →
  (eᵗ : (ATAnn 𝒜) ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  ∀ {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} {mvix : MetaVarIx ℐ ϑ} {ix} →
    (⊨ϑ : MetaVarSat ℐ (termEnvᵗ ϑ) (varIxᵗ mvix)) →
    IsTermIx eᵗ tt mvix ix →
    BoundarySat eᵗ tt mvix ix →
    ℐ ⊨[ ix ] esubstᵗ eᵗ ϑ
isubstᵗ (# y) ⊨ϑ ann◁var ⊨bndry = ann◁var (⊨ϑ y)
isubstᵗ (proxy/t a e emᵗ) {ϑ} ⊨ϑ (ix◁ctxt , ann◁var) ((ix◁ix′ , psat) , ⊨bndry) rewrite ix◁ctxt =
  proxy/i (monctorsubstᵗ emᵗ ϑ) _ _ ix◁ix′ psat (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (B# a ⟪ e ⟫) ⊨ϑ (ix◁ctxt , ann◁var) ((ix◁ix′ , bsat) , ⊨bndry) rewrite ix◁ctxt =
  B/i _ _ ix◁ix′ bsat (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ ⋆ ⊨ϑ ann◁var ⊨bndry = ⋆
isubstᵗ `z ⊨ϑ ann◁var ⊨bndry = `z
isubstᵗ (`s e) ⊨ϑ ann◁var ⊨bndry = `s (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (foldN e ez es) ⊨ϑ (ann◁var  , ann◁varz , ann◁vars) (⊨bndry , ⊨bndryz , ⊨bndrys) =
  foldN (isubstᵗ e ⊨ϑ ann◁var ⊨bndry) (isubstᵗ ez ⊨ϑ ann◁varz ⊨bndryz) (isubstᵗ es ⊨ϑ ann◁vars ⊨bndrys)
isubstᵗ (assert e) ⊨ϑ ann◁var ⊨bndry = assert (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (e₁ `, e₂) ⊨ϑ (ann◁var₁ , ann◁var₂) (⊨bndry₁ , ⊨bndry₂) =
  isubstᵗ e₁ ⊨ϑ ann◁var₁ ⊨bndry₁ `, isubstᵗ e₂ ⊨ϑ ann◁var₂ ⊨bndry₂
isubstᵗ (π₁ e) ⊨ϑ ann◁var ⊨bndry = π₁ (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (π₂ e) ⊨ϑ ann◁var ⊨bndry = π₂ (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (inl e) ⊨ϑ ann◁var ⊨bndry = inl (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (inr e) ⊨ϑ ann◁var ⊨bndry = inr (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (case e of e₁ ∣ e₂) ⊨ϑ (ann◁var , ann◁var₁ , ann◁var₂) (⊨bndry , ⊨bndry₁ , ⊨bndry₂) =
  case isubstᵗ e ⊨ϑ ann◁var ⊨bndry of
    isubstᵗ e₁ ⊨ϑ ann◁var₁ ⊨bndry₁
  ∣ isubstᵗ e₂ ⊨ϑ ann◁var₂ ⊨bndry₂
isubstᵗ (box e) ⊨ϑ ann◁var ⊨bndry = box (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (unbox e) ⊨ϑ ann◁var ⊨bndry = unbox (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (` y) ⊨ϑ ann◁var ⊨bndry = ` y
isubstᵗ (ƛ e) ⊨ϑ ann◁var ⊨bndry = ƛ isubstᵗ e ⊨ϑ ann◁var ⊨bndry
isubstᵗ (e · eₐ) ⊨ϑ (ann◁var , ann◁varₐ) (⊨bndry , ⊨bndryₐ) =
  isubstᵗ e ⊨ϑ ann◁var ⊨bndry · isubstᵗ eₐ ⊨ϑ ann◁varₐ ⊨bndryₐ
isubstᵗ (unroll e) ⊨ϑ ann◁var ⊨bndry = unroll (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (roll τ e) ⊨ϑ ann◁var ⊨bndry = roll τ (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (fix e) ⊨ϑ ann◁var ⊨bndry = fix (isubstᵗ e ⊨ϑ ann◁var ⊨bndry)
isubstᵗ (e ⨟ e₁) ⊨ϑ (ann◁var , ann◁var₁) (⊨bndry , ⊨bndry₁) =
  isubstᵗ e ⊨ϑ ann◁var ⊨bndry ⨟ isubstᵗ e₁ ⊨ϑ ann◁var₁ ⊨bndry₁
