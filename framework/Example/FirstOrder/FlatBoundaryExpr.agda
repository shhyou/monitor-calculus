{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Example.FirstOrder.FlatBoundaryExpr (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product.Base as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Example.FirstOrder.FirstOrderTy 𝒜

open AnnTerm 𝒜 using (Ann; State)

private variable
  𝒯 : AnnTransit 𝒜

  Δ Δ′ : TCtxt
  Γ Γ′ : Ctxt
  τ τ′ τ₁ τ₂ τₐ τᵣ : TyN Δ
  e e′ ez es e₁ e₂ eₐ v : Ann ∣ Γ ⊢ τ
  s s′ : State

-- A boundary-delimited expression that contains only flat boundaries and no proxies
data FlatBdrExpr : (e : Ann ∣ Γ ⊢ τ) → Set where
  B/fb      : (τ/ft : FlatTy [] τ) → (A : Ann τ) → FlatBdrExpr {Γ} (B# A ⟪ e ⟫)
  ⋆/fb      : FlatBdrExpr {Γ} ⋆
  z/fb      : FlatBdrExpr {Γ} `z
  s/fb      : FlatBdrExpr e → FlatBdrExpr (`s e)
  foldN/fb  : FlatBdrExpr e → FlatBdrExpr ez → FlatBdrExpr es → FlatBdrExpr (foldN e ez es)
  assert/fb : FlatBdrExpr e → FlatBdrExpr (assert e)
  _,/fb_    : FlatBdrExpr e₁ → FlatBdrExpr e₂ → FlatBdrExpr (e₁ `, e₂)
  π₁/fb     : FlatBdrExpr e → FlatBdrExpr (π₁ e)
  π₂/fb     : FlatBdrExpr e → FlatBdrExpr (π₂ e)
  inl/fb    : FlatBdrExpr e → FlatBdrExpr {Γ} {τ₁ `+ τ₂} (inl e)
  inr/fb    : FlatBdrExpr e → FlatBdrExpr {Γ} {τ₁ `+ τ₂} (inr e)
  case/fb   : FlatBdrExpr e → FlatBdrExpr e₁ → FlatBdrExpr e₂ → FlatBdrExpr (case e of e₁ ∣ e₂)
  box/fb    : FlatBdrExpr e → FlatBdrExpr (box e)
  unbox/fb  : FlatBdrExpr e → FlatBdrExpr (unbox e)
  `/fb_     : (y : τ ∈ Γ) → FlatBdrExpr (` y)
  ƛ/fb_     : FlatBdrExpr e → FlatBdrExpr (ƛ e)
  _·/fb_    : FlatBdrExpr e → FlatBdrExpr eₐ → FlatBdrExpr (e · eₐ)
  unroll/fb : FlatBdrExpr e → FlatBdrExpr (unroll e)
  roll/fb   : FlatBdrExpr e → FlatBdrExpr (roll τ e)
  fix/fb    : FlatBdrExpr e → FlatBdrExpr (fix e)
  _⨟/fb_    : FlatBdrExpr e → FlatBdrExpr e₁ → FlatBdrExpr (e ⨟ e₁)


f0mapsto [f0↦_] : {e : Ann ∣ Γ ⊢ τ} →
  FlatBdrExpr e →
  ∀ {τ′} → (y : τ′ ∈ (τ ∷ Γ)) → FlatBdrExpr ([x0↦ e ] y)
f0mapsto e/fb (here refl)  = e/fb
f0mapsto e/fb (there τ′∈Γ) = `/fb τ′∈Γ
[f0↦_] = f0mapsto

f0f1mapsto [f0↦_&&f1↦_] : {e₁ : Ann ∣ Γ ⊢ τ} {e₂ : Ann ∣ Γ ⊢ τ′} →
  FlatBdrExpr e₁ →
  FlatBdrExpr e₂ →
  ∀ {τ″} → (y : τ″ ∈ (τ ∷ τ′ ∷ Γ)) → FlatBdrExpr ([x0↦ e₁ &&x1↦ e₂ ] y)
f0f1mapsto e0 e1 (here refl)          = e0
f0f1mapsto e0 e1 (there (here refl))  = e1
f0f1mapsto e0 e1 (there (there τ″∈Γ)) = `/fb τ″∈Γ
[f0↦_&&f1↦_] = f0f1mapsto

frename :
  FlatBdrExpr e →
  (ren : ∀ {τ} → τ ∈ Γ → τ ∈ Γ′) →
  FlatBdrExpr (erename e ren)
frename (B/fb τ/ft A)               ren = B/fb τ/ft A
frename ⋆/fb                        ren = ⋆/fb
frename z/fb                        ren = z/fb
frename (s/fb e/fb)                 ren = s/fb (frename e/fb ren)
frename (foldN/fb e/fb ez/fb es/fb) ren =
  foldN/fb (frename e/fb ren) (frename ez/fb ren) (frename es/fb (pext (pext ren)))
frename (assert/fb e/fb)            ren = assert/fb (frename e/fb ren)
frename (e₁/fb ,/fb e₂/fb)          ren = frename e₁/fb ren ,/fb frename e₂/fb ren
frename (π₁/fb e/fb)                ren = π₁/fb (frename e/fb ren)
frename (π₂/fb e/fb)                ren = π₂/fb (frename e/fb ren)
frename (inl/fb e/fb)               ren = inl/fb (frename e/fb ren)
frename (inr/fb e/fb)               ren = inr/fb (frename e/fb ren)
frename (case/fb e/fb e₁/fb e₂/fb)  ren =
  case/fb (frename e/fb ren) (frename e₁/fb (pext ren)) (frename e₂/fb (pext ren))
frename (box/fb e/fb)               ren = box/fb (frename e/fb ren)
frename (unbox/fb e/fb)             ren = unbox/fb (frename e/fb ren)
frename (`/fb y)                    ren = `/fb (ren y)
frename (ƛ/fb e/fb)                 ren = ƛ/fb (frename e/fb (pext ren))
frename (e/fb ·/fb eₐ/fb)           ren = frename e/fb ren ·/fb frename eₐ/fb ren
frename (unroll/fb e/fb)            ren = unroll/fb (frename e/fb ren)
frename (roll/fb e/fb)              ren = roll/fb (frename e/fb ren)
frename (fix/fb e/fb)               ren = fix/fb (frename e/fb (pext ren))
frename (e/fb ⨟/fb e₁/fb)           ren = frename e/fb ren ⨟/fb frename e₁/fb ren

fext :
  {σ : ∀ {τ′} → τ′ ∈ Γ → Ann ∣ Γ′ ⊢ τ′} →
  (σf : ∀ {τ} → (y : τ ∈ Γ) → FlatBdrExpr (σ y)) →
  ∀ {τ′} → (y : τ′ ∈ τ ∷ Γ) → FlatBdrExpr (eext σ y)
fext σf (here refl) = `/fb here refl
fext σf (there τ∈Γ) = frename (σf τ∈Γ) there

fsubst :
  FlatBdrExpr e →
  {σ : ∀ {τ} → τ ∈ Γ → Ann ∣ Γ′ ⊢ τ} →
  (σf : ∀ {τ} → (y : τ ∈ Γ) → FlatBdrExpr (σ y)) →
  FlatBdrExpr (esubst e σ)
fsubst (B/fb τ/ft A) σf               = B/fb τ/ft A
fsubst ⋆/fb σf                        = ⋆/fb
fsubst z/fb σf                        = z/fb
fsubst (s/fb e/fb) σf                 = s/fb (fsubst e/fb σf)
fsubst (foldN/fb e/fb ez/fb es/fb) σf =
  foldN/fb (fsubst e/fb σf) (fsubst ez/fb σf) (fsubst es/fb (fext (fext σf)))
fsubst (assert/fb e/fb) σf            = assert/fb (fsubst e/fb σf)
fsubst (e₁/fb ,/fb e₂/fb) σf          = fsubst e₁/fb σf ,/fb fsubst e₂/fb σf
fsubst (π₁/fb e/fb) σf                = π₁/fb (fsubst e/fb σf)
fsubst (π₂/fb e/fb) σf                = π₂/fb (fsubst e/fb σf)
fsubst (inl/fb e/fb) σf               = inl/fb (fsubst e/fb σf)
fsubst (inr/fb e/fb) σf               = inr/fb (fsubst e/fb σf)
fsubst (case/fb e/fb e₁/fb e₂/fb) σf  =
  case/fb (fsubst e/fb σf) (fsubst e₁/fb (fext σf)) (fsubst e₂/fb (fext σf))
fsubst (box/fb e/fb) σf               = box/fb (fsubst e/fb σf)
fsubst (unbox/fb e/fb) σf             = unbox/fb (fsubst e/fb σf)
fsubst (`/fb y) σf                    = σf y
fsubst (ƛ/fb e/fb) σf                 = ƛ/fb (fsubst e/fb (fext σf))
fsubst (e/fb ·/fb eₐ/fb) σf           = fsubst e/fb σf ·/fb fsubst eₐ/fb σf
fsubst (unroll/fb e/fb) σf            = unroll/fb (fsubst e/fb σf)
fsubst (roll/fb e/fb) σf              = roll/fb (fsubst e/fb σf)
fsubst (fix/fb e/fb) σf               = fix/fb (fsubst e/fb (fext σf))
fsubst (e/fb ⨟/fb e₁/fb) σf           = fsubst e/fb σf ⨟/fb fsubst e₁/fb σf


fbexpr-betarel : e ⟶r e′ → FlatBdrExpr e → FlatBdrExpr e′
fbexpr-betarel R-foldz          (foldN/fb e/fb ez/fb es/fb)         = ez/fb
fbexpr-betarel (R-folds iv)     (foldN/fb (s/fb e/fb) ez/fb es/fb)  =
  fsubst es/fb [f0↦ e/fb &&f1↦ foldN/fb e/fb ez/fb es/fb ]
fbexpr-betarel (R-assert iv)    (assert/fb e/fb)                    = ⋆/fb
fbexpr-betarel (R-outl iv₁ iv₂) (π₁/fb (e₁/fb ,/fb e₂/fb))          = e₁/fb
fbexpr-betarel (R-outr iv₁ iv₂) (π₂/fb (e₁/fb ,/fb e₂/fb))          = e₂/fb
fbexpr-betarel (R-casel iv)     (case/fb (inl/fb e/fb) e₁/fb e₂/fb) = fsubst e₁/fb [f0↦ e/fb ]
fbexpr-betarel (R-caser iv)     (case/fb (inr/fb e/fb) e₁/fb e₂/fb) = fsubst e₂/fb [f0↦ e/fb ]
fbexpr-betarel (R-unbox iv)     (unbox/fb (box/fb e/fb))            = e/fb
fbexpr-betarel (R-β iv)         ((ƛ/fb e/fb) ·/fb eₐ/fb)            = fsubst e/fb [f0↦ eₐ/fb ]
fbexpr-betarel (R-unroll iv)    (unroll/fb (roll/fb e/fb))          = e/fb
fbexpr-betarel R-fix            (fix/fb e/fb)                       = fsubst e/fb [f0↦ fix/fb e/fb ]
fbexpr-betarel (R-seq iv)       (e/fb ⨟/fb e₁/fb₁)                  = e₁/fb₁


nat-is-flat : Ann ∣ v isvalof `ℕ → FlatBdrExpr v
nat-is-flat z/v      = z/fb
nat-is-flat (s/v iv) = s/fb (nat-is-flat iv)

fbexpr-bdrrel : {e e′ : Ann ∣ [] ⊢ τ} →
  (𝒯 : AnnTransit 𝒜) →
  (tag : RuleTag) →
  ATStep 𝒜 (AnnRules Ann tag , 𝒯 tag) s e s′ e′ →
  FlatBdrExpr e → FlatBdrExpr e′
fbexpr-bdrrel 𝒯 `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb τ/ft e/fb)
  = ⋆/fb
fbexpr-bdrrel 𝒯 `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit@iv trWit)
  (B/fb τ/ft A)
  = nat-is-flat iv
fbexpr-bdrrel 𝒯 `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb (τ₁/f */f τ₂/f) A)
  = B/fb τ₁/f (ψ₂(here refl)) ,/fb B/fb τ₂/f (ψ₂(there (here refl)))
fbexpr-bdrrel 𝒯 `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb (τ₁/f +/f τ₂/f) A)
  = inl/fb (B/fb τ₁/f (ψ₂(here refl)))
fbexpr-bdrrel 𝒯 `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb (τ₁/f +/f τ₂/f) A)
  = inr/fb (B/fb τ₂/f (ψ₂(here refl)))
fbexpr-bdrrel 𝒯 `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb (μ/f τ/f) A)
  = roll/fb (B/fb (ftsubst τ/f [ft0↦ (μ/f τ/f) ]) (ψ₂(here refl)))
fbexpr-bdrrel 𝒯 `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb () A)
fbexpr-bdrrel 𝒯 `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb () A)
fbexpr-bdrrel 𝒯 `R-merge-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb () A)
fbexpr-bdrrel 𝒯 `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/fb () A)
fbexpr-bdrrel 𝒯 `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (unbox/fb ())
fbexpr-bdrrel 𝒯 `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (() ·/fb eₐ/fb)

fbexpr-ctxt : {Rel : ReductionRel 𝒜} →
  (∀ {τ′} {e e′ : Ann ∣ [] ⊢ τ′} → Rel s e s′ e′ → FlatBdrExpr e → FlatBdrExpr e′) →
  CtxtRel 𝒜 Rel s e s′ e′ →
  FlatBdrExpr e → FlatBdrExpr e′
fbexpr-ctxt step-resp (RC-here step) e/fb =
  step-resp step e/fb
fbexpr-ctxt step-resp (RC-B step) (B/fb τ/ft A) =
  B/fb τ/ft A
fbexpr-ctxt step-resp (RC-s step) (s/fb e/fb) =
  s/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-foldN step) (foldN/fb e/fb ez/fb es/fb) =
  foldN/fb (fbexpr-ctxt step-resp step e/fb) ez/fb es/fb
fbexpr-ctxt step-resp (RC-assert step) (assert/fb e/fb) =
  assert/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-consl step) (e₁/fb ,/fb e₂/fb) =
  (fbexpr-ctxt step-resp step e₁/fb) ,/fb e₂/fb
fbexpr-ctxt step-resp (RC-consr iv step) (e₁/fb ,/fb e₂/fb) =
  e₁/fb ,/fb (fbexpr-ctxt step-resp step e₂/fb)
fbexpr-ctxt step-resp (RC-outl step) (π₁/fb e/fb) =
  π₁/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-outr step) (π₂/fb e/fb) =
  π₂/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-inl step) (inl/fb e/fb) =
  inl/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-inr step) (inr/fb e/fb) =
  inr/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-case step) (case/fb e/fb e₁/fb e₂/fb) =
  case/fb (fbexpr-ctxt step-resp step e/fb) e₁/fb e₂/fb
fbexpr-ctxt step-resp (RC-box step) (box/fb e/fb) =
  box/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-unbox step) (unbox/fb e/fb) =
  unbox/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-appl step) (e/fb ·/fb eₐ/fb) =
  (fbexpr-ctxt step-resp step e/fb) ·/fb eₐ/fb
fbexpr-ctxt step-resp (RC-appr iv step) (e/fb ·/fb eₐ/fb) =
  e/fb ·/fb (fbexpr-ctxt step-resp step eₐ/fb)
fbexpr-ctxt step-resp (RC-unroll step) (unroll/fb e/fb) =
  unroll/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-roll step) (roll/fb e/fb) =
  roll/fb (fbexpr-ctxt step-resp step e/fb)
fbexpr-ctxt step-resp (RC-seq step) (e/fb ⨟/fb e₁/fb) =
  (fbexpr-ctxt step-resp step e/fb) ⨟/fb e₁/fb

flatty∧isval⇒fbexpr : FlatTy [] τ → Ann ∣ v isvalof τ → FlatBdrExpr v
flatty∧isval⇒fbexpr 1/f               ⋆/v            = ⋆/fb
flatty∧isval⇒fbexpr ℕ/f               z/v            = z/fb
flatty∧isval⇒fbexpr ℕ/f               (s/v iv)       = s/fb (flatty∧isval⇒fbexpr ℕ/f iv)
flatty∧isval⇒fbexpr (τ₁/ft */f τ₂/ft) (iv₁ `,/v iv₂) =
  (flatty∧isval⇒fbexpr τ₁/ft iv₁) ,/fb (flatty∧isval⇒fbexpr τ₂/ft iv₂)
flatty∧isval⇒fbexpr (τ₁/ft +/f τ₂/ft) (inl/v iv)     = inl/fb (flatty∧isval⇒fbexpr τ₁/ft iv)
flatty∧isval⇒fbexpr (τ₁/ft +/f τ₂/ft) (inr/v iv)     = inr/fb (flatty∧isval⇒fbexpr τ₂/ft iv)
flatty∧isval⇒fbexpr (μ/f τ/ft)        (roll/v iv)    =
  roll/fb (flatty∧isval⇒fbexpr (ftsubst τ/ft [ft0↦ (μ/f τ/ft) ]) iv)
