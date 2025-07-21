{-# OPTIONS --without-K --safe #-}

open import Annotation.Language
open import Blame.Base
  using (module AnnBlameContractLang)
  renaming (𝒜owner to B𝒜owner)
open AnnBlameContractLang
  using ()
  renaming (𝒜blame to B𝒜blame)

module Blame.Consistency
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜owner-view : AnnTermView 𝒜 (B𝒜owner Label))
  (𝒜blame-view : AnnTermView 𝒜 (B𝒜blame Label 𝒜))
  where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; subst; trans)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; curry; uncurry)

open import Data.List.Base as List using (List; []; _∷_; length; _++_; map; reverse)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All.Properties as ListAll
import Data.List.Properties as List

open import Function.Base using (id; const; constᵣ; _∘′_)

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Interpretation

open Blame.Base Label hiding (module AnnBlameContractLang)
open import Blame.Sign Label 𝒜
open import Contract.Common Label
open import Contract.Base Label 𝒜
open import Contract.Satisfaction Label 𝒜
open AnnTerm 𝒜

open AnnBlameContractLang Label 𝒜
open AnnTermView 𝒜blame-view

private variable
  Δ Δ′ : TCtxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ

  ± : Sgn
  δ  : All (const Sgn) Δ
  δ′ : All (const Sgn) Δ′

  b : Blame

𝒜sctc-view  : AnnTermView 𝒜 𝒜sctc
𝒜sctc-view = annTermViewCompose 𝒜blame-sctc-view 𝒜blame-view

𝒜blameobj-view : AnnTermView 𝒜 𝒜blameobj
𝒜blameobj-view = annTermViewCompose 𝒜blame-blameobj-view 𝒜blame-view

𝒯 : ℕ → AnnTransit 𝒜
𝒯 zero    = ∅tr
𝒯 (suc i) = 𝒯blame 𝒜blameobj-view  ∩tr  𝒯owner 𝒜owner-view  ∩tr  (𝒯sctc 𝒜sctc-view (𝒯 i))

data BlameConsistent : ∀ {Δ τ} → Blame → SCtc1N Δ τ → Set where
  `_ : (a : tt ∈ Δ) → BlameConsistent b (` a)
  1/bc : BlameConsistent {Δ} b 1/c
  flat/bc : ∀ {l e} →
    l ≡ bpos b →
    BlameConsistent {Δ} b (flat l e)
  _*/bc_ : ∀ {sκ₁ sκ₂} →
    BlameConsistent b sκ₁ →
    BlameConsistent b sκ₂ →
    BlameConsistent {Δ} {τ₁ `* τ₂} b (sκ₁ */c sκ₂)
  _+/bc_ : ∀ {sκ₁ sκ₂} →
    BlameConsistent b sκ₁ →
    BlameConsistent b sκ₂ →
    BlameConsistent {Δ} {τ₁ `+ τ₂} b (sκ₁ +/c sκ₂)
  box/bc : ∀ {sκ} →
    BlameConsistent b sκ →
    BlameConsistent {Δ} {Box τ} b (box/c sκ)
  _→/bc_ : ∀ {sκₐ sκᵣ} →
    BlameConsistent (blame-swap b) sκₐ →
    BlameConsistent b sκᵣ →
    BlameConsistent {Δ} {τₐ `→ τᵣ} b (sκₐ →/c sκᵣ)
  μ/bc_ : ∀ {sκ} →
    BlameConsistent           b sκ →
    BlameConsistent {Δ} {μ τ} b (μ/c sκ)

bcrename :
  {sκ : SCtc1N Δ τ} →
  BlameConsistent b sκ →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  BlameConsistent b (sκrename sκ ren)
bcrename (` a)           ren = ` ren a
bcrename 1/bc            ren = 1/bc
bcrename (flat/bc lp)    ren = flat/bc lp
bcrename (bc₁ */bc bc₂)  ren = bcrename bc₁ ren */bc bcrename bc₂ ren
bcrename (bc₁ +/bc bc₂)  ren = bcrename bc₁ ren +/bc bcrename bc₂ ren
bcrename (box/bc bc)     ren = box/bc (bcrename bc ren)
bcrename (bcₐ →/bc bcᵣ)  ren = bcrename bcₐ ren →/bc bcrename bcᵣ ren
bcrename (μ/bc bc)       ren = μ/bc (bcrename bc (pext ren))

bcext :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  (σbc : (a : tt ∈ Δ) → BlameConsistent (signed-blame (ListAll.lookup δ a) b) (σκ a)) →
  (a : tt ∈ (tt ∷ Δ)) →
    BlameConsistent {tt ∷ Δ′} (signed-blame (ListAll.lookup (± ∷ δ) a) b) (sκext σκ a)
bcext σbc (here refl) = ` here refl
bcext σbc (there x∈Δ) = bcrename (σbc x∈Δ) there

bcsubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  {sκ : SCtc1N Δ τ} →
  BlameConsistent (signed-blame ± b) sκ →
  SCtcSigned ± δ sκ →
  (σp : (a : tt ∈ Δ) → SCtcSigned (ListAll.lookup δ a) δ′ (σκ a)) →
  (σbc : (a : tt ∈ Δ) → BlameConsistent (signed-blame (ListAll.lookup δ a) b) (σκ a)) →
  BlameConsistent (signed-blame ± b) (sκsubst sκ σκ)
bcsubst (` a)                 (` .a)          σp σbc = σbc a
bcsubst 1/bc                  pmκ             σp σbc = 1/bc
bcsubst (flat/bc lposeq)      pmκ             σp σbc = flat/bc lposeq
bcsubst (bc₁ */bc bc₂)        (pmκ₁ */p pmκ₂) σp σbc = bcsubst bc₁ pmκ₁ σp σbc */bc bcsubst bc₂ pmκ₂ σp σbc
bcsubst (bc₁ +/bc bc₂)        (pmκ₁ +/p pmκ₂) σp σbc = bcsubst bc₁ pmκ₁ σp σbc +/bc bcsubst bc₂ pmκ₂ σp σbc
bcsubst (box/bc bc)           (box/p pmκ)     σp σbc = box/bc (bcsubst bc pmκ σp σbc)
bcsubst {± = ±} {b = b} {σκ = σκ} {sκₐ →/c sκᵣ} (bcₐ →/bc bcᵣ) (pmκₐ →/p pmκᵣ) σp σbc =
  substd-bcₐ →/bc bcsubst bcᵣ pmκᵣ σp σbc where
    substd-bcₐ : BlameConsistent (blame-swap (signed-blame ± b)) (sκsubst sκₐ σκ)
    substd-bcₐ rewrite blame-swap-sgn-negate ± b = bcsubst bcₐ pmκₐ σp σbc
bcsubst (μ/bc bc)             (μ/p pmκ)      σp σbc = μ/bc (bcsubst bc pmκ (pmκext σp) (bcext σbc))

bc0mapsto [bc0↦_] : {sκ : SCtc1N Δ τ} →
  BlameConsistent (signed-blame ± b) sκ →
  (a : tt ∈ (tt ∷ Δ)) →
  BlameConsistent (signed-blame (ListAll.lookup (± ∷ δ) a) b) ([sκ0↦ sκ ] a)
bc0mapsto bc (here refl) = bc
bc0mapsto bc (there x∈Δ) = ` x∈Δ

[bc0↦_] = bc0mapsto


blcon-*₁ : ∀ {sκ} →
  BlameConsistent {Δ} {τ₁ `* τ₂} b sκ → BlameConsistent b (*/c-sκ₁ sκ)
blcon-*₁ (bc₁ */bc bc₂) = bc₁

blcon-*₂ : ∀ {sκ} →
  BlameConsistent {Δ} {τ₁ `* τ₂} b sκ → BlameConsistent b (*/c-sκ₂ sκ)
blcon-*₂ (bc₁ */bc bc₂) = bc₂

blcon-+₁ : ∀ {sκ} →
  BlameConsistent {Δ} {τ₁ `+ τ₂} b sκ → BlameConsistent b (+/c-sκ₁ sκ)
blcon-+₁ (bc₁ +/bc bc₂) = bc₁

blcon-+₂ : ∀ {sκ} →
  BlameConsistent {Δ} {τ₁ `+ τ₂} b sκ → BlameConsistent b (+/c-sκ₂ sκ)
blcon-+₂ (bc₁ +/bc bc₂) = bc₂

blcon-box : ∀ {sκ} →
  BlameConsistent {Δ} {Box τ} b sκ → BlameConsistent b (box/c-sκ sκ)
blcon-box (box/bc bc) = bc

blcon-dom : ∀ {sκ} →
  BlameConsistent {Δ} {τₐ `→ τᵣ} b sκ → BlameConsistent (blame-swap b) (→/c-dom-sκ sκ)
blcon-dom (bcₐ →/bc bcᵣ) = bcₐ

blcon-rng : ∀ {sκ} →
  BlameConsistent {Δ} {τₐ `→ τᵣ} b sκ → BlameConsistent b (→/c-rng-sκ sκ)
blcon-rng (bcₐ →/bc bcᵣ) = bcᵣ

blcon-μ : ∀ {sκ} →
  SCtcSigned {Δ} ± δ sκ →
  BlameConsistent {Δ} {μ τ} (signed-blame ± b) sκ →
  BlameConsistent (signed-blame ± b) (μ/c-sκ sκ)
blcon-μ (μ/p pmκ) (μ/bc bc) = bcsubst bc pmκ [pmκ0↦ μ/p pmκ ] [bc0↦ μ/bc bc ]

ℐconsistent : (i : ℕ) → AnnIntr (𝒯 i)
AnnIntr.Ix         (ℐconsistent i) = ⊤
AnnIntr.IxRel      (ℐconsistent i) A ix ix′ = ⊤
AnnIntr.Inv        (ℐconsistent i) s = ⊤
AnnIntr.Ord        (ℐconsistent i) = trivialOrd
AnnIntr.isPreorder (ℐconsistent i) = trivialOrdIsPreorder
AnnIntr.𝔹          (ℐconsistent zero)    obsκs ix◁ix′ e = ⊥
AnnIntr.𝔹          (ℐconsistent (suc i)) obsκs ix◁ix′ e =
  All (SCtcSigned pos [] ∘′ proj₂) (getAnn obsκs) ×
  All (uncurry BlameConsistent) (getAnn obsκs) ×
  All (SCtcSat (ℐconsistent i) tt ∘′ proj₂) (getAnn obsκs)
AnnIntr.𝔹Sound     (ℐconsistent zero)    step inv inv′ mono ()
AnnIntr.𝔹Sound     (ℐconsistent (suc i)) step inv inv′ mono (pmκs , bcs , κsats) =
  pmκs ,′ bcs ,′ κsats
AnnIntr.ℙ          (ℐconsistent i) obsκs ix◁ix′ em =
  AnnIntr.𝔹 (ℐconsistent i) obsκs ix◁ix′ ⌊ em ⌋m

ℐconsistency-monotonic : ∀ i → AnnTransitInterpIs (ℐconsistent i) Monotonic
ℐconsistency-monotonic zero    tag step esat₁ termSat = tt , tt
ℐconsistency-monotonic (suc i) tag step esat₁ termSat = tt , tt

ℐconsistency-sound : ∀ i → AnnTransitInterpIs (ℐconsistent i) Sound
ℐconsistency-sound zero `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-merge-box
  step@(mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound zero `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit ())
  esat termSat inv′,mono
ℐconsistency-sound (suc i) `R-cross-unit
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat ⋆)
  termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐconsistency-sound (suc i) `R-cross-nat
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit trWit)
  (B/i ix ix′ ix◁ix′ bsat esat)
  termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐconsistency-sound (suc i) `R-cross-cons
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((bs₁-eq , bs₂-eq) , (owns₁-eq , owns₂-eq) , (s-eq , refl) , (sκs₁-eq , sκs₂-eq)))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
       (tt ,
        (all-map₂-subst (SCtcSigned pos [])
                        */c-sκ₁
                        (sym sκs₁-eq)
                        (ListAll.map pmκ-*₁ pmκs) ,′
         all-map-subst  (uncurry BlameConsistent)
                        (Product.map₂ */c-sκ₁)
                        (sym (map-×-≡ˡ */c-sκ₁ bs₁-eq sκs₁-eq))
                        (ListAll.map blcon-*₁ bcs) ,′
         all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        */c-sκ₁
                        (sym sκs₁-eq)
                        (ListAll.map sκsat-*₁ κsats))) ,′
       (tt ,
        (all-map₂-subst (SCtcSigned pos [])
                        */c-sκ₂
                        (sym sκs₂-eq)
                        (ListAll.map pmκ-*₂ pmκs) ,′
         all-map-subst  (uncurry BlameConsistent)
                        (Product.map₂ */c-sκ₂)
                        (sym (map-×-≡ˡ */c-sκ₂ bs₂-eq sκs₂-eq))
                        (ListAll.map blcon-*₂ bcs) ,′
         all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        */c-sκ₂
                        (sym sκs₂-eq)
                        (ListAll.map sκsat-*₂ κsats)))
    }
ℐconsistency-sound (suc i) `R-cross-inl
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all-map₂-subst (SCtcSigned pos [])
                        +/c-sκ₁
                        (sym sκs-eq)
                        (ListAll.map pmκ-+₁ pmκs) ,′
         all-map-subst  (uncurry BlameConsistent)
                        (Product.map₂ +/c-sκ₁)
                        (sym (map-×-≡ˡ +/c-sκ₁ bs-eq sκs-eq))
                        (ListAll.map blcon-+₁ bcs) ,′
         all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        +/c-sκ₁
                        (sym sκs-eq)
                        (ListAll.map sκsat-+₁ κsats))
    }
ℐconsistency-sound (suc i) `R-cross-inr
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all-map₂-subst (SCtcSigned pos [])
                        +/c-sκ₂
                        (sym sκs-eq)
                        (ListAll.map pmκ-+₂ pmκs) ,′
         all-map-subst  (uncurry BlameConsistent)
                        (Product.map₂ +/c-sκ₂)
                        (sym (map-×-≡ˡ +/c-sκ₂ bs-eq sκs-eq))
                        (ListAll.map blcon-+₂ bcs) ,′
         all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        +/c-sκ₂
                        (sym sκs-eq)
                        (ListAll.map sκsat-+₂ κsats))
    }
ℐconsistency-sound (suc i) `R-cross-roll
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all-map₂-subst (SCtcSigned pos [])
                        μ/c-sκ
                        (sym sκs-eq)
                        (ListAll.map pmκ-μ pmκs) ,′
         all-map-subst  (uncurry BlameConsistent)
                        (Product.map₂ μ/c-sκ)
                        (sym (map-×-≡ˡ μ/c-sκ bs-eq sκs-eq))
                        (all-map-zip blcon-μ pmκs bcs) ,′
         all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        μ/c-sκ
                        (sym sκs-eq)
                        (ListAll.map sκsat-μ κsats))
    }
ℐconsistency-sound (suc i) `R-cross-box
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all₂-subst (SCtcSigned pos []) (sym sκs-eq) pmκs ,′
         subst  (All (uncurry BlameConsistent))
                (sym (map-×-≡ bs-eq sκs-eq))
                bcs ,′
         all₂-subst (SCtcSat (ℐconsistent i) tt) (sym sκs-eq) κsats)
    }
ℐconsistency-sound (suc i) `R-cross-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all₂-subst (SCtcSigned pos []) (sym sκs-eq) pmκs ,′
         subst  (All (uncurry BlameConsistent))
                (sym (map-×-≡ bs-eq sκs-eq))
                bcs ,′
         all₂-subst (SCtcSat (ℐconsistent i) tt) (sym sκs-eq) κsats)
    }
ℐconsistency-sound (suc i) `R-merge-box
  step@(mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          trWit@(bs-eq , (owns-eq , match-eq) , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  termSat@record { boundarySat = (_ , (pmκs , bcs , κsats)) , (_ , (pmκs′ , bcs′ , κsats′)) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all₂-subst (SCtcSigned pos [])
                    (sym (trans sκs-eq (sym (List.map-++  proj₂
                                                          (getAnn (ψ₁(there (here refl))))
                                                          (getAnn (ψ₁(here refl)))))))
                    (ListAll.++⁺ pmκs′ pmκs) ,′
         subst  (All (uncurry BlameConsistent))
                (sym (map-×-≡
                      (trans bs-eq (sym (List.map-++  proj₁
                                                      (getAnn (ψ₁(there (here refl))))
                                                      (getAnn (ψ₁(here refl))))))
                      (trans sκs-eq (sym (List.map-++ proj₂
                                                      (getAnn (ψ₁(there (here refl))))
                                                      (getAnn (ψ₁(here refl))))))))
                (ListAll.++⁺ bcs′ bcs) ,′
         all₂-subst (SCtcSat (ℐconsistent i) tt)
                    (sym (trans sκs-eq (sym (List.map-++  proj₂
                                                          (getAnn (ψ₁(there (here refl))))
                                                          (getAnn (ψ₁(here refl)))))))
                    (ListAll.++⁺ κsats′ κsats))
    }
ℐconsistency-sound (suc i) `R-merge-lam
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , (owns-eq , match-eq) , (s-eq , refl) , sκs-eq))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esatb)))
  termSat@record { boundarySat = (_ , (pmκs , bcs , κsats)) , (_ , (pmκs′ , bcs′ , κsats′)) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix″ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all₂-subst (SCtcSigned pos [])
                    (sym (trans sκs-eq (sym (List.map-++  proj₂
                                                          (getAnn (ψ₁(there (here refl))))
                                                          (getAnn (ψ₁(here refl)))))))
                    (ListAll.++⁺ pmκs′ pmκs) ,′
         subst  (All (uncurry BlameConsistent))
                (sym (map-×-≡
                      (trans bs-eq (sym (List.map-++  proj₁
                                                      (getAnn (ψ₁(there (here refl))))
                                                      (getAnn (ψ₁(here refl))))))
                      (trans sκs-eq (sym (List.map-++ proj₂
                                                      (getAnn (ψ₁(there (here refl))))
                                                      (getAnn (ψ₁(here refl))))))))
                (ListAll.++⁺ bcs′ bcs) ,′
         all₂-subst (SCtcSat (ℐconsistent i) tt)
                    (sym (trans sκs-eq (sym (List.map-++  proj₂
                                                          (getAnn (ψ₁(there (here refl))))
                                                          (getAnn (ψ₁(here refl)))))))
                    (ListAll.++⁺ κsats′ κsats))
    }
ℐconsistency-sound (suc i) `R-proxy-unbox
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@(bs-eq , owns-eq , (s-eq , refl) , sκs-eq))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        (all-map₂-subst (SCtcSigned pos [])
                        box/c-sκ
                        (sym sκs-eq)
                        (ListAll.map pmκ-box pmκs) ,′
         all-map-subst  (uncurry BlameConsistent)
                        (Product.map₂ box/c-sκ)
                        (sym (map-×-≡ˡ box/c-sκ bs-eq sκs-eq))
                        (ListAll.map blcon-box bcs) ,′
         all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        box/c-sκ
                        (sym sκs-eq)
                        (ListAll.map sκsat-box κsats))
    }
ℐconsistency-sound (suc i) `R-proxy-β
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
    trWit@((bsₐ-eq , bsᵣ-eq) , (ownsₐ-eq , ownsᵣ-eq) , (s-eq , refl) , (sκsₐ-eq , sκsᵣ-eq)))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  termSat@record { boundarySat = _ , (pmκs , bcs , κsats) }
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        (tt ,
         (all-map₂-subst (SCtcSigned pos [])
                        →/c-rng-sκ
                        (sym sκsᵣ-eq)
                        (ListAll.map pmκ-rng pmκs) ,′
          all-map-subst (uncurry BlameConsistent)
                        (Product.map₂ →/c-rng-sκ)
                        (sym (map-×-≡ˡ →/c-rng-sκ bsᵣ-eq sκsᵣ-eq))
                        (ListAll.map blcon-rng bcs) ,′
          all-map₂-subst (SCtcSat (ℐconsistent i) tt)
                        →/c-rng-sκ
                        (sym sκsᵣ-eq)
                        (ListAll.map sκsat-rng κsats))) ,′
        (tt ,
         (ListAll.map pmκnegate
                      (all-reverse-map₂-subst (SCtcSigned neg [])
                                              →/c-dom-sκ
                                              (getAnn (ψ₁(here refl)))
                                              (sym sκsₐ-eq)
                                              (all-reverse (ListAll.map pmκ-dom pmκs))) ,′
         subst (All (uncurry BlameConsistent))
              (sym (map-×-≡ˡʳ-reverse (getAnn (ψ₁(here refl))) blame-swap →/c-dom-sκ bsₐ-eq sκsₐ-eq))
              (all-reverse (all-unfold-map (Product.map blame-swap →/c-dom-sκ) blcon-dom bcs)) ,′
         all-reverse-map₂-subst (SCtcSat (ℐconsistent i) tt)
                                →/c-dom-sκ
                                (getAnn (ψ₁(here refl)))
                                (sym sκsₐ-eq)
                                (all-reverse (ListAll.map sκsat-dom κsats))))
    }
