{-# OPTIONS --without-K --safe #-}

module Utils.Misc where

open import Agda.Primitive

open import Relation.Binary
  using (IsPreorder; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; subst)

open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; assocʳ′; assocˡ′)
import Data.Product.Properties as Product
open import Data.List.Base as List using (List; []; _∷_; length; lookup)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.List.Properties as List
  using (∷-injective)

open import Function.Base using (_∋_; _∘_; id; const; flip)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Composition using (_↔-∘_)
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Bundles using (Inverse; _↔_; mk↔; mk↔ₛ′)

private variable
  A B C D : Set

substd : {B : A → Set} {a c : A} {b : B a} {d : B c} →
  (P : (a : A) → B a → Set) →
  (eq : a ≡ c) →
  subst B eq b ≡ d →
  P a b → P c d
substd P refl refl p = p

module _ {State : Set} where
  trivialOrd : State → State → Set
  trivialOrd s s′ = ⊤

  trivialOrdIsPreorder : IsPreorder _≡_ trivialOrd
  IsPreorder.isEquivalence trivialOrdIsPreorder = PropEq.isEquivalence
  IsPreorder.reflexive     trivialOrdIsPreorder eq = tt
  IsPreorder.trans         trivialOrdIsPreorder ord ord′ = tt

-- The associativity declaration, the `r` of `infixr`, is missing from the stdlib
infixr 8 _↔-∘′_
_↔-∘′_ = _↔-∘_

↔-×-identityˡ : A ↔ B → (A × ⊤) ↔ B
↔-×-identityˡ iso = mk↔ₛ′ (to ∘ proj₁)
                          ((_,′ tt) ∘ from)
                          (λ b → inverseˡ refl)
                          (λ a,tt → Product.×-≡,≡→≡ (inverseʳ refl ,′ refl))
  where open Inverse iso

↔-×-assoc : ((A × B) × C) ↔ (A × B × C)
↔-×-assoc = mk↔ₛ′ assocʳ′ assocˡ′ (λ _ → refl) (λ _ → refl)

_↔-,_ : A ↔ C → B ↔ D → (A × B) ↔ (C × D)
_↔-,_ iso₁ iso₂ = mk↔ₛ′ (λ a,b → Inverse.to iso₁ (proj₁ a,b) ,′ Inverse.to iso₂ (proj₂ a,b))
                        (λ c,d → Inverse.from iso₁ (proj₁ c,d) ,′ Inverse.from iso₂ (proj₂ c,d))
                        (λ c,d →
                          Product.×-≡,≡→≡ ( Inverse.inverseˡ iso₁ refl ,′
                                            Inverse.inverseˡ iso₂ refl ))
                        (λ a,b →
                          Product.×-≡,≡→≡ ( Inverse.inverseʳ iso₁ refl ,′
                                            Inverse.inverseʳ iso₂ refl ))

all-unfold-map : ∀ {P : A → Set} {Q : B → Set} {xs} →
  (g : A → B) →
  (pg : ∀ {x} → P x → Q (g x)) →
  All P xs →
  All Q (List.map g xs)
all-unfold-map g pg []         = []
all-unfold-map g pg (px ∷ pxs) = pg px ∷ all-unfold-map g pg pxs

all-fold-map : ∀ {P : A → Set} {Q : B → Set} {xs} →
  (g : A → B) →
  (pg : ∀ {x} → Q (g x) → P x) →
  All Q (List.map g xs) →
  All P xs
all-fold-map {xs = []}    g pg []         = []
all-fold-map {xs = _ ∷ _} g pg (px ∷ pxs) = pg px ∷ all-fold-map g pg pxs

all-reverse : ∀ {P : A → Set} {xs} → All P xs → All P (List.reverse xs)
all-reverse [] = []
all-reverse {xs = x ∷ xs} (px ∷ pxs) rewrite List.unfold-reverse x xs
  = ListAll.++⁺ (all-reverse pxs) (px ∷ [])

all-map-zip : ∀ {P : A → Set} {Q : A → Set} {R : A → Set} {xs} →
  (pg : ∀ {x} → P x → Q x → R x) →
  All P xs →
  All Q xs →
  All R xs
all-map-zip pg []         []         = []
all-map-zip pg (px ∷ pxs) (qx ∷ qxs) = pg px qx ∷ all-map-zip pg pxs qxs

all-map₂-subst : {xs : List (A × B)} {ys : List (C × D)} →
  (P : D → Set) →
  (f : B → D) →
  List.map f (List.map proj₂ xs) ≡ List.map proj₂ ys →
  All (P ∘ f ∘ proj₂) xs →
  All (P ∘ proj₂) ys
all-map₂-subst P f map-eq pxs with all-unfold-map {P = P ∘ f} {Q = P} f id (all-unfold-map proj₂ id pxs)
... | map-pxs rewrite map-eq = all-fold-map proj₂ id map-pxs

all₂-subst : {xs : List (A × B)} {ys : List (C × B)} →
  (P : B → Set) →
  List.map proj₂ xs ≡ List.map proj₂ ys →
  All (P ∘ proj₂) xs →
  All (P ∘ proj₂) ys
all₂-subst P map-eq pxs with all-unfold-map proj₂ id pxs
... | map-pxs rewrite map-eq = all-fold-map proj₂ id map-pxs

all-map-subst : {xs : List A} {ys : List B} →
  (P : B → Set) →
  (f : A → B) →
  List.map f xs ≡ ys →
  All (P ∘ f) xs →
  All P ys
all-map-subst P f map-eq pxs with all-unfold-map {Q = P} f id pxs
... | map-pxs rewrite map-eq = map-pxs

all-reverse-map-subst : {ys : List B} →
  (P : B → Set) →
  (f : A → B) →
  (xs : List A) →
  List.reverse (List.map f xs) ≡ ys →
  All (P ∘ f) (List.reverse xs) →
  All P ys
all-reverse-map-subst P f xs map-eq rev-pxs
  rewrite sym (List.reverse-map f xs)
  = all-map-subst P f map-eq rev-pxs

all-reverse-map₂-subst : {ys : List (C × D)} →
  (P : D → Set) →
  (f : B → D) →
  (xs : List (A × B)) →
  List.reverse (List.map f (List.map proj₂ xs)) ≡ List.map proj₂ ys →
  All (P ∘ f ∘ proj₂) (List.reverse xs) →
  All (P ∘ proj₂) ys
all-reverse-map₂-subst P f xs map-eq rev-pxs
  rewrite sym (List.reverse-map f (List.map proj₂ xs))
        | sym (List.reverse-map proj₂ xs)
  = all-map₂-subst P f map-eq rev-pxs

lookupAt : ∀ {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} {xs} → All P xs → (i : Fin (length xs)) → P (lookup xs i)
lookupAt (px ∷ pxs) zero    = px
lookupAt (px ∷ pxs) (suc i) = lookupAt pxs i

data All2 {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} (Q : Σ A P → Set (ℓ ⊔ ℓ′)) :
  ∀ {xs} →
  All P xs →
  Set (ℓ ⊔ ℓ′) where
    [] : All2 Q []
    _∷_ : ∀ {x xs px} {pxs : All P xs} → (qx : Q (x , px)) → (qxs : All2 Q pxs) → All2 Q (px ∷ pxs)

lookupAt2 : ∀ {ℓ ℓ′} →
  ∀ {A : Set ℓ} {P : A → Set ℓ′} {Q : Σ A P → Set (ℓ ⊔ ℓ′)} {xs} {pxs : All P xs} →
  All2 Q pxs → (i : Fin (length xs)) → Q (lookup xs i , lookupAt pxs i)
lookupAt2 (qx ∷ qxs) zero    = qx
lookupAt2 (qx ∷ qxs) (suc i) = lookupAt2 qxs i

all2-map : ∀ {ℓ ℓ′} →
  ∀ {A : Set ℓ} {P : A → Set ℓ′} {Q R : Σ A P → Set (ℓ ⊔ ℓ′)} {xs} {pxs : All P xs} →
  (f : ∀ {x,px} → Q x,px → R x,px) →
  All2 Q pxs → All2 R pxs
all2-map f []         = []
all2-map f (qx ∷ qxs) = f qx ∷ all2-map f qxs

all2-map² : ∀ {ℓ ℓ′} →
  ∀ {A : Set ℓ} {P : A → Set ℓ′} {Q R S : Σ A P → Set (ℓ ⊔ ℓ′)} {xs} {pxs : All P xs} →
  (g : ∀ {x,px} → Q x,px → R x,px → S x,px) →
  All2 Q pxs → All2 R pxs → All2 S pxs
all2-map² g []         []         = []
all2-map² g (qx ∷ qxs) (rx ∷ rxs) = g qx rx ∷ all2-map² g qxs rxs

map-×-≡ :
  {xs ys : List (A × B)} →
  List.map proj₁ xs ≡ List.map proj₁ ys →
  List.map proj₂ xs ≡ List.map proj₂ ys →
  xs ≡ ys
map-×-≡ {xs = []}             {[]}             eqs₁ eqs₂ = refl
map-×-≡ {xs = (x₁ , x₂) ∷ xs} {(y₁ , y₂) ∷ ys} eqs₁ eqs₂ with ∷-injective eqs₁ | ∷-injective eqs₂
... | x₁≡y₁ , map-π₁-xs≡map-π₁-ys | x₂≡y₂ , map-π₂-xs≡map-π₂-ys rewrite x₁≡y₁ | x₂≡y₂ =
  cong ((y₁ , y₂) ∷_) (map-×-≡ map-π₁-xs≡map-π₁-ys map-π₂-xs≡map-π₂-ys)

map-×-≡ˡʳ :
  {xs : List (A × B)} →
  {ys : List (C × D)} →
  (f : C → A) →
  (g : D → B) →
  List.map proj₁ xs ≡ List.map f (List.map proj₁ ys) →
  List.map proj₂ xs ≡ List.map g (List.map proj₂ ys) →
  xs ≡ List.map (Product.map f g) ys
map-×-≡ˡʳ {xs = []}             {[]}             f g eqs₁ eqs₂ = refl
map-×-≡ˡʳ {xs = (x₁ , x₂) ∷ xs} {(y₁ , y₂) ∷ ys} f g eqs₁ eqs₂ with ∷-injective eqs₁ | ∷-injective eqs₂
... | x₁≡y₁ , map-π₁-xs≡map-π₁-ys | x₂≡y₂ , map-π₂-xs≡map-π₂-ys rewrite x₁≡y₁ | x₂≡y₂ =
  cong ((f y₁ , g y₂) ∷_) (map-×-≡ˡʳ f g map-π₁-xs≡map-π₁-ys map-π₂-xs≡map-π₂-ys)

map-×-≡ˡ :
  {xs : List (A × B)} →
  {ys : List (A × C)} →
  (g : C → B) →
  List.map proj₁ xs ≡ List.map proj₁ ys →
  List.map proj₂ xs ≡ List.map g (List.map proj₂ ys) →
  xs ≡ List.map (Product.map₂ g) ys
map-×-≡ˡ {ys = ys} g eqs₁ eqs₂ rewrite sym (List.map-id (List.map proj₁ ys))
  = map-×-≡ˡʳ id g eqs₁ eqs₂

map-×-≡ʳ :
  {xs : List (A × B)} →
  {ys : List (C × B)} →
  (f : C → A) →
  List.map proj₁ xs ≡ List.map f (List.map proj₁ ys) →
  List.map proj₂ xs ≡ List.map proj₂ ys →
  xs ≡ List.map (Product.map₁ f) ys
map-×-≡ʳ {ys = ys} f eqs₁ eqs₂ rewrite sym (List.map-id (List.map proj₂ ys))
  = map-×-≡ˡʳ f id eqs₁ eqs₂

map-×-≡ˡʳ-reverse :
  {xs : List (A × B)} →
  (ys : List (C × D)) →
  (f : C → A) →
  (g : D → B) →
  List.map proj₁ xs ≡ List.reverse (List.map f (List.map proj₁ ys)) →
  List.map proj₂ xs ≡ List.reverse (List.map g (List.map proj₂ ys)) →
  xs ≡ List.reverse (List.map (Product.map f g) ys)
map-×-≡ˡʳ-reverse {xs = xs} ys f g eqs₁ eqs₂
  rewrite sym (List.reverse-map f (List.map proj₁ ys))
        | sym (List.reverse-map proj₁ ys)
        | sym (List.reverse-map g (List.map proj₂ ys))
        | sym (List.reverse-map proj₂ ys)
        | sym (List.reverse-map (Product.map f g) ys)
  = map-×-≡ˡʳ f g eqs₁ eqs₂
