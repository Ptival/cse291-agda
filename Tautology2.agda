module Tautology2 where

open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level using (_⊔_)
open import Reflection renaming (_≟_ to _≟-Term_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary hiding (Dec)

infixr 0 _∨_
infixr 0 _∧_


data _∨_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  ↼∨ : A → A ∨ B
  ∨⇀ : B → A ∨ B


data _∧_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _∧i_ : A → B → A ∧ B


p₁ : ∀ {A B : Set} → A ∧ B → A
p₁ (l ∧i r) = l


p₂ : ∀ {A B : Set} → A ∧ B → B
p₂ (l ∧i r) = r


data Formula : Set where
  TAtomic : Term → Formula
  TTrue   : Formula
  TFalse  : Formula
  TAnd    : (a : Formula) → (b : Formula) → Formula
  TOr     : (a : Formula) → (b : Formula) → Formula
  TImp    : (a : Formula) → (b : Formula) → Formula


Assign : Set₁
Assign = Term → Set


infix 50 _⟦_⟧
_⟦_⟧ : Assign → Formula → Set
σ ⟦ TAtomic x ⟧ = σ x
σ ⟦ TTrue     ⟧ = ⊤
σ ⟦ TFalse    ⟧ = ⊥
σ ⟦ TAnd a b  ⟧ = σ ⟦ a ⟧ ∧ σ ⟦ b ⟧
σ ⟦ TOr  a b  ⟧ = σ ⟦ a ⟧ ∨ σ ⟦ b ⟧
σ ⟦ TImp a b  ⟧ = σ ⟦ a ⟧ → σ ⟦ b ⟧


all⊤ : Assign → List Term → Set
all⊤ σ []      = ⊤
all⊤ σ (x ∷ l) = (σ x) ∧ (all⊤ σ l)


_∷≡_ : Term → List Term → List Term
x ∷≡ []      = x ∷ []
x ∷≡ (y ∷ l) with x ≟-Term y
... | yes p = y ∷ l
... | no ¬p = y ∷ (x ∷≡ l)


all⊤∷≡ : ∀ {σ t l} → σ t → all⊤ σ l → all⊤ σ (t ∷≡ l)
all⊤∷≡ {σ} {t} {[]}    σt all⊤l = σt ∧i tt
all⊤∷≡ {σ} {t} {x ∷ l} σt all⊤l with t ≟-Term x
...                                  | yes p = all⊤l
all⊤∷≡ {σ} {t} {x ∷ l} σt (x₁ ∧i x₂) | no ¬p = x₁ ∧i all⊤∷≡ σt x₂


data _∈_ : Term → List Term → Set where
  here : ∀ {t r} → t ∈ (t ∷ r)
  there : ∀ {t h r} → t ∈ r → t ∈ (h ∷ r)


Dec : Set → Set
Dec P = P ∨ ¬ P


_∈?_ : (t : Term) → (l : List Term) → Dec (t ∈ l)
t ∈? []       = ∨⇀ (λ ())
t ∈? (x ∷ l)  with t ≟-Term x
.x ∈? (x ∷ l) | yes refl = ↼∨ here
...           | no ¬p with t ∈? l
...                   | ↼∨ p = ↼∨ (there p)
...                   | ∨⇀ p = ∨⇀ (λ t∈xl → ¬∈ ¬p p t∈xl)
  where
  ¬∈ : ∀ {t x l} → ¬ (t ≡ x) → ¬ (t ∈ l) → ¬ (t ∈ (x ∷ l))
  ¬∈ neq nin here        = neq refl
  ¬∈ neq nin (there tin) = nin tin


all⊤∈ : ∀ {σ l t} → all⊤ σ l → t ∈ l → σ t
all⊤∈ (x ∧i x₁) here = x
all⊤∈ (x ∧i x₁) (there mem) = all⊤∈ x₁ mem


¿_ = Maybe


¿↼∨ : ∀ {A B : Set} → A ∨ B → ¿ A
¿↼∨ (↼∨ x) = just x
¿↼∨ (∨⇀ x) = nothing


Reduce : ∀ {A B : Set} → (a : ¿ A) → (A → B) → ¿ B
Reduce (just x) f = just (f x)
Reduce nothing  f = nothing


⟨_∨_⟩_ : ∀ {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
⟨ f ∨ g ⟩ ↼∨ x = f x
⟨ f ∨ g ⟩ ∨⇀ x = g x


⇒ : ∀ σ f Γ h → (∀ Γ' → ¿ (all⊤ σ Γ' → σ ⟦ f ⟧)) → ¿ (all⊤ σ Γ → σ ⟦ h ⟧ → σ ⟦ f ⟧)
⇒ σ f Γ (TAtomic x) cont = Reduce (cont (x ∷≡ Γ)) (λ k all⊤ σh → k (all⊤∷≡ σh all⊤))
⇒ σ f Γ TTrue       cont = Reduce (cont Γ) (λ k all⊤ σh → k all⊤)
⇒ σ f Γ TFalse      cont = just (λ all⊤ bot → ⊥-elim bot)
⇒ σ f Γ (TAnd h h₁) cont = Reduce (⇒ σ (TImp h₁ f) Γ h (λ Γ' → Reduce (⇒ σ f Γ' h₁ cont) (λ k all⊤ σh → k all⊤ σh))) (λ k all⊤ σh → k all⊤ (p₁ σh) (p₂ σh))
⇒ σ f Γ (TOr  h h₁) cont with ⇒ σ f Γ h cont | ⇒ σ f Γ h₁ cont
...                         | just res       | just res₁       = just (λ all⊤ σh → ⟨ res all⊤ ∨ res₁ all⊤ ⟩ σh)
...                         | _              | _               = nothing
⇒ σ f Γ (TImp _ _)  cont = Reduce (cont Γ) (λ k all⊤ σh → k all⊤)


⇐ : ∀ σ Γ f → ¿ (all⊤ σ Γ → σ ⟦ f ⟧)
⇐ σ Γ (TAtomic x) = Reduce (¿↼∨ (x ∈? Γ)) ∈all⊤
  where
  ∈all⊤ : ∀ {x Γ σ} → x ∈ Γ → all⊤ σ Γ → σ x
  ∈all⊤ here        (x₁ ∧i x₂) = x₁
  ∈all⊤ (there x∈Γ) (x₁ ∧i x₂) = ∈all⊤ x∈Γ x₂
⇐ σ Γ TTrue       = just (λ _ → tt)
⇐ σ Γ TFalse      = nothing
⇐ σ Γ (TAnd f f₁) with ⇐ σ Γ f  | ⇐ σ Γ f₁
...                  | just res | just res₁ = just (λ a → res a ∧i res₁ a)
...                  | _        | _         = nothing
⇐ σ Γ (TOr  f f₁) with ⇐ σ Γ f  | ⇐ σ Γ f₁
...                  | just res | _        = just (λ a → ↼∨ (res a))
...                  | _        | just res = just (λ a → ∨⇀ (res a))
...                  | _        | _        = nothing
⇐ σ Γ (TImp a b)  = ⇒ σ b Γ a (λ Γ' → ⇐ σ Γ' b)


mutual

  reifyable : Term → Set
  reifyable (var x args) = ⊤
  reifyable (con c args) = ⊤
  reifyable (def f args)
      with f ≟-Name quote ⊤
  ... | yes p = ⊤
  ... | no ¬p
      with f ≟-Name quote ⊥
  ... | yes q = ⊤
  ... | no ¬q
      with f ≟-Name quote _∨_
  ... | yes r = reifyable2args args
  ... | no ¬r
      with f ≟-Name quote _∧_
  ... | yes s = reifyable2args args
  ... | no ¬s = ⊤
  reifyable (lam v t)    = ⊤
  reifyable (pi (arg v r (el s t)) (el s₁ t₁)) = reifyable t × reifyable t₁
  reifyable (sort x)     = ⊤
  reifyable unknown      = ⊥

  reifyable2args : List (Arg Term) → Set
  reifyable2args [] = ⊥
  reifyable2args (x ∷ []) = ⊥
  reifyable2args (x ∷ x₁ ∷ []) = ⊥
  reifyable2args (x ∷ x₁ ∷ x₂ ∷ []) = ⊥
  reifyable2args (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args) = ⊥
  reifyable2args (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ x₃ ∷ []) = reifyable x₂ × reifyable x₃


mutual

  reify : (t : Term) → reifyable t → Formula
  reify (var x args) r = TAtomic (var x args)
  reify (con c args) r = TAtomic (con c args)
  reify (def f args) r
      with f ≟-Name quote ⊤
  ... | yes p = TTrue
  ... | no ¬p
      with f ≟-Name quote ⊥
  ... | yes q = TFalse
  ... | no ¬q
      with f ≟-Name quote _∨_
  ... | yes s = reify2args TOr args r
  ... | no ¬s
      with f ≟-Name quote _∧_
  ... | yes t = reify2args TAnd args r
  ... | no ¬t = TAtomic (def f args)
  reify (lam v t)    r = TAtomic (lam v t)
  reify (pi (arg v r (el s t)) (el s₁ t₁)) (proj₁ , proj₂) = TImp (reify t proj₁) (reify t₁ proj₂)
  reify (sort x)     r = TAtomic (sort x)
  reify unknown ()

  reify2args : (Formula → Formula → Formula) → (args : List (Arg Term)) → (reifyable2args args) → Formula
  reify2args f [] ()
  reify2args f (x ∷ []) ()
  reify2args f (x ∷ x₁ ∷ []) ()
  reify2args f (x ∷ x₁ ∷ x₂ ∷ []) ()
  reify2args f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args) ()
  reify2args f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ x₃ ∷ []) (proj₁ , proj₂) = f (reify x₂ proj₁) (reify x₃ proj₂)


autoreify : (t : Term) → {pf : reifyable t} → Formula
autoreify t {pf} = reify t pf


f : ∀ {x y z : ℕ} → (x < y ∧ y > z) ∨ (y > z ∧ x < suc y) → y > z ∧ (x < y ∨ x < suc y)
f = quoteGoal g in (let x = ⇐ (λ _ → ⊥) [] (autoreify g) in {!!})


f' : ∀ {x : ℕ} → x < x → x < x
f' = quoteGoal g in (let x = ⇐ (λ _ → ⊥) [] (autoreify g) in {!!})


isJust : ∀ {A : Set} → ¿ A → Set
isJust (just x) = ⊤
isJust nothing  = ⊥


fromJust : ∀ {A : Set} → (a : ¿ A) → {i : isJust a} → A
fromJust (just x) {i}  = x
fromJust nothing  {()}


tauto1 : ⊤
tauto1 = quoteGoal g in (fromJust (⇐ (λ _ → ⊥) [] (autoreify g)) _)


tauto2 : ⊥ → ⊥
tauto2 = quoteGoal g in (fromJust (⇐ (λ _ → ⊥) [] (autoreify g)) _)


tauto3 : (⊤ → ⊥) → (⊤ → ⊤)
tauto3 = quoteGoal g in (fromJust (⇐ (λ _ → ⊥) [] (autoreify g)) _)


mkσ : List (Set × Term) → Assign
mkσ = go (λ _ → ⊥)
  where
  go : Assign → List (Set × Term) → Assign
  go σ []                    t = σ t
  go σ ((proj₁ , proj₂) ∷ l) t with proj₂ ≟-Term t
  ... | yes p = proj₁
  ... | no ¬p = σ t


g : (⊤ → 2 ≡ 2) → ⊤
g =
  let σ = mkσ [ ((2 ≡ 2) , quoteTerm (2 ≡ 2)) ] in
  quoteGoal g in (fromJust (⇐ σ [] (autoreify g))) _
