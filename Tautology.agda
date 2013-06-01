module Tautology where

open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level
open import Reflection
open import Relation.Nullary

data _∨_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  ∨l : A → A ∨ B
  ∨r : B → A ∨ B

data _∧_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _∧i_ : A → B → A ∧ B

data Tauto : Set where
  TTrue : Tauto
  TAnd  : (a : Tauto) → (b : Tauto) → Tauto
  TOr   : (a : Tauto) → (b : Tauto) → Tauto
  TImp  : (a : Tauto) → (b : Tauto) → Tauto

⟦_⟧ : Tauto → Set
⟦ TTrue ⟧    = ⊤
⟦ TAnd a b ⟧ = ⟦ a ⟧ ∧ ⟦ b ⟧
⟦ TOr  a b ⟧ = ⟦ a ⟧ ∨ ⟦ b ⟧
⟦ TImp a b ⟧ = ⟦ a ⟧ → ⟦ b ⟧

tautoTrue : ∀ t → ⟦ t ⟧
tautoTrue TTrue      = tt
tautoTrue (TAnd a b) = tautoTrue a ∧i tautoTrue b
tautoTrue (TOr  a b) = ∨l (tautoTrue a)
tautoTrue (TImp a b) = λ _ → tautoTrue b

mutual

  reifyable : Term → Set
  reifyable (var x args) = ⊥
  reifyable (con c args) = ⊥
  reifyable (def f args) with f ≟-Name quote ⊤ | f ≟-Name quote _∨_ | f ≟-Name quote _∧_
  ...                       | yes _            | no _               | no _               = ⊤
  ...                       | no _             | yes _              | no _               = reifyable2args args
  ...                       | no _             | no _               | yes _              = reifyable2args args
  ...                       | _                | _                  | _                  = ⊥
  reifyable (lam v t)    = ⊥
  reifyable (pi (arg v r (el s t)) (el s₁ t₁)) = reifyable t × reifyable t₁
  reifyable (sort x)     = ⊥
  reifyable unknown      = ⊥

  reifyable2args : List (Arg Term) → Set
  reifyable2args [] = ⊥
  reifyable2args (x ∷ []) = ⊥
  reifyable2args (x ∷ x₁ ∷ []) = ⊥
  reifyable2args (x ∷ x₁ ∷ x₂ ∷ []) = ⊥
  reifyable2args (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args) = ⊥
  reifyable2args (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ x₃ ∷ []) = reifyable x₂ × reifyable x₃

mutual

  reify : (t : Term) → reifyable t → Tauto
  reify (var x args) ()
  reify (con c args) ()
  reify (def f args) pf with f ≟-Name quote ⊤ | f ≟-Name quote _∨_ | f ≟-Name quote _∧_
  reify (def f args) () | yes p | yes p₁ | z
  reify (def f args) () | yes p | no ¬p | yes p₁
  reify (def f args) pf | yes p | no ¬p | no ¬p₁ = TTrue
  reify (def f args) () | no ¬p | yes p | yes p₁
  reify (def f args) pf | no ¬p | yes p | no ¬p₁ = reify2args TOr args pf
  reify (def f args) pf | no ¬p | no ¬p₁ | yes p = reify2args TAnd args pf
  reify (def f args) () | no ¬p | no ¬p₁ | no ¬p₂
  reify (lam v t) ()
  reify (pi (arg v r (el s t)) (el s₁ t₁)) (proj₁ , proj₂) = TImp (reify t proj₁) (reify t₁ proj₂)
  reify (sort x) ()
  reify unknown ()

  reify2args : (Tauto → Tauto → Tauto) → (args : List (Arg Term)) → (reifyable2args args) → Tauto
  reify2args f [] ()
  reify2args f (x ∷ []) ()
  reify2args f (x ∷ x₁ ∷ []) ()
  reify2args f (x ∷ x₁ ∷ x₂ ∷ []) ()
  reify2args f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args) ()
  reify2args f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ x₃ ∷ []) (proj₁ , proj₂) = f (reify x₂ proj₁) (reify x₃ proj₂)

autoreify : (t : Term) → {pf : reifyable t} → Tauto
autoreify t {pf} = reify t pf

t : ⊤
t    = quoteGoal g in tautoTrue (autoreify g)

tand : ⊤ ∨ ⊤
tand = quoteGoal g in tautoTrue (autoreify g)

tor : ⊤ ∨ ⊤
tor  = quoteGoal g in tautoTrue (autoreify g)

timp : ⊤ → ⊤
timp = quoteGoal g in tautoTrue (autoreify g)

t? : (⊤ ∧ ⊤) → (⊤ ∨ (⊤ ∧ (⊤ → ⊤)))
t?   = quoteGoal g in tautoTrue (autoreify g)
