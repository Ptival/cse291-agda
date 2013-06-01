module Vector where

open import Data.Nat

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n : ℕ} → (hd : A) → (tl : Vec A n) → Vec A (suc n)

_⊹_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
[]       ⊹ y = y
(hd ∷ x) ⊹ y = hd ∷ (x ⊹ y)
