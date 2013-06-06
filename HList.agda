module HList where

open import Data.Bool
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Nat

TList = List Set

data HList : TList → Set₁ where
  []  : HList []
  _∷_ : ∀ {A ts} → A → HList ts → HList (A ∷ ts)

ts : TList
ts = Bool  ∷ ℕ ∷ Bool ∷ []

xs : HList ts
xs = false ∷ 5 ∷ true ∷ []

data _∈_ : Set → TList → Set₁ where
  here : ∀ {t ts} → t ∈ (t ∷ ts)
  next : ∀ {t x ts} → t ∈ ts → t ∈ (x ∷ ts)

_!_ : ∀ {t ts} → HList ts → t ∈ ts → t
(x ∷ xs) ! here     = x
(x ∷ xs) ! (next i) = xs ! i

f : Bool
f = xs ! here

t : Bool
t = xs ! (next (next here))

nth : (l : TList) → Fin (length l) → Set
nth []      ()
nth (t ∷ l) zero    = t
nth (t ∷ l) (suc f) = nth l f

get : ∀ {t : TList} → HList t → (n : Fin (length t)) → nth t n
get []      ()
get (x ∷ l) zero    = x
get (x ∷ l) (suc n) = get l n

n : ℕ
n = get xs (suc zero)
