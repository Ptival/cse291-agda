module View where

open import Data.List

data SnocView {A : Set} : List A → Set where
  `[]  : SnocView []
  _`∷_ : (xs : List A) → (x : A) → SnocView (xs ++ (x ∷ []))

snocview : {A : Set} → (xs : List A) → SnocView xs
snocview [] = `[]
snocview (hd ∷ xs)                with snocview xs
snocview (hd ∷ .[])               | `[]     = [] `∷ hd
snocview (hd ∷ .(ys ++ (y ∷ []))) | ys `∷ y = (hd ∷ ys) `∷ y

rotateRight : {A : Set} → List A → List A
rotateRight xs                with snocview xs
rotateRight .[]               | `[]     = []
rotateRight .(ys ++ (y ∷ [])) | ys `∷ y = y ∷ ys
