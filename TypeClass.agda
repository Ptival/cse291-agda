module TypeClass where

open import Data.Bool renaming (_≟_ to _B≟_)
open import Data.Maybe
open import Data.String using (String) renaming (_≟_ to _S≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

record EqDec (T : Set) : Set where
  field _≟_ : ∀ (x y : T) → Dec (x ≡ y)

open EqDec ⦃...⦄

EqDecString : EqDec String
EqDecString = record { _≟_ = _S≟_ }

EqDecBool : EqDec Bool
EqDecBool = record { _≟_ = _B≟_ }

congjust : ∀ {T : Set} {x y : T} → (_≡_ {_} {Maybe T} (just x) (just y)) → x ≡ y
congjust refl = refl

just≢nothing : ∀ {T : Set} {x : T} → _≢_ {_} {Maybe T} (just x) nothing
just≢nothing ()

nothing≢just : ∀ {T : Set} {x : T} → _≢_ {_} {Maybe T} nothing (just x)
nothing≢just ()

eqdecmaybe : ∀ {T : Set} ⦃ ET : EqDec T ⦄ (x y : Maybe T) → Dec (x ≡ y)
eqdecmaybe (just x) (just y) with x ≟ y
eqdecmaybe (just x) (just .x) | yes refl = yes refl
eqdecmaybe (just x) (just y)  | no  neq  = no (λ J → neq (congjust J))
eqdecmaybe (just x) nothing   = no just≢nothing
eqdecmaybe nothing  (just x)  = no nothing≢just
eqdecmaybe nothing  nothing   = yes refl

EqDecMaybe : ∀ {T} ⦃ ET : EqDec T ⦄ → EqDec (Maybe T)
EqDecMaybe {ET} = record { _≟_ = eqdecmaybe {ET} }

eqdecmaybebool : ∀ (x y : Maybe Bool) → Dec (x ≡ y)
eqdecmaybebool = _≟_
  where help = EqDecMaybe ⦃ EqDecBool ⦄

f : ∀ (x y : Bool) → Dec(x ≡ y)
f x y = x ≟ y

g : ∀ (x y : String) → Dec(x ≡ y)
g x y = x ≟ y
