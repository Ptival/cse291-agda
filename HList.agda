module HList where

  data Bool : Set where
    true  : Bool
    false : Bool

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  infixr 40 _::_ _:::_

  data TList : Set₁ where
    []  : TList
    _:::_ : (t : Set) → TList → TList

  data HList : TList → Set₁ where
    []   : HList []
    _::_ : ∀ {A ts} → A → HList ts → HList (A ::: ts)

  ts = Bool ::: ℕ ::: Bool ::: []

  xs : HList ts
  xs = false :: 5 :: true :: []

  data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} → Fin n → Fin (suc n)

  data _∈_ : Set → TList → Set₁ where
    here : ∀ {t ts} → t ∈ (t ::: ts)
    next : ∀ {t x ts} → t ∈ ts → t ∈ (x ::: ts)

  _!_ : ∀ {t ts} → HList ts → t ∈ ts → t
  [] ! ()
  (x :: xs) ! here     = x
  (x :: xs) ! (next i) = xs ! i

  f : Bool
  f = xs ! here

  t : Bool
  t = xs ! (next (next here))

  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)

  TListlen : TList → ℕ
  TListlen [] = 0
  TListlen (t ::: l) = 1 + TListlen l

  nth : (l : TList) → Fin (TListlen l) → Set
  nth [] ()
  nth (t ::: l) zero = t
  nth (t ::: l) (suc f) = nth l f

  get : ∀ {t : TList} → (l : HList t) → (n : Fin (TListlen t)) → nth t n
  get []       ()
  get (x :: l) zero    = x
  get (x :: l) (suc n) = get l n

  n : ℕ
  n = get xs (suc zero)
