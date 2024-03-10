{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude renaming (congS to ap)

-- Higher inductive type definition of ℤ
data ℤₕ : Set where
    zero : ℤₕ
    succ : ℤₕ → ℤₕ
    pred : ℤₕ → ℤₕ
    sec : (z : ℤₕ) → pred (succ z) ≡ z
    ret : (z : ℤₕ) → succ (pred z) ≡ z
    coh : (z : ℤₕ) → ap succ (sec z) ≡ ret (succ z)

-- Operations of HIT Integers
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℤₕ → ℤₕ → ℤₕ
zero        + b = b
succ a      + b = succ (a + b)
pred a      + b = pred (a + b)
sec a i     + b = sec (a + b) i
ret a i     + b = ret (a + b) i
coh a i₁ i₂ + b = coh (a + b) i₁ i₂

_-_ : ℤₕ → ℤₕ → ℤₕ
a - zero        = a
a - succ b      = pred (a - b)
a - pred b      = succ (a - b)
a - sec b i     = ret (a - b) i
a - ret b i     = sec (a - b) i
a - coh b i₁ i₂ = {!   !}

_*_ : ℤₕ → ℤₕ → ℤₕ
zero * b        = zero
succ a * b      = a * b + b
pred a * b      = a * b - b
sec a i * b     = {!   !}
ret a i * b     = {!   !}
coh a i₁ i₂ * b = {!   !}