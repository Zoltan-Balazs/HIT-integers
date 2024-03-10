{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude renaming (congS to ap)
open import Cubical.Data.Nat hiding (_+_)

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

-- Inductive type definition of ℤ
data ℤω : Set where
    zero : ℤω
    strpos : ℕ → ℤω
    strneg : ℕ → ℤω

succℤω : ℤω → ℤω
succℤω zero             = strpos zero
succℤω (strpos n)       = strpos (suc n)
succℤω (strneg zero)    = zero
succℤω (strneg (suc n)) = strneg n

predℤω : ℤω → ℤω
predℤω zero             = strneg zero
predℤω (strpos zero)    = zero
predℤω (strpos (suc n)) = strpos n
predℤω (strneg n)       = strneg (suc n)

secℤω : (z : ℤω) → predℤω (succℤω z) ≡ z
secℤω zero             = refl
secℤω (strpos n)       = refl
secℤω (strneg zero)    = refl
secℤω (strneg (suc n)) = refl

retℤω : (z : ℤω) → succℤω (predℤω z) ≡ z
retℤω zero             = refl
retℤω (strpos zero)    = refl
retℤω (strpos (suc n)) = refl
retℤω (strneg n)       = refl

cohℤω : (z : ℤω) → ap succℤω (secℤω z) ≡ retℤω (succℤω z)
cohℤω zero             = refl
cohℤω (strpos n)       = refl
cohℤω (strneg zero)    = refl
cohℤω (strneg (suc n)) = refl
