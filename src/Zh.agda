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

-- Properties needed for HIT Integers to form a Commutative Ring
-- Is it an Abelian Group under addition?
ℤₕ-add-is-assoc : (a : ℤₕ) → (b : ℤₕ) → (c : ℤₕ) → (a + b) + c ≡ a + (b + c)
ℤₕ-add-is-assoc a b c = {!   !}

-- ℤₕ-add-has-id-elem :
-- ℤₕ-add-has-inv-elem :

ℤₕ-add-is-comm : (a : ℤₕ) → (b : ℤₕ) → a + b ≡ b + a
ℤₕ-add-is-comm a b = {!   !}

-- Is it a Monoid under multiplication?
ℤₕ-mul-is-assoc : (a : ℤₕ) → (b : ℤₕ) → (c : ℤₕ) → (a * b) * c ≡ a * (b * c)
ℤₕ-mul-is-assoc a b c = {!   !}

-- ℤₕ-mul-has-id-elem :

-- Is this multiplication distributive over addition?
ℤₕ-mul-is-dist-to-add : (a : ℤₕ) → (b : ℤₕ) → (c : ℤₕ) → a * (b + c) ≡ (a * b) + (a * c)
ℤₕ-mul-is-dist-to-add a b c = {!   !}

-- Is multiplication commutative?
ℤₕ-mul-is-comm : (a : ℤₕ) → (b : ℤₕ) → a * b ≡ b * a
ℤₕ-mul-is-comm a b = {!   !}

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

-- Conversions between the two type definitions
ℤₕ-to-ℤω : ℤₕ → ℤω
ℤₕ-to-ℤω zero        = zero
ℤₕ-to-ℤω (succ n)    = succℤω (ℤₕ-to-ℤω n)
ℤₕ-to-ℤω (pred n)    = predℤω (ℤₕ-to-ℤω n)
ℤₕ-to-ℤω (sec n i)   = secℤω (ℤₕ-to-ℤω n) i
ℤₕ-to-ℤω (ret n i)   = retℤω (ℤₕ-to-ℤω n) i
ℤₕ-to-ℤω (coh n i j) = cohℤω (ℤₕ-to-ℤω n) i j

ℤω-to-ℤₕ : ℤω → ℤₕ
ℤω-to-ℤₕ zero             = zero
ℤω-to-ℤₕ (strpos zero)    = succ zero
ℤω-to-ℤₕ (strpos (suc n)) = succ (ℤω-to-ℤₕ (strpos n))
ℤω-to-ℤₕ (strneg zero)    = pred zero
ℤω-to-ℤₕ (strneg (suc n)) = pred (ℤω-to-ℤₕ (strneg n))
