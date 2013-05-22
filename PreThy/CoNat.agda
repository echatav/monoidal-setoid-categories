module PreThy.CoNat where

open import Bundle.Prelude

data CoNat : Set₀ where
  zero : CoNat
  succ : ∞ CoNat → CoNat

ω : CoNat
ω = succ (♯ ω)
