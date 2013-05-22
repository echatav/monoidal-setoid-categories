{-# OPTIONS --type-in-type #-}
module PreThy.Boot.Map where

infixr 0 _⇒_

_⇒_ : Set → Set → Set
A₁ ⇒ A₂ = A₁ → A₂
