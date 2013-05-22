module Prelude.Lvl where

infixl 6 _⊔_

postulate
  Lvl : Set
  z   : Lvl
  s   : Lvl → Lvl
  _⊔_ : Lvl → Lvl → Lvl

{-# BUILTIN LEVEL     Lvl #-}
{-# BUILTIN LEVELZERO z   #-}
{-# BUILTIN LEVELSUC  s   #-}
{-# BUILTIN LEVELMAX  _⊔_ #-}

record ↑ {i₁} i₂ (A : Set i₁) : Set (i₁ ⊔ i₂) where
  constructor lft
  field lwr : A

open ↑ public
