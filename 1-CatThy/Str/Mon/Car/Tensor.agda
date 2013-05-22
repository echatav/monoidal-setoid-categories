{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C

module 1-CatThy.Str.Mon.Car.Tensor (A : C.Cat) (φ : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

×-⇒₁ : A C.× A C.⇒₁ A
×-⇒₁ = C.O.×-⇒₁ A φ
