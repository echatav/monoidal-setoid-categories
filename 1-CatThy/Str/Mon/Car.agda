{-# OPTIONS --type-in-type #-}
module 1-CatThy.Str.Mon.Car where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd      as C
import 1-CatThy.Obj.Trm      as C
import 1-CatThy.Str.Mon.Core as C

open import 1-CatThy.Str.Mon.Car.One
open import 1-CatThy.Str.Mon.Car.Tensor
open import 1-CatThy.Str.Mon.Car.Lambda
open import 1-CatThy.Str.Mon.Car.Rho
open import 1-CatThy.Str.Mon.Car.Alpha
open import 1-CatThy.Str.Mon.Car.IsMon

import 1-CatThy.Str.Mon.Car.Alpha.Core

record CarMon (A : C.Cat) : Set where
  field
    trm : C.O.Trm A
    prd : C.O.Prd A

  open 1-CatThy.Str.Mon.Car.Alpha.Core A trm prd

  mon : C.Mon A
  mon = record
    { one   = one   A trm
    ; ⊗     = ×-⇒₁  A     prd
    ; λ′    = λ′    A trm prd
    ; ρ     = ρ     A trm prd
    ; α     = α     A trm prd
    ; isMon = isMon A trm prd
    }

  open C.Mon   mon public
  open C.O.Trm trm public
  open C.O.Prd prd public

open CarMon public
