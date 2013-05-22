{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Alpha.IsIso
  (A   : C.Cat)
  (trm : C.O.Trm A)
  (prd : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Str.Mon.Car.One    as CM
import 1-CatThy.Str.Mon.Car.Tensor as CM

import 1-CatThy.Str.Mon.Car.Alpha.Core
import 1-CatThy.Str.Mon.Car.Alpha.Fwd
import 1-CatThy.Str.Mon.Car.Alpha.Bwd
import 1-CatThy.Str.Mon.Car.Alpha.IsIso.L-Fwd
import 1-CatThy.Str.Mon.Car.Alpha.IsIso.L-Bwd

open 1-CatThy.Str.Mon.Car.Alpha.Core        A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.Fwd         A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.Bwd         A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.IsIso.L-Fwd A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.IsIso.L-Bwd A trm prd

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

  one : C.obj A
  one = CM.one  A trm

  ⊗ : A C.× A C.⇒₁ A
  ⊗ = CM.×-⇒₁ A prd

isIso : C.I.IsIso (C.M₁.cat ((A C.× A) C.× A) A) fwd bwd
isIso = record
  { l-fwd = l-fwd
  ; l-bwd = l-bwd
  }
