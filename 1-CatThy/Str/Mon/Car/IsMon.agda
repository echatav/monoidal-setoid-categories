{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd      as C
import 1-CatThy.Obj.Trm      as C
import 1-CatThy.Str.Mon.Core as C

module 1-CatThy.Str.Mon.Car.IsMon
  (A   : C.Cat)
  (trm : C.O.Trm A)
  (prd : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Str.Mon.Car.One
import 1-CatThy.Str.Mon.Car.Tensor
import 1-CatThy.Str.Mon.Car.Lambda
import 1-CatThy.Str.Mon.Car.Rho
import 1-CatThy.Str.Mon.Car.Alpha
import 1-CatThy.Str.Mon.Car.IsMon.L-Coh-Pnt
import 1-CatThy.Str.Mon.Car.IsMon.L-Coh-Tri

open 1-CatThy.Str.Mon.Car.One             A trm
open 1-CatThy.Str.Mon.Car.Tensor          A     prd
open 1-CatThy.Str.Mon.Car.Lambda          A trm prd
open 1-CatThy.Str.Mon.Car.Rho             A trm prd
open 1-CatThy.Str.Mon.Car.Alpha           A trm prd
open 1-CatThy.Str.Mon.Car.IsMon.L-Coh-Pnt A trm prd
open 1-CatThy.Str.Mon.Car.IsMon.L-Coh-Tri A trm prd

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

isMon : C.IsMon A one ×-⇒₁ λ′ ρ α
isMon = record
  { l-coh-pnt = l-coh-pnt
  ; l-coh-tri = l-coh-tri
  }
