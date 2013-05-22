{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.One (A : C.Cat) (φ : C.O.Trm A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

one : C.obj A
one = C.O.Trm.⊤ φ
