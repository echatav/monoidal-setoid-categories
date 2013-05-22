{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Alpha.Core
  (A   : C.Cat)
  (trm : C.O.Trm A)
  (prd : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

-- left nested projections
fst← : {a₁ a₂ a₃ : c.obj} → c.hom ((a₁ o.× a₂) o.× a₃) a₁
fst← = o.π₁ c.∘ o.π₁

snd← : {a₁ a₂ a₃ : c.obj} → c.hom ((a₁ o.× a₂) o.× a₃) a₂
snd← = o.π₂ c.∘ o.π₁

thd← : {a₁ a₂ a₃ : c.obj} → c.hom ((a₁ o.× a₂) o.× a₃) a₃
thd← = o.π₂

-- right nested projections
fst→ : {a₁ a₂ a₃ : c.obj} → c.hom (a₁ o.× (a₂ o.× a₃)) a₁
fst→ = o.π₁

snd→ : {a₁ a₂ a₃ : c.obj} → c.hom (a₁ o.× (a₂ o.× a₃)) a₂
snd→ = o.π₁ c.∘ o.π₂

thd→ : {a₁ a₂ a₃ : c.obj} → c.hom (a₁ o.× (a₂ o.× a₃)) a₃
thd→ = o.π₂ c.∘ o.π₂
