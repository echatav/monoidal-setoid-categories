{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd      as C
import 1-CatThy.Obj.Trm      as C
import 1-CatThy.Str.Mon.Core as C

module 1-CatThy.Str.Mon.Car.IsMon.L-Coh-Tri
  (A   : C.Cat)
  (trm : C.O.Trm A)
  (prd : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

import 1-CatThy.Str.Mon.Car.One
import 1-CatThy.Str.Mon.Car.Tensor
import 1-CatThy.Str.Mon.Car.Lambda
import 1-CatThy.Str.Mon.Car.Rho
import 1-CatThy.Str.Mon.Car.Alpha
import 1-CatThy.Str.Mon.Car.Alpha.Core

open 1-CatThy.Str.Mon.Car.One        A trm
open 1-CatThy.Str.Mon.Car.Tensor     A     prd
open 1-CatThy.Str.Mon.Car.Lambda     A trm prd
open 1-CatThy.Str.Mon.Car.Rho        A trm prd
open 1-CatThy.Str.Mon.Car.Alpha      A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.Core A trm prd

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

l-coh-tri : {a₁ a₂ : c.obj} →
  S.[ c.* ]
          C.h⇒ ×-⇒₁ S.· (c.idn , C.com (C.I.fwd λ′) a₂)
      c.∘ C.com (C.I.fwd α) ((C.o⇒ (C.M₁.idn A) a₁ , one) , a₂)
    ≃ C.h⇒ ×-⇒₁ S.· (C.com (C.I.fwd ρ) a₁ , c.idn)
l-coh-tri = let open S.Eq c.* in
  proof

            o.⟨ c.idn c.∘ fst→ , thd→ ⟩
        c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩

  {- left identity law -}
  ↝⟨ c.cmp* S.⩪ (o.⟨,⟩* S.⩪ (c.l-idn₁ , S.idn c.*) , S.idn c.*) ⟩

            o.⟨ fst→ , thd→ ⟩
        c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↝⟨ o.l-⟨,⟩-∘ ⟩

            o.⟨ fst→ c.∘  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
              , thd→ c.∘  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩

  {- β-reduction -}
  ↝⟨ o.⟨,⟩* S.⩪
     ( o.l-π₁-β
     , S.[ c.* ]
           (S.[ c.* ]
                o.l-π₂-β
              ∘ c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β))
         ∘  c.l-cmp ) ⟩

            o.⟨ fst← , thd← ⟩

  {- left identity law -}
  ↜⟨ o.⟨,⟩* S.⩪ (S.idn c.* , c.l-idn₁) ⟩

            o.⟨ fst← , c.idn c.∘ thd← ⟩

  ∎
