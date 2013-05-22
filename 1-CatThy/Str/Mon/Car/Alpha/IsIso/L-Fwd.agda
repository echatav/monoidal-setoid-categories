{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Alpha.IsIso.L-Fwd
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

open 1-CatThy.Str.Mon.Car.Alpha.Core A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.Fwd  A trm prd
open 1-CatThy.Str.Mon.Car.Alpha.Bwd  A trm prd

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

  one : C.obj A
  one = CM.one  A trm

  ⊗ : A C.× A C.⇒₁ A
  ⊗ = CM.×-⇒₁ A prd

l-fwd : {a : C.obj ((A C.× A) C.× A)} →
  S.[ c.* ]
      C.com (C.[ C.M₁.cat ((A C.× A) C.× A) A ] bwd ∘ fwd) a
    ≃ C.com
        (C.idn (C.M₁.cat ((A C.× A) C.× A) A)
        {⊗ C.M₁.∘ C.⟨ ⊗ × C.M₁.idn A ⟩}) a
l-fwd {a} = let open S.Eq c.* in
  proof

            o.⟨ o.⟨ fst→ , snd→ ⟩ , thd→ ⟩
        c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↝⟨ S.[ c.* ] o.⟨,⟩* S.⩪ (o.l-⟨,⟩-∘ , S.idn c.*) ∘ o.l-⟨,⟩-∘ ⟩

            o.⟨ o.⟨ fst→ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
                  , snd→ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩
              ,     thd→ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩

  {- calculation -}
  ↭

            o.⟨ o.⟨ (o.π₁         ) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
                  , (o.π₁ c.∘ o.π₂) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩
              ,     (o.π₂ c.∘ o.π₂) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩

  {- associativity -}
  ↝⟨ o.⟨,⟩* S.⩪ (o.⟨,⟩* S.⩪ (S.idn c.* , c.l-cmp) , c.l-cmp) ⟩

            o.⟨ o.⟨ o.π₁           c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
                  , o.π₁ c.∘ (o.π₂ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) ⟩
              ,     o.π₂ c.∘ (o.π₂ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) ⟩

  {- β-reduction -}
  ↝⟨ o.⟨,⟩* S.⩪
     ( o.⟨,⟩* S.⩪
       ( o.l-π₁-β
       , S.[ c.* ] o.l-π₁-β ∘ c.cmp* S.⩪ ( S.idn c.* , o.l-π₂-β) )
     , S.[ c.* ] o.l-π₂-β ∘ c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ) ⟩

            o.⟨ o.⟨ fst← , snd← ⟩ , thd← ⟩

  {- calculation -}
  ↭

            o.⟨ o.⟨ o.π₁ c.∘ o.π₁ , o.π₂ c.∘ o.π₁ ⟩ , o.π₂ ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↜⟨ o.⟨,⟩* S.⩪ (o.l-⟨,⟩-∘ , S.idn c.*) ⟩

            o.⟨ o.⟨ o.π₁ , o.π₂ ⟩ c.∘ o.π₁ , o.π₂ ⟩

  {- η-contraction; left identity law -}
  ↝⟨ o.⟨,⟩* S.⩪
     ( S.[ c.* ] c.l-idn₁ ∘ c.cmp* S.⩪ (o.l-⟨,⟩-η , S.idn c.*)
     , S.idn c.* ) ⟩

            o.⟨ o.π₁ , o.π₂ ⟩

  {- η-contraction -}
  ↝⟨ o.l-⟨,⟩-η ⟩

            c.idn

  ∎
