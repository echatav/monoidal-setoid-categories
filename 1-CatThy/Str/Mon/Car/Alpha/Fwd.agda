{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Alpha.Fwd
  (A   : C.Cat)
  (trm : C.O.Trm A)
  (prd : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Str.Mon.Car.One    as CM
import 1-CatThy.Str.Mon.Car.Tensor as CM

import 1-CatThy.Str.Mon.Car.Alpha.Core
open   1-CatThy.Str.Mon.Car.Alpha.Core A trm prd

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

  one : C.obj A
  one = CM.one  A trm

  ⊗ : A C.× A C.⇒₁ A
  ⊗ = CM.×-⇒₁ A prd

fwd :   (⊗ C.M₁.∘ C.⟨ ⊗ × C.M₁.idn A ⟩)
  C.⇒₂ ((⊗ C.M₁.∘ C.⟨ C.M₁.idn A × ⊗ ⟩) C.M₁.∘ C.×-α A A A)
fwd = record
  { com   = λ _ → o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
  ; l-nat = λ { {_} {_} {(m₁ , m₂) , m₃} → let open S.Eq c.* in
      proof

                o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩
            c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩

      {- calculation -}
      ↭

                o.⟨     m₁ c.∘ o.π₁
                  , o.⟨ m₂ c.∘ o.π₁
                      , m₃ c.∘ o.π₂ ⟩ c.∘ o.π₂ ⟩
            c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩

      {- ∘ distributes over ⟨,⟩; β-reduction in second component -}
      ↝⟨ S.[ c.* ]
             o.⟨,⟩* S.⩪
               ( S.idn c.*
               , S.[ c.* ]
                     (S.[ c.* ]
                          o.l-⟨,⟩-∘
                        ∘ c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β))
                   ∘ c.l-cmp)
           ∘ o.l-⟨,⟩-∘ ⟩

                o.⟨     (m₁ c.∘ o.π₁) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
                  , o.⟨ (m₂ c.∘ o.π₁) c.∘            o.⟨ snd← , thd← ⟩
                      , (m₃ c.∘ o.π₂) c.∘            o.⟨ snd← , thd← ⟩ ⟩ ⟩

      {- associativity; β-reduction -}
      ↝⟨ o.⟨,⟩* S.⩪
         ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
         , o.⟨,⟩* S.⩪
           ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
           , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp)) ⟩

                o.⟨     m₁ c.∘ fst←
                  , o.⟨ m₂ c.∘ snd←
                      , m₃ c.∘ thd← ⟩ ⟩

      {- associativity -}
      ↜⟨ o.⟨,⟩* S.⩪ (c.l-cmp , o.⟨,⟩* S.⩪ (c.l-cmp , S.idn c.*)) ⟩

                o.⟨     (m₁ c.∘ o.π₁) c.∘ o.π₁
                  , o.⟨ (m₂ c.∘ o.π₂) c.∘ o.π₁
                      ,  m₃           c.∘ o.π₂ ⟩ ⟩

      {- β-reduction -}
      ↜⟨ o.⟨,⟩* S.⩪
         ( c.cmp* S.⩪ (o.l-π₁-β , S.idn c.*)
         , o.⟨,⟩* S.⩪
           ( c.cmp* S.⩪ (o.l-π₂-β , S.idn c.*)
           , S.idn c.* )) ⟩

                o.⟨     (o.π₁ c.∘ o.⟨ m₁ × m₂ ⟩) c.∘ o.π₁
                  , o.⟨ (o.π₂ c.∘ o.⟨ m₁ × m₂ ⟩) c.∘ o.π₁
                      ,  m₃                      c.∘ o.π₂ ⟩ ⟩

      {- associativity -}
      ↝⟨ o.⟨,⟩* S.⩪ (c.l-cmp , o.⟨,⟩* S.⩪ (c.l-cmp , S.idn c.*)) ⟩

                o.⟨     o.π₁ c.∘ (o.⟨ m₁ × m₂ ⟩ c.∘ o.π₁)
                  , o.⟨ o.π₂ c.∘ (o.⟨ m₁ × m₂ ⟩ c.∘ o.π₁)
                      , m₃                      c.∘ o.π₂ ⟩ ⟩

      {- associativity; β-reduction -}
      ↜⟨ o.⟨,⟩* S.⩪
         ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
         , o.⟨,⟩* S.⩪
           ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
           , o.l-π₂-β)) ⟩

                o.⟨     (o.π₁ c.∘ o.π₁) c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩
                  , o.⟨ (o.π₂ c.∘ o.π₁) c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩
                      , (o.π₂         ) c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩ ⟩ ⟩

      {- calculation -}
      ↭

                o.⟨     fst← c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩
                  , o.⟨ snd← c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩
                      , thd← c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩ ⟩ ⟩

      {- ∘ distributes over ⟨,⟩ -}
      ↜⟨ S.[ c.* ] o.⟨,⟩* S.⩪ (S.idn c.* , o.l-⟨,⟩-∘) ∘ o.l-⟨,⟩-∘ ⟩

                o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
            c.∘ o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩

      ∎
    }
  }
