{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Alpha.Bwd
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

bwd :  ((⊗ C.M₁.∘ C.⟨ C.M₁.idn A × ⊗ ⟩) C.M₁.∘ C.×-α A A A)
  C.⇒₂  (⊗ C.M₁.∘ C.⟨ ⊗ × C.M₁.idn A ⟩)
bwd = record
  { com   = λ _ → o.⟨ o.⟨ fst→ , snd→ ⟩ , thd→ ⟩
  ; l-nat = λ { {_} {_} {(m₁ , m₂) , m₃} → let open S.Eq c.* in
      proof

                o.⟨ o.⟨ m₁ × m₂ ⟩ × m₃ ⟩
            c.∘ o.⟨ o.⟨ fst→ , snd→ ⟩ , thd→ ⟩

      {- calculation -}
      ↭

                o.⟨ o.⟨ m₁ c.∘ o.π₁
                      , m₂ c.∘ o.π₂ ⟩ c.∘ o.π₁
                  ,     m₃ c.∘ o.π₂ ⟩
            c.∘ o.⟨ o.⟨ fst→ , snd→ ⟩ , thd→ ⟩

      {- distributes ... -}
      ↝⟨ S.[ c.* ]
             o.⟨,⟩* S.⩪
               ( S.[ c.* ]
                     (S.[ c.* ]
                          o.l-⟨,⟩-∘
                        ∘ c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β))
                   ∘ c.l-cmp
               , S.idn c.* )
           ∘ o.l-⟨,⟩-∘ ⟩

                o.⟨ o.⟨ (m₁ c.∘ o.π₁) c.∘     o.⟨ fst→ , snd→ ⟩
                      , (m₂ c.∘ o.π₂) c.∘     o.⟨ fst→ , snd→ ⟩ ⟩
                  ,     (m₃ c.∘ o.π₂) c.∘ o.⟨ o.⟨ fst→ , snd→ ⟩ , thd→ ⟩ ⟩

      {- associativity; β-reduction -}
      ↝⟨ o.⟨,⟩* S.⩪
         ( o.⟨,⟩* S.⩪
           ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
           , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp )
         , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp ) ⟩

                o.⟨ o.⟨ m₁ c.∘ fst→
                      , m₂ c.∘ snd→ ⟩
                  ,     m₃ c.∘ thd→ ⟩

      {- associativity -}
      ↜⟨ o.⟨,⟩* S.⩪ (o.⟨,⟩* S.⩪ (S.idn c.* , c.l-cmp) , c.l-cmp) ⟩

                o.⟨ o.⟨  m₁           c.∘ o.π₁
                      , (m₂ c.∘ o.π₁) c.∘ o.π₂ ⟩
                  ,     (m₃ c.∘ o.π₂) c.∘ o.π₂ ⟩

      {- β-reduction -}
      ↜⟨ o.⟨,⟩* S.⩪
        ( o.⟨,⟩* S.⩪
          ( S.idn c.*
          , c.cmp* S.⩪ (o.l-π₁-β , S.idn c.*) )
        , c.cmp* S.⩪ (o.l-π₂-β , S.idn c.*) ) ⟩

                o.⟨ o.⟨  m₁                      c.∘ o.π₁
                      , (o.π₁ c.∘ o.⟨ m₂ × m₃ ⟩) c.∘ o.π₂ ⟩
                  ,     (o.π₂ c.∘ o.⟨ m₂ × m₃ ⟩) c.∘ o.π₂ ⟩

      {- associativity -}
      ↝⟨ o.⟨,⟩* S.⩪ (o.⟨,⟩* S.⩪ (S.idn c.* , c.l-cmp) , c.l-cmp) ⟩

                o.⟨ o.⟨ m₁                      c.∘ o.π₁
                      , o.π₁ c.∘ (o.⟨ m₂ × m₃ ⟩ c.∘ o.π₂) ⟩
                  ,     o.π₂ c.∘ (o.⟨ m₂ × m₃ ⟩ c.∘ o.π₂) ⟩

      {- associativity; β-reduction -}
      ↜⟨ o.⟨,⟩* S.⩪
         ( o.⟨,⟩* S.⩪
           ( o.l-π₁-β
           , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp)
         , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp ) ⟩

                o.⟨ o.⟨ (o.π₁         ) c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩
                      , (o.π₁ c.∘ o.π₂) c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩ ⟩
                  ,     (o.π₂ c.∘ o.π₂) c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩ ⟩

      {- calculation -}
      ↭

                o.⟨ o.⟨ fst→ c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩
                      , snd→ c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩ ⟩
                  ,     thd→ c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩ ⟩

      {- ∘ distributes over ⟨,⟩ -}
      ↜⟨ S.[ c.* ] o.⟨,⟩* S.⩪ (o.l-⟨,⟩-∘ , S.idn c.*) ∘ o.l-⟨,⟩-∘ ⟩

                o.⟨ o.⟨ fst→ , snd→ ⟩ , thd→ ⟩
            c.∘ o.⟨ m₁ × o.⟨ m₂ × m₃ ⟩ ⟩

      ∎
    }
  }

