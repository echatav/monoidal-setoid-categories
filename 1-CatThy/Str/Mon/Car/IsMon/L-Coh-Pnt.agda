{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd      as C
import 1-CatThy.Obj.Trm      as C
import 1-CatThy.Str.Mon.Core as C

module 1-CatThy.Str.Mon.Car.IsMon.L-Coh-Pnt
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

l-coh-pnt : {a₁ a₂ a₃ a₄ : c.obj} →
  S.[ c.* ]
          C.com (C.I.fwd α) ((a₁ , a₂) , C.o⇒ ×-⇒₁ (a₃ , a₄))
      c.∘ C.com (C.I.fwd α) ((C.o⇒ ×-⇒₁ (a₁ , a₂) , a₃) , a₄)
    ≃     C.h⇒ ×-⇒₁ S.· (c.idn , C.com (C.I.fwd α) ((a₂ , a₃) , a₄))
      c.∘ (    C.com (C.I.fwd α) ((a₁ , C.o⇒ ×-⇒₁ (a₂ , a₃)) , a₄)
           c.∘ C.h⇒ ×-⇒₁ S.· (C.com (C.I.fwd α) ((a₁ , a₂) , a₃) , c.idn))
l-coh-pnt = let open S.Eq c.* in
  proof
            o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
        c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↝⟨ S.[ c.* ] o.⟨,⟩* S.⩪ (S.idn c.* , o.l-⟨,⟩-∘) ∘ o.l-⟨,⟩-∘ ⟩

            o.⟨      fst← c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
              , o.⟨  snd← c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
                  ,  thd← c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩ ⟩

  {- calculation -}
  ↭

            o.⟨     (o.π₁ c.∘ o.π₁) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
              , o.⟨ (o.π₂ c.∘ o.π₁) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
                  , (         o.π₂) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩ ⟩

  {- associativity -}
  ↝⟨ o.⟨,⟩* S.⩪ (c.l-cmp , o.⟨,⟩* S.⩪ (c.l-cmp , S.idn c.*)) ⟩

            o.⟨        o.π₁ c.∘ (o.π₁ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩)
              ,   o.⟨  o.π₂ c.∘ (o.π₁ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩)
                    ,           (o.π₂ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) ⟩ ⟩

  {- β-reduction -}
  ↝⟨ o.⟨,⟩* S.⩪
     ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
     , o.⟨,⟩* S.⩪
       ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
       , o.l-π₂-β )) ⟩

            o.⟨           o.π₁ c.∘ fst←
              ,   o.⟨     o.π₂ c.∘ fst←
                    , o.⟨ snd←
                        , thd← ⟩ ⟩ ⟩

  {- calculation -}
  ↭

            o.⟨           o.π₁ c.∘ (o.π₁ c.∘ o.π₁)
              ,   o.⟨     o.π₂ c.∘ (o.π₁ c.∘ o.π₁)
                    , o.⟨ o.π₂ c.∘ o.π₁
                        , thd← ⟩ ⟩ ⟩


  {- associativity -}
  ↜⟨ o.⟨,⟩* S.⩪ (c.l-cmp , o.⟨,⟩* S.⩪ (c.l-cmp , S.idn c.*)) ⟩

            o.⟨           (o.π₁ c.∘ o.π₁) c.∘ o.π₁
              ,   o.⟨     (o.π₂ c.∘ o.π₁) c.∘ o.π₁
                    , o.⟨  o.π₂ c.∘ o.π₁
                        ,  thd← ⟩ ⟩ ⟩

  {- calculation -}
  ↭

            o.⟨           fst← c.∘ o.π₁
              ,   o.⟨     snd← c.∘ o.π₁
                    , o.⟨ thd← c.∘ o.π₁
                        , thd← ⟩ ⟩ ⟩

  {- β-reduction -}
  ↜⟨ o.⟨,⟩* S.⩪
     ( c.cmp* S.⩪ (o.l-π₁-β , S.idn c.*)
     , o.⟨,⟩* S.⩪
       ( c.cmp* S.⩪ (o.l-π₁-β , S.idn c.*)
       , o.⟨,⟩* S.⩪
         ( c.cmp* S.⩪ (o.l-π₂-β , S.idn c.*)
         , S.idn c.* ))) ⟩

             o.⟨          (o.π₁ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) c.∘ o.π₁
               ,  o.⟨     (o.π₁ c.∘            o.⟨ snd← , thd← ⟩  ) c.∘ o.π₁
                    , o.⟨ (o.π₂ c.∘            o.⟨ snd← , thd← ⟩  ) c.∘ o.π₁
                        ,                                 thd← ⟩ ⟩ ⟩

  {- associativity -}
  ↝⟨ o.⟨,⟩* S.⩪
     ( c.l-cmp
     , o.⟨,⟩* S.⩪
       ( c.l-cmp
       , o.⟨,⟩* S.⩪
         ( c.l-cmp
         , S.idn c.* ))) ⟩

             o.⟨          o.π₁ c.∘ (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁)
               ,  o.⟨     o.π₁ c.∘ (           o.⟨ snd← , thd← ⟩   c.∘ o.π₁)
                    , o.⟨ o.π₂ c.∘ (           o.⟨ snd← , thd← ⟩   c.∘ o.π₁)
                        ,                                 thd← ⟩ ⟩ ⟩

  {- β-reduction -}
  ↜⟨ o.⟨,⟩* S.⩪
     ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
     , o.⟨,⟩* S.⩪
       ( c.cmp* S.⩪ (S.idn c.* , c.cmp* S.⩪ (o.l-π₂-β , S.idn c.*))
       ,  o.⟨,⟩* S.⩪
          ( c.cmp* S.⩪ (S.idn c.* , c.cmp* S.⩪ (o.l-π₂-β , S.idn c.*))
          , o.l-π₂-β ))) ⟩

             o.⟨           o.π₁ c.∘  (o.π₁  c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩)
               ,  o.⟨      o.π₁ c.∘ ((o.π₂  c.∘      o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) c.∘ o.π₁)
                    , o.⟨  o.π₂ c.∘ ((o.π₂  c.∘      o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) c.∘ o.π₁)
                        ,            (o.π₂  c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩) ⟩ ⟩ ⟩

  {- associativity -}
  ↜⟨ o.⟨,⟩* S.⩪
     ( c.l-cmp
     , o.⟨,⟩* S.⩪
       ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , S.[ c.* ] c.l-cmp ⁻¹) ∘ c.l-cmp
       , o.⟨,⟩* S.⩪
         ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , S.[ c.* ] c.l-cmp ⁻¹) ∘ c.l-cmp
         , S.idn c.* ))) ⟩

             o.⟨           (o.π₁ c.∘ o.π₁) c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩
               ,  o.⟨      (o.π₁ c.∘ o.π₂) c.∘     (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁)
                    , o.⟨  (o.π₂ c.∘ o.π₂) c.∘     (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁)
                        ,  (         o.π₂) c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩ ⟩ ⟩ ⟩

  {- calculation -}
  ↭

             o.⟨           fst← c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩
               ,  o.⟨      snd→ c.∘     (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁)
                    , o.⟨  thd→ c.∘     (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁)
                        ,  thd← c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩ ⟩ ⟩ ⟩

  {- associativity -}
  ↜⟨ o.⟨,⟩* S.⩪
     ( S.idn c.*
     , o.⟨,⟩* S.⩪
       ( c.l-cmp
       , o.⟨,⟩* S.⩪
         ( c.l-cmp
         , S.idn c.* ))) ⟩

             o.⟨           fst← c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩
               ,  o.⟨     (snd→ c.∘      o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) c.∘ o.π₁
                    , o.⟨ (thd→ c.∘      o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) c.∘ o.π₁
                        ,  thd← c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩ ⟩ ⟩ ⟩

  {- associativity -}
  ↝⟨ o.⟨,⟩* S.⩪
     ( S.idn c.*
     , o.⟨,⟩* S.⩪
       ( c.l-cmp
       , o.⟨,⟩* S.⩪
         ( c.l-cmp
         , S.idn c.* ))) ⟩

             o.⟨          fst←  c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩
               ,  o.⟨     snd→  c.∘     (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁)
                    , o.⟨ thd→  c.∘     (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁)
                        , thd←  c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩  c.∘ o.π₁  , thd← ⟩ ⟩ ⟩ ⟩

  {- β-reduction -}
  ↜⟨ o.⟨,⟩* S.⩪
     ( S.idn c.*
     , o.⟨,⟩* S.⩪
       ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
       , o.⟨,⟩* S.⩪
         ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
         , S.idn c.*) )) ⟩

             o.⟨           fst←           c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩
               ,  o.⟨      snd→ c.∘ (o.π₁ c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩)
                    , o.⟨  thd→ c.∘ (o.π₁ c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩)
                        ,  thd←           c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩ ⟩ ⟩ ⟩

  {- associativity -}
  ↜⟨ o.⟨,⟩* S.⩪
     ( S.idn c.*
     , o.⟨,⟩* S.⩪
       ( c.l-cmp
       , o.⟨,⟩* S.⩪
         ( c.l-cmp
         , S.idn c.* ))) ⟩

             o.⟨           fst←           c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩
               ,  o.⟨     (snd→ c.∘ o.π₁) c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩
                    , o.⟨ (thd→ c.∘ o.π₁) c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩
                        ,  thd←           c.∘ o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩ ⟩ ⟩ ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↜⟨ S.[ c.* ]
         o.⟨,⟩* S.⩪
           ( S.idn c.*
           , S.[ c.* ]
                 o.⟨,⟩* S.⩪
                   ( S.idn c.*
                   , o.l-⟨,⟩-∘ )
               ∘ o.l-⟨,⟩-∘ )
       ∘ o.l-⟨,⟩-∘ ⟩

             o.⟨          fst←
               ,  o.⟨     snd→ c.∘ o.π₁
                    , o.⟨ thd→ c.∘ o.π₁
                        , thd← ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- calculation -}
  ↭

             o.⟨                    fst←
               ,  o.⟨     (o.π₁ c.∘ o.π₂) c.∘ o.π₁
                    , o.⟨ (o.π₂ c.∘ o.π₂) c.∘ o.π₁
                        ,           thd← ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- associativity -}
  ↝⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪
       ( S.idn c.*
       , o.⟨,⟩* S.⩪
         ( c.l-cmp
         , o.⟨,⟩* S.⩪
           ( c.l-cmp
           , S.idn c.* )))
     , S.idn c.*) ⟩

             o.⟨                   fst←
               ,  o.⟨     o.π₁ c.∘ (o.π₂ c.∘ o.π₁)
                    , o.⟨ o.π₂ c.∘ (o.π₂ c.∘ o.π₁)
                        ,          thd← ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- calculation -}
  ↭

             o.⟨                   fst←
               ,  o.⟨     o.π₁ c.∘ snd←
                    , o.⟨ o.π₂ c.∘ snd←
                        ,          thd← ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- β-reduction -}
  ↜⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪
       ( S.idn c.*
       , o.⟨,⟩* S.⩪
         ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
         , o.⟨,⟩* S.⩪
           ( c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β)
           , o.l-π₂-β )))
     , S.idn c.* ) ⟩

             o.⟨                                 fst←
               ,  o.⟨     o.π₁ c.∘ (o.π₁ c.∘ o.⟨ snd← , thd← ⟩)
                    , o.⟨ o.π₂ c.∘ (o.π₁ c.∘ o.⟨ snd← , thd← ⟩)
                        ,          (o.π₂ c.∘ o.⟨ snd← , thd← ⟩) ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- associativity -}
  ↜⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪
       ( S.idn c.*
       , o.⟨,⟩* S.⩪
         ( c.l-cmp
         , o.⟨,⟩* S.⩪
           ( c.l-cmp
           , S.idn c.* )))
     , S.idn c.* ) ⟩

             o.⟨                                  fst←
               ,  o.⟨     (o.π₁ c.∘ o.π₁) c.∘ o.⟨ snd← , thd← ⟩
                    , o.⟨ (o.π₂ c.∘ o.π₁) c.∘ o.⟨ snd← , thd← ⟩
                        , (         o.π₂) c.∘ o.⟨ snd← , thd← ⟩ ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- calculation -}
  ↭

             o.⟨                       fst←
               ,  o.⟨     fst← c.∘ o.⟨ snd← , thd← ⟩
                    , o.⟨ snd← c.∘ o.⟨ snd← , thd← ⟩
                        , thd← c.∘ o.⟨ snd← , thd← ⟩ ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↜⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪
       ( S.idn c.*
       , S.[ c.* ]
             o.⟨,⟩* S.⩪
               ( S.idn c.*
               , o.l-⟨,⟩-∘ )
           ∘ o.l-⟨,⟩-∘ )
     , S.idn c.* ) ⟩

             o.⟨                                         fst←
               ,  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.⟨ snd← , thd← ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- β-reduction -}
  ↜⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪
       ( o.l-π₁-β
       , c.cmp* S.⩪
         ( S.idn c.*
         , o.l-π₂-β ))
     , S.idn c.* ) ⟩

             o.⟨                                     (o.π₁ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩)
               ,  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ (o.π₂ c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩) ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘  o.π₁ , thd← ⟩

  {- associativity -}
  ↜⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪
       ( S.idn c.*
       , c.l-cmp )
     , S.idn c.* ) ⟩

             o.⟨                                     o.π₁  c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
               , (o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₂) c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ ⟩
        c.∘  o.⟨  o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- ∘ distributes over ⟨,⟩ -}
  ↜⟨ c.cmp* S.⩪ (o.l-⟨,⟩-∘ , S.idn c.*) ⟩

            (    o.⟨                                    o.π₁
                   , o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₂ ⟩
             c.∘ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩)
        c.∘  o.⟨ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩

  {- associativity -}
  ↝⟨ c.l-cmp ⟩

             o.⟨                                    o.π₁
               , o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₂ ⟩
        c.∘ (    o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
             c.∘ o.⟨ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁ , thd← ⟩)

  {- left identity law -}
  ↜⟨ c.cmp* S.⩪
     ( o.⟨,⟩* S.⩪ (c.l-idn₁ , S.idn c.*)
     , c.cmp* S.⩪
       ( S.idn c.*
       , o.⟨,⟩* S.⩪ (S.idn c.* , c.l-idn₁))) ⟩

             o.⟨ c.idn c.∘ fst→
               , o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₂ ⟩
        c.∘ (    o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩
             c.∘ o.⟨ o.⟨ fst← , o.⟨ snd← , thd← ⟩ ⟩ c.∘ o.π₁
                   , c.idn c.∘ thd← ⟩)

  ∎
