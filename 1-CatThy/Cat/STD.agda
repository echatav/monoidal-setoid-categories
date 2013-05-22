{-# OPTIONS --type-in-type #-}
module 1-CatThy.Cat.STD where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

private
  obj : Set
  obj = S.Std

  hom* : obj → obj → S.Std
  hom* = S.M.std

  idn* : {A : obj} → S.One S.⇒ hom* A A
  idn* = S.M.elm S.M.idn

  cmp* : {A₁ A₂ A₃ : obj} → hom* A₂ A₃ S.× hom* A₁ A₂ S.⇒ hom* A₁ A₃
  cmp* {A₁} {A₂} {A₃} = record
    { o⇒ = S.M.cmp
    ; h⇒ = λ {f} p → S.[ A₃ ] P.π₁ p ∘ P.π₁ f S.⩪ P.π₂ p
    }

  isCat : C.IsCat obj hom* idn* cmp*
  isCat = record
    { l-idn₁ = λ {_} {A₂} → S.idn A₂
    ; l-idn₂ = λ {_} {A₂} → S.idn A₂
    ; l-cmp  = λ {_} {_} {_} {A₄} → S.idn A₄
    }

STD : C.Cat
STD = record
  { obj   = obj
  ; hom*  = hom*
  ; idn*  = idn*
  ; cmp*  = cmp*
  ; isCat = isCat
  }
