{-# OPTIONS --type-in-type #-}
module 1-CatThy.Cat.Op where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

private
  module OpDef (C : C.Cat) where
    module c = C.Cat C

    obj : Set
    obj = c.obj

    hom* : obj → obj → S.Std
    hom* a₁ a₂ = c.hom* a₂ a₁

    idn* : {a : obj} → S.One S.⇒ hom* a a
    idn* = c.idn*

    cmp* : {a₁ a₂ a₃ : obj} → hom* a₂ a₃ S.× hom* a₁ a₂ S.⇒ hom* a₁ a₃
    cmp* = c.cmp* S.M.∘ S.⟨ S.π₂ c.* {c.*} , S.π₁ {c.*} c.* ⟩

    isCat : C.IsCat obj hom* idn* cmp*
    isCat = record
      { l-idn₁ = c.l-idn₂
      ; l-idn₂ = c.l-idn₁
      ; l-cmp  = S.[ c.* ] c.l-cmp ⁻¹
      }

Op : C.Cat → C.Cat
Op C = record
  { obj   = obj
  ; hom*  = hom*
  ; idn*  = idn*
  ; cmp*  = cmp*
  ; isCat = isCat
  }
  where
    open OpDef C
