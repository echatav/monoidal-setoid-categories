{-# OPTIONS --type-in-type #-}
open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

import 1-CatThy.Cat.Fam.Rel    as C
import 1-CatThy.Cat.Op         as C
import 1-CatThy.Cat.STD        as C
import 1-CatThy.Obj.CwF.CtxCmp as C
import 1-CatThy.Str.CwF.Core

module 1-CatThy.Obj.CwF.Pi
  (C   : C.Cat)
  (T   : C.Op C C.⇒₁ C.FAM C.STD)
  (ctx : C.O.CtxCmp C T) where
open 1-CatThy.Str.CwF.Core C T
open C.O.CtxCmp            C T ctx

module O where
  record IsPi : Set where

  record Pi : Set where
    field
      Π    : {Γ : Ctx} (A₁ : Tp Γ) (A₂ : Tp (Γ ▸ A₁)) → Tp Γ
      abs  : {Γ : Ctx} {A₁ : Tp Γ} {A₂ : Tp (Γ ▸ A₁)}
        → Tm (Γ ▸ A₁) A₂
        → Tm Γ (Π A₁ A₂)
      app  : {Γ : Ctx} {A₁ : Tp Γ} {A₂ : Tp (Γ ▸ A₁)}
        → Tm Γ (Π A₁ A₂)
        → (M₂ : Tm Γ A₁)
        → Tm Γ (A₂ Tp[ ext (C.idn C) A₁ (C.F.* C.STD (T C.· Γ) {!!} S.· M₂) ])
      isPi : IsPi
