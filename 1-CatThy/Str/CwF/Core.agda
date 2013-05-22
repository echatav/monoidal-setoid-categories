{-# OPTIONS --type-in-type #-}
open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

import 1-CatThy.Cat.Fam.Rel as C
import 1-CatThy.Cat.Op      as C
import 1-CatThy.Cat.STD     as C

module 1-CatThy.Str.CwF.Core (C : C.Cat) (T : C.Op C C.⇒₁ C.FAM C.STD) where

Ctx : Set
Ctx = C.obj C

Sub* : Ctx → Ctx → S.Std
Sub* = C.hom* C

Sub  : Ctx → Ctx → Set
Sub Γ₂ Γ₁ = S.obj (Sub* Γ₂ Γ₁)

-- B
Tp* : Ctx → S.Std
Tp* Γ = C.F.B C.STD (T C.· Γ)

Tp  : Ctx → Set
Tp  Γ = S.obj (Tp* Γ)

-- fib
Tm* : (Γ : Ctx) → Tp Γ → S.Std
Tm* Γ A = C.F.fib C.STD (T C.· Γ) A

Tm  : (Γ : Ctx) → Tp Γ → Set
Tm  Γ A = S.obj (Tm* Γ A)

-- ↑
tm↑* : (Γ : Ctx) {A₁ A₂ : Tp Γ}
    → S.[ Tp* Γ ] A₁ ≃ A₂
    →     Tm* Γ   A₁
  S.⇒     Tm* Γ        A₂
tm↑* Γ φ = C.F.↑ C.STD (T C.· Γ) φ

tm↑ : (Γ : Ctx) {A₁ A₂ : Tp Γ}
  → S.[ Tp* Γ ] A₁ ≃ A₂
  →     Tm  Γ   A₁
  →     Tm  Γ        A₂
tm↑ Γ φ = S.o⇒ (tm↑* Γ φ)

tm↑-stb : (Γ : Ctx) {A₁ A₂ : Tp Γ} {M₁ M₂ : Tm Γ A₁}
  → (φ : S.[ Tp* Γ    ]         A₁ ≃         A₂)
  →      S.[ Tm* Γ A₁ ]         M₁ ≃         M₂
  →      S.[ Tm* Γ A₂ ] tm↑ Γ φ M₁ ≃ tm↑ Γ φ M₂
tm↑-stb Γ φ = S.h⇒ (tm↑* Γ φ)

-- laws
tm↑*-idn : (Γ : Ctx) {A : Tp Γ}
  → S.[ S.M.std (Tm* Γ A) (Tm* Γ A) ]
        tm↑* Γ (S.idn (Tp* Γ))
      ≃ C.idn C.STD
tm↑*-idn Γ = C.F.l-idn C.STD (T C.· Γ)

tm↑*-cmp : (Γ : Ctx) {A₁ A₂ A₃ : Tp Γ}
  → {φ₂ : S.[ Tp* Γ ] A₂ ≃ A₃}
  → {φ₁ : S.[ Tp* Γ ] A₁ ≃ A₂}
  → S.[ S.M.std (Tm* Γ A₁) (Tm* Γ A₃) ]
        C.[ C.STD ] tm↑* Γ φ₂ ∘ tm↑* Γ φ₁
      ≃ tm↑* Γ (S.[ Tp* Γ ] φ₂ ∘ φ₁)
tm↑*-cmp Γ = C.F.l-cmp C.STD (T C.· Γ)

tm↑*-inv₁ : (Γ : Ctx) {A₁ A₂ : Tp Γ}
  → {φ : S.[ Tp* Γ ] A₁ ≃ A₂}
  → S.[ S.M.std (Tm* Γ A₁) (Tm* Γ A₁) ]
        C.[ C.STD ] tm↑* Γ (S.[ Tp* Γ ] φ ⁻¹) ∘ tm↑* Γ φ
      ≃ C.idn C.STD
tm↑*-inv₁ Γ = C.F.l-inv₁ C.STD (T C.· Γ)

tm↑*-inv₂ : (Γ : Ctx) {A₁ A₂ : Tp Γ}
  → {φ : S.[ Tp* Γ ] A₁ ≃ A₂}
  → S.[ S.M.std (Tm* Γ A₂) (Tm* Γ A₂) ]
        C.[ C.STD ] tm↑* Γ φ ∘ tm↑* Γ (S.[ Tp* Γ ] φ ⁻¹)
      ≃ C.idn C.STD
tm↑*-inv₂ Γ = C.F.l-inv₂ C.STD (T C.· Γ)

-- B⇒
tp⇒* : {Γ₁ Γ₂ : Ctx} → Sub Γ₂ Γ₁ → Tp* Γ₁ S.⇒ Tp* Γ₂
tp⇒* γ   = C.F.B⇒ C.STD (C.h⇒ T S.· γ)

foo : {Γ₁ Γ₂ : Ctx} {γ₁ γ₂ : Sub Γ₂ Γ₁}
  → S.[ Sub* Γ₂ Γ₁ ] γ₁ ≃ γ₂
  → S.[ S.M.std (Tp* Γ₁) (Tp* Γ₂) ] tp⇒* γ₁ ≃ tp⇒* γ₂
foo {Γ₁} {Γ₂} {γ₁} {γ₂} φ = {!C.h⇒ T S.⩪ φ!}

infixl 0 _tp[_]
_tp[_] : {Γ₁ Γ₂ : Ctx} → Tp Γ₁ → Sub Γ₂ Γ₁ → Tp Γ₂
_tp[_] A γ = tp⇒* γ S.· A

tp[]-stb : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) {A₁ A₂ : Tp Γ₁}
  → S.[ Tp* Γ₁ ] A₁         ≃ A₂
  → S.[ Tp* Γ₂ ] A₁ tp[ γ ] ≃ A₂ tp[ γ ]
tp[]-stb γ φ = tp⇒* γ S.⩪ φ

-- fib⇒
tm⇒* : {Γ₁ Γ₂ : Ctx} {A : Tp Γ₁}
  → (γ : Sub Γ₂ Γ₁) → Tm* Γ₁ A S.⇒ Tm* Γ₂ (A tp[ γ ])
tm⇒* γ = C.F.fib⇒ C.STD (C.h⇒ T S.· γ)

-- foo : {Γ₁ Γ₂ : Ctx} {A : Tp Γ₁} (γ₁ γ₂ : Sub Γ₂ Γ₁)
--   → (φ : S.[ Sub* Γ₂ Γ₁ ] γ₁ ≃ γ₂)
--   → {!!}
-- foo γ₁ γ₂ φ = {!S.h⇒ (C.h⇒ T) φ!}

infixl 0 _tm[_]
_tm[_] : {Γ₁ Γ₂ : Ctx} {A : Tp Γ₁}
  → Tm Γ₁ A → (γ : Sub Γ₂ Γ₁) → Tm Γ₂ (A tp[ γ ])
_tm[_] A γ = tm⇒* γ S.· A

-- l-nat
tm↑*-nat : {Γ₁ Γ₂ : Ctx} {A₁ A₂ : Tp Γ₁} {φ : S.[ Tp* Γ₁ ] A₁ ≃ A₂}
  → (γ : Sub Γ₂ Γ₁)
  → S.[ S.M.std (Tm* Γ₁ A₁) (Tm* Γ₂ (A₂ tp[ γ ])) ]
        C.[ C.STD ] tm⇒* γ ∘ tm↑* Γ₁ φ
      ≃ C.[ C.STD ] tm↑* Γ₂ (tp⇒* γ S.⩪ φ) ∘ tm⇒* γ
tm↑*-nat {Γ₁} {Γ₂} {A} γ = C.F.l-nat C.STD (T C.⩪ γ)

module Coe
  (_▸_ : (Γ : Ctx) → Tp Γ → Ctx)
  (wkn : (Γ : Ctx) (A : Tp Γ) → Sub (Γ ▸ A) Γ)
  (var : (Γ : Ctx) (A : Tp Γ) → Tm (Γ ▸ A) (A tp[ wkn Γ A ]))
  (ext : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁)
    → Tm Γ₂ (A tp[ γ ]) → Sub Γ₂ (Γ₁ ▸ A))
  (law₁ : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A tp[ γ ]))
    → S.[ Sub* Γ₂ Γ₁ ] C.[ C ] wkn Γ₁ A ∘ ext γ A x ≃ γ)
  where
    coe : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A tp[ γ ]))
      → S.[ Tp* Γ₂ ]
            A tp[ wkn Γ₁ A ] tp[ ext γ A x ]
          ≃ A tp[ γ ]
    coe {Γ₁} {Γ₂} γ A x =
      S.cmp (Tp* Γ₂) {a₃ = C.F.B⇒ C.STD (T C.⩪ γ) S.· A}
        ( C.F.B≃ C.STD ((C.h⇒ T) S.⩪ law₁ γ A x)
        , S.[ Tp* Γ₂ ] C.F.B≃ C.STD (C.l-h⇒-cmp T) ⁻¹ )
