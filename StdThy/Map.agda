{-# OPTIONS --type-in-type #-}
module StdThy.Map where

open import Bundle.Prelude
open import Bundle.PreThy

import StdThy.Prd as S
import StdThy.Std as S

open import StdThy.Boot.Map public

private
  module StdDef (S₁ S₂ : S.Std) where
    ⁰ : Set
    ⁰ = S₁ ⇒ S₂

    ¹ : ⁰ → ⁰ → Set
    ¹ m₁ m₂ = {s⁰₁ : S.⁰ S₁} → S.¹ S₂ (m₁ ·⁰ s⁰₁) (m₂ ·⁰ s⁰₁)

    idn : {m : ⁰} → ¹ m m
    idn = S.idn S₂

    cmp : {m₁ m₂ m₃ : ⁰} → ¹ m₂ m₃ P.× ¹ m₁ m₂ → ¹ m₁ m₃
    cmp (s¹₂ , s¹₁) = S.cmp S₂ (s¹₂ , s¹₁)

    inv : {m₁ m₂ : ⁰} → ¹ m₁ m₂ → ¹ m₂ m₁
    inv s¹₁ = S.inv S₂ s¹₁

    std : S.Std
    std = record
      { ⁰ = ⁰
      ; ¹ = ¹
      ; idn = λ {m} → idn {m}
      ; cmp = λ {m₁} {m₂} {m₃} → cmp {m₁} {m₂} {m₃}
      ; inv = λ {m₁} {m₂} → inv {m₁} {m₂}
      }

module M where
  idn : {S : S.Std} → S ⇒ S
  idn = record
    { _·⁰_ = P.M.idn
    ; _·¹_ = P.M.idn
    }

  cmp : {S₁ S₂ S₃ : S.Std} → (S₂ ⇒ S₃) P.× (S₁ ⇒ S₂) → S₁ ⇒ S₃
  cmp (m₂ , m₁) = record
    { _·⁰_ = _·⁰_ m₂ P.M.∘ _·⁰_ m₁
    ; _·¹_ = _·¹_ m₂ P.M.∘ _·¹_ m₁
    }

  _∘_ : {S₁ S₂ S₃ : S.Std} → _ → _ → _
  _∘_ {S₁} {S₂} {S₃} m₂ m₁ = cmp {S₁} {S₂} {S₃} (m₂ , m₁)

  elm : {S₁ S₂ : S.Std} → S.⁰ S₁ → S₂ ⇒ S₁
  elm {S₁} s⁰₁ = record
    { _·⁰_ = P.M.elm s⁰₁
    ; _·¹_ = P.M.elm (S.idn S₁)
    }

  std : S.Std → S.Std → S.Std
  std = StdDef.std
