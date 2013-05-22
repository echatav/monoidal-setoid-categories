{-# OPTIONS --type-in-type #-}
module PreThy.Map where

import PreThy.Prd as P

open import PreThy.Boot.Map public

module M where
  idn : {A : Set} → A ⇒ A
  idn a = a

  cmp : {A₁ A₂ A₃ : Set} → (A₂ ⇒ A₃) P.× (A₁ ⇒ A₂) → A₁ ⇒ A₃
  cmp (f₁ P., f₂) a = f₁ (f₂ a)

  _∘_ : {A₁ A₂ A₃ : Set} → A₂ ⇒ A₃ → A₁ ⇒ A₂ → A₁ ⇒ A₃
  _∘_ f₂ f₁ = cmp (f₂ P., f₁)

  elm : {A₁ A₂ : Set} → A₁ → A₂ ⇒ A₁
  elm a _ = a
