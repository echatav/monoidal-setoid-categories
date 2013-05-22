{-# OPTIONS --type-in-type #-}
module PreThy.Id where

import PreThy.Prd as P

module I where
  data Id {A : Set} (a : A) : A → Set where
    refl : Id a a

  cmp : {A : Set} {a₁ a₂ a₃ : A} → Id a₂ a₃ P.× Id a₁ a₂ → Id a₁ a₃
  cmp (refl P., refl) = refl

  _∘_ : {A : Set} {a₁ a₂ a₃ : A} → _ → _ → _
  _∘_ {A} {a₁} {a₂} {a₃} p₂ p₁ = cmp {A} {a₁} {a₂} {a₃} (p₂ P., p₁)

  inv : {A : Set} {a₁ a₂ : A} → Id a₁ a₂ → Id a₂ a₁
  inv refl = refl

  _⁻¹ : {A : Set} {a₁ a₂ : A} → _ → _
  _⁻¹ {A} {a₁} {a₂} = inv {A} {a₁} {a₂}

  stb : {A₁ A₂ : Set} (f : A₁ → A₂) {a₁ a₂ : A₁} → Id a₁ a₂ → Id (f a₁) (f a₂)
  stb f refl = refl
