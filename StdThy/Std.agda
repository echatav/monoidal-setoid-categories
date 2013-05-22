{-# OPTIONS --type-in-type #-}
module StdThy.Std where

open import Bundle.Prelude
open import Bundle.PreThy

record Std : Set where
  infixr 0 _∘_
  infixr 0 [_]_∘_
  field
    ⁰ : Set
    ¹ : ⁰ → ⁰ → Set
    idn : {s⁰₁ : ⁰} → ¹ s⁰₁ s⁰₁
    cmp : {s⁰₁ s⁰₂ s⁰₃ : ⁰} → ¹ s⁰₂ s⁰₃ P.× ¹ s⁰₁ s⁰₂ → ¹ s⁰₁ s⁰₃
    inv : {s⁰₁ s⁰₂ : ⁰} → ¹ s⁰₁ s⁰₂ → ¹ s⁰₂ s⁰₁


  _∘_ : {s⁰₁ s⁰₂ s⁰₃ : ⁰} → _ → _ → _
  _∘_ {s⁰₁} {s⁰₂} {s⁰₃} s¹₂ s¹₁ = cmp {s⁰₁} {s⁰₂} {s⁰₃} (s¹₂ , s¹₁)

  [_]_∘_ : {s⁰₁ s⁰₂ s⁰₃ : ⁰} → _ → _ → _
  [_]_∘_ {s⁰₁} {s⁰₂} {s⁰₃} = _∘_ {s⁰₁} {s⁰₂} {s⁰₃}
open Std public
