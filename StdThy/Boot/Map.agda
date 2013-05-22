{-# OPTIONS --type-in-type #-}
module StdThy.Boot.Map where

import StdThy.Std as S

infixr 0 _⇒_

record _⇒_ (S₁ S₂ : S.Std) : Set where
  infix 0 _·⁰_
  infix 0 _·¹_
  field
    _·⁰_ : S.⁰ S₁ → S.⁰ S₂
    _·¹_ : {s⁰₁ s⁰₂ : S.⁰ S₁} → S.¹ S₁ s⁰₁ s⁰₂ → S.¹ S₂ (_·⁰_ s⁰₁) (_·⁰_ s⁰₂)
open _⇒_ public
