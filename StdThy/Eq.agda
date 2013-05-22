{-# OPTIONS --type-in-type #-}
module StdThy.Eq where

open import Bundle.PreThy

import StdThy.Std as S

module Eq (S : S.Std) where
  open S.Std S

  infix  1 proof_
  infixr 2 _↝⟨_⟩_
  infixr 2 _↜⟨_⟩_
  infixr 2 _↭_
  infix  2 _∎

  data ¹↑ (s⁰₁ s⁰₂ : ⁰) : Set where
    emb : ¹ s⁰₁ s⁰₂ → ¹↑ s⁰₁ s⁰₂

  proof_ : {s⁰₁ s⁰₂ : ⁰} → ¹↑ s⁰₁ s⁰₂ → ¹ s⁰₁ s⁰₂
  proof_ (emb s¹₁) = s¹₁

  _↝⟨_⟩_ : (s⁰₁ : ⁰) {s⁰₂ s⁰₃ : ⁰} → ¹  s⁰₁ s⁰₂ → ¹↑ s⁰₂ s⁰₃ → ¹↑ s⁰₁ s⁰₃
  _↝⟨_⟩_ s⁰₁ s¹₁ (emb s¹₂) = emb (s¹₂ ∘ s¹₁)

  _↜⟨_⟩_ : (s⁰₁ : ⁰) {s⁰₂ s⁰₃ : ⁰} → ¹  s⁰₂ s⁰₁ → ¹↑ s⁰₂ s⁰₃ → ¹↑ s⁰₁ s⁰₃
  _↜⟨_⟩_ s⁰₁ s¹₁ (emb s¹₂) = emb (s¹₂ ∘ inv s¹₁)

  _↭_ : (s⁰₁ : ⁰) {s⁰₂ : ⁰} → ¹↑  s⁰₁ s⁰₂ → ¹↑ s⁰₁ s⁰₂
  _↭_ s⁰₁ s¹₁ = s¹₁

  _∎ : (s⁰₁ : ⁰) → ¹↑ s⁰₁ s⁰₁
  _∎ _ = emb idn
