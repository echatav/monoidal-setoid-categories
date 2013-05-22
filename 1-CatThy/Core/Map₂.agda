{-# OPTIONS --type-in-type #-}
import 1-CatThy.Core.Cat as C

module 1-CatThy.Core.Map₂ {C₁ C₂ : C.Cat} where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Core.Boot.Map₁ as C

private
  module nC₁ = C.Cat C₁
  module nC₂ = C.Cat C₂

record _⇒²_ (m¹₁ m¹₂ : C₁ C.⇒¹ C₂) : Set where
  field
    com   : (c⁰₁ : nC₁.⁰) → nC₂.¹ (m¹₁ C.·⁰ c⁰₁) (m¹₂ C.·⁰ c⁰₁)
    l-nat : {c⁰₁ c⁰₂ : nC₁.⁰} {c¹₁ : nC₁.¹ c⁰₁ c⁰₂} →
      nC₂.²
        ((m¹₂ C.·¹ c¹₁) nC₂.∘⁰ com c⁰₁)
        (com c⁰₂ nC₂.∘⁰ m¹₁ C.·¹ c¹₁)
open _⇒²_ public

module M₂ where
  private
    module StdDef (m¹₁ m¹₂ : C₁ C.⇒¹ C₂) where
      ⁰ : Set
      ⁰ = m¹₁ ⇒² m¹₂

      ¹ : ⁰ → ⁰ → Set
      ¹ m²₁ m²₂ = {c⁰₁ : nC₁.⁰} → nC₂.² (com m²₁ c⁰₁) (com m²₂ c⁰₁)

      idn : {m²₁ : ⁰} → ¹ m²₁ m²₁
      idn = S.idn nC₂.¹×²?

      cmp : {m²₁ m²₂ m²₃ : ⁰} → ¹ m²₂ m²₃ P.× ¹ m²₁ m²₂ → ¹ m²₁ m²₃
      cmp (m³₂ , m³₁) = S.[ nC₂.¹×²? ] m³₂ ∘ m³₁

      inv : {m²₁ m²₂ : ⁰} → ¹ m²₁ m²₂ → ¹ m²₂ m²₁
      inv m³₁ = S.inv nC₂.¹×²? m³₁

  std : C₁ C.⇒¹ C₂ → C₁ C.⇒¹ C₂ → S.Std
  std m¹₁ m¹₂ = record
    { ⁰ = ⁰
    ; ¹ = ¹
    ; idn = λ {n} → idn {n}
    ; cmp = λ {n₁} {n₂} {n₃} → cmp {n₁} {n₂} {n₃}
    ; inv = λ {n₁} {n₂} → inv {n₁} {n₂}
    }
    where
      open StdDef m¹₁ m¹₂

  idn : (m¹₀ : C₁ C.⇒¹ C₂) → m¹₀ ⇒² m¹₀
  idn m¹₀ = record
    { com   = λ _ → C.idn⁰ C₂
    ; l-nat = λ {_} {_} {c¹₁} → let open S.Eq nC₂.¹×²? in
        proof

              (m¹₀ C.·¹ c¹₁) nC₂.∘⁰ nC₂.idn⁰

        {- right identity law -}
        ↝⟨ nC₂.l-cmp⁰-idn₂ ⟩

              m¹₀ C.·¹ c¹₁

        {- left identity law -}
        ↜⟨ nC₂.l-cmp⁰-idn₁ ⟩

              nC₂.idn⁰ nC₂.∘⁰ (m¹₀ C.·¹ c¹₁)

        ∎
    }

  cmp : {m¹₁ m¹₂ m¹₃ : C₁ C.⇒¹ C₂} → m¹₂ ⇒² m¹₃ P.× m¹₁ ⇒² m¹₂ → m¹₁ ⇒² m¹₃
  cmp {m¹₁} {m¹₂} {m¹₃} (m²₂ , m²₁) = record
    { com   = λ c⁰₁ → com m²₂ c⁰₁ nC₂.∘⁰ com m²₁ c⁰₁
    ; l-nat = λ {c⁰₁} {c⁰₂} {c¹₁} → let open S.Eq nC₂.¹×²? in
        proof

              m¹₃ C.·¹ c¹₁ nC₂.∘⁰ (com m²₂ c⁰₁ nC₂.∘⁰ com m²₁ c⁰₁)

        {- associativity -}
        ↜⟨ nC₂.l-cmp⁰-ass ⟩

              (m¹₃ C.·¹ c¹₁ nC₂.∘⁰ com m²₂ c⁰₁) nC₂.∘⁰ com m²₁ c⁰₁

        {- naturality of com n₂ -}
        ↝⟨ l-nat m²₂ nC₂.∘¹ S.idn nC₂.¹×²? ⟩

              (com m²₂ c⁰₂ nC₂.∘⁰ m¹₂ C.·¹ c¹₁) nC₂.∘⁰ com m²₁ c⁰₁

        {- associativity -}
        ↝⟨ nC₂.l-cmp⁰-ass ⟩

              com m²₂ c⁰₂ nC₂.∘⁰ (m¹₂ C.·¹ c¹₁ nC₂.∘⁰ com m²₁ c⁰₁)

        {- naturality of com n₁ -}
        ↝⟨ S.idn nC₂.¹×²? nC₂.∘¹ l-nat m²₁ ⟩

              com m²₂ c⁰₂ nC₂.∘⁰ (com m²₁ c⁰₂ nC₂.∘⁰ m¹₁ C.·¹ c¹₁)

        {- associativity -}
        ↜⟨ nC₂.l-cmp⁰-ass ⟩

              (com m²₂ c⁰₂ nC₂.∘⁰ com m²₁ c⁰₂) nC₂.∘⁰ m¹₁ C.·¹ c¹₁

        ∎
    }

  _∘_ : {m¹₁ m¹₂ m¹₃ : C₁ C.⇒¹ C₂} → m¹₂ ⇒² m¹₃ → m¹₁ ⇒² m¹₂ → m¹₁ ⇒² m¹₃
  _∘_ m²₂ m²₁ = cmp (m²₂ , m²₁)
