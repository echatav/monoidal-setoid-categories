{-# OPTIONS --type-in-type #-}
module 1-CatThy.Core.Cat where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

record IsCat
  (⁰    : Set)
  (¹×²  : ⁰ → ⁰ → S.Std)
  (idn⇒ : {c⁰ : ⁰} → S.⊤ S.⇒ ¹×² c⁰ c⁰)
  (cmp⇒ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → ¹×² c⁰₂ c⁰₃ S.× ¹×² c⁰₁ c⁰₂ S.⇒ ¹×² c⁰₁ c⁰₃)
    : Set
  where
    infixr 3 _∘⁰_
    infixr 3 _∘¹_

    ¹ : ⁰ → ⁰ → Set
    ¹ c⁰₁ c⁰₂ = S.⁰ (¹×² c⁰₁ c⁰₂)

    ² : {c⁰₁ c⁰₂ : ⁰} → ¹ c⁰₁ c⁰₂ → ¹ c⁰₁ c⁰₂ → Set
    ² {c⁰₁} {c⁰₂} = S.¹ (¹×² c⁰₁ c⁰₂)

    idn⁰ : {c⁰₁ : ⁰} → ¹ c⁰₁ c⁰₁
    idn⁰ = idn⇒ S.·⁰ _

    idn¹ : {c⁰₁ : ⁰} → ² {c⁰₁} {c⁰₁} _ _
    idn¹ = idn⇒ S.·¹ _

    cmp⁰ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → ¹ c⁰₂ c⁰₃ P.× ¹ c⁰₁ c⁰₂ → ¹ c⁰₁ c⁰₃
    cmp⁰ = S._·⁰_ cmp⇒

    cmp¹ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} {c¹₂₁ c¹₂₂ : ¹ c⁰₂ c⁰₃} {c¹₁₁ c¹₁₂ : ¹ c⁰₁ c⁰₂}
      → ² c¹₂₁ c¹₂₂ P.× ² c¹₁₁ c¹₁₂
      → ² (cmp⁰ (c¹₂₁ , c¹₁₁)) (cmp⁰ (c¹₂₂ , c¹₁₂))
    cmp¹ = S._·¹_ cmp⇒

    _∘⁰_ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → _ → _ → _
    _∘⁰_ {c⁰₁} {c⁰₂} {c⁰₃} c¹₂ c¹₁ = cmp⁰ {c⁰₁} {c⁰₂} {c⁰₃} (c¹₂ , c¹₁)

    _∘¹_ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} {c¹₂₁ c¹₂₂ : ¹ c⁰₂ c⁰₃} {c¹₁₁ c¹₁₂ : ¹ c⁰₁ c⁰₂}
      → _ → _ → _
    _∘¹_   {c⁰₁} {c⁰₂} {c⁰₃} {c¹₂₁} {c¹₂₂} {c¹₁₁} {c¹₁₂}  c²₂   c²₁ =
      cmp¹ {c⁰₁} {c⁰₂} {c⁰₃} {c¹₂₁} {c¹₂₂} {c¹₁₁} {c¹₁₂} (c²₂ , c²₁)

    field
      l-cmp⁰-idn₁ : {c⁰₁ c⁰₂ : ⁰} {c¹₁ : ¹ c⁰₁ c⁰₂} →
        ² (idn⁰ ∘⁰ c¹₁) c¹₁

      l-cmp⁰-idn₂ : {c⁰₁ c⁰₂ : ⁰} {c¹₁ : ¹ c⁰₁ c⁰₂} →
        ² (c¹₁ ∘⁰ idn⁰) c¹₁

      l-cmp⁰-ass  : {c⁰₁ c⁰₂ c⁰₃ c⁰₄ : ⁰}
        → {c¹₃ : ¹ c⁰₃ c⁰₄}
        → {c¹₂ : ¹ c⁰₂ c⁰₃}
        → {c¹₁ : ¹ c⁰₁ c⁰₂}
        → ² ((c¹₃ ∘⁰ c¹₂) ∘⁰ c¹₁) (c¹₃ ∘⁰ (c¹₂ ∘⁰ c¹₁))

record Cat : Set where
  infixr 3 [_]_∘⁰_
  infixr 3 [_]_∘¹_
  field
    ⁰     : Set
    ¹×²   : ⁰ → ⁰ → S.Std
    idn⇒  : {c⁰₁ : ⁰} → S.⊤ S.⇒ ¹×² c⁰₁ c⁰₁
    cmp⇒  : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → ¹×² c⁰₂ c⁰₃ S.× ¹×² c⁰₁ c⁰₂ S.⇒ ¹×² c⁰₁ c⁰₃
    isCat : IsCat ⁰ ¹×² idn⇒ cmp⇒

  open IsCat isCat public

  [_]_∘⁰_ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → _
  [_]_∘⁰_ {c⁰₁} {c⁰₂} {c⁰₃} = _∘⁰_ {c⁰₁} {c⁰₂} {c⁰₃}

  [_]_∘¹_ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} {c¹₂₁ c¹₂₂ : ¹ c⁰₂ c⁰₃} {c¹₁₁ c¹₁₂ : ¹ c⁰₁ c⁰₂}
    → _
  [_]_∘¹_ {c⁰₁} {c⁰₂} {c⁰₃} {c¹₂₁} {c¹₂₂} {c¹₁₁} {c¹₁₂} =
     _∘¹_ {c⁰₁} {c⁰₂} {c⁰₃} {c¹₂₁} {c¹₂₂} {c¹₁₁} {c¹₁₂}

  ¹×²? : {c⁰₁ c⁰₂ : ⁰} → S.Std
  ¹×²? {c⁰₁} {c⁰₂} = ¹×² c⁰₁ c⁰₂
open Cat public
