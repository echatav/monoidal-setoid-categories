{-# OPTIONS --type-in-type #-}
module StdThy.Prd where

open import Bundle.Prelude
open import Bundle.PreThy

import StdThy.Boot.Map as S
import StdThy.Std      as S

infixr 1 _×_

private
  module PrdDef (S₁ S₂ : S.Std) where
    ⁰ : Set
    ⁰ = S.⁰ S₁ P.× S.⁰ S₂

    ¹ : ⁰ → ⁰ → Set
    ¹ (s⁰₁₁ , s⁰₁₂) (s⁰₂₁ , s⁰₂₂) = S.¹ S₁ s⁰₁₁ s⁰₂₁ P.× S.¹ S₂ s⁰₁₂ s⁰₂₂

    idn : {s⁰ : ⁰} → ¹ s⁰ s⁰
    idn = S.idn S₁ , S.idn S₂

    cmp : {s⁰₁ s⁰₂ s⁰₃ : ⁰} → ¹ s⁰₂ s⁰₃ P.× ¹ s⁰₁ s⁰₂ → ¹ s⁰₁ s⁰₃
    cmp ((s¹₁₁ , s¹₁₂) , (s¹₂₁ , s¹₂₂)) =
        S.[ S₁ ] s¹₁₁ ∘ s¹₂₁
      , S.[ S₂ ] s¹₁₂ ∘ s¹₂₂

    inv : {s⁰₁ s⁰₂ : ⁰} → ¹ s⁰₁ s⁰₂ → ¹ s⁰₂ s⁰₁
    inv (s¹₁ , s¹₂) =
        S.inv S₁ s¹₁
      , S.inv S₂ s¹₂

_×_ : S.Std → S.Std → S.Std
S₁ × S₂ = record
  { ⁰ = ⁰
  ; ¹ = ¹
  ; idn = idn
  ; cmp = cmp
  ; inv = inv
  }
  where
    open PrdDef S₁ S₂

π₁ : {S₁ : S.Std} (S₂ : S.Std) → S₁ × S₂ S.⇒ S₁
π₁ S₂ = record
  { _·⁰_ = P.π₁
  ; _·¹_ = P.π₁
  }

π₂ : (S₁ : S.Std) {S₂ : S.Std} → S₁ × S₂ S.⇒ S₂
π₂ S₁ = record
  { _·⁰_ = P.π₂
  ; _·¹_ = P.π₂
  }

⟨_,_⟩ : {S₁ S₂ S₃ : S.Std} → S₃ S.⇒ S₁ → S₃ S.⇒ S₂ → S₃ S.⇒ S₁ × S₂
⟨_,_⟩ {S₁} {S₂} {S₃} m₁ m₂ = record
  { _·⁰_ = P.⟨ S._·⁰_ m₁ , S._·⁰_ m₂ ⟩
  ; _·¹_ = P.⟨_,_⟩
             {S.¹ S₁ (m₁ S.·⁰ _) (m₁ S.·⁰ _)}
             {S.¹ S₂ (m₂ S.·⁰ _) (m₂ S.·⁰ _)}
             {S.¹ S₃ _           _          }
             (S._·¹_ m₁)
             (S._·¹_ m₂)
--P.⟨ S._·¹_ m₁ , S._·¹_ m₂ ⟩
  }

-- ⟨_×_⟩ : {S₁ S₂ S₃ S₄ : S.Std} → S₁ S.⇒ S₃ → S₂ S.⇒ S₄ → S₁ × S₂ S.⇒ S₃ × S₄
-- ⟨ m₁ × m₂ ⟩ = record
--   { _·⁰_ = P.⟨ S._·⁰_ m₁ × S._·⁰_ m₂ ⟩
--   ; _·¹_ = P.⟨ S._·¹_ m₁ × S._·¹_ m₂ ⟩
--   }
