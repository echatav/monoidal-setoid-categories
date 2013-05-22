{-# OPTIONS --type-in-type #-}
module 1-CatThy.Core.Boot.Map₁ where

import StdThy.Map as S
import StdThy.Std as S

import 1-CatThy.Core.Cat as C

infixr 0 _⇒¹_

record Is-⇒¹
  (C₁ C₂ : C.Cat)
  (⇒⁰    : C.⁰ C₁ → C.⁰ C₂)
  (⇒¹×²  : {c⁰₁ c⁰₂ : C.⁰ C₁} → C.¹×² C₁ c⁰₁ c⁰₂ S.⇒ C.¹×² C₂ (⇒⁰ c⁰₁) (⇒⁰ c⁰₂))
    : Set
  where
    field
      l-⇒¹×²-idn : {c⁰₁ : C.⁰ C₁} →
        C.² C₂ (⇒¹×² S.·⁰ C.idn⁰ C₁ {c⁰₁}) (C.idn⁰ C₂ {⇒⁰ c⁰₁})

      l-⇒¹×²-cmp : {c⁰₁ c⁰₂ c⁰₃ : C.⁰ C₁}
        → {c¹₂ : C.¹ C₁ c⁰₂ c⁰₃}
        → {c¹₁ : C.¹ C₁ c⁰₁ c⁰₂}
        → C.² C₂
            (⇒¹×² S.·⁰ (C.[ C₁ ] c¹₂ ∘⁰ c¹₁))
            (C.[ C₂ ] (⇒¹×² S.·⁰ c¹₂) ∘⁰ (⇒¹×² S.·⁰ c¹₁))

record _⇒¹_ (C₁ C₂ : C.Cat) : Set where
  infix 0 _·⁰_
  infix 0 _·¹×²_
  infix 4 _·¹_
  infix 1 _·²_
  field
    _·⁰_   : C.⁰ C₁ → C.⁰ C₂
    _·¹×²_ : {c⁰₁ c⁰₂ : C.⁰ C₁} →
      C.¹×² C₁ c⁰₁ c⁰₂ S.⇒ C.¹×² C₂ (_·⁰_ c⁰₁) (_·⁰_ c⁰₂)
    is-⇒¹  : Is-⇒¹ C₁ C₂ _·⁰_ _·¹×²_

  open Is-⇒¹ is-⇒¹ public

  _·¹_ : {c⁰₁ c⁰₂ : C.⁰ C₁} → _ → _
  _·¹_ {c⁰₁} {c⁰₂} c¹₁ = _·¹×²_ {c⁰₁} {c⁰₂} S.·⁰ c¹₁

  _·²_ : {c⁰₁ c⁰₂ : C.⁰ C₁} {c¹₁ c¹₂ : C.¹ C₁ c⁰₁ c⁰₂} → C.² C₁ c¹₁ c¹₂ → _
  _·²_ {c⁰₁} {c⁰₂} c²₁ = _·¹×²_ {c⁰₁} {c⁰₂} S.·¹ c²₁
open _⇒¹_ public
