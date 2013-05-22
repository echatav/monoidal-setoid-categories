{-# OPTIONS --type-in-type #-}
module 1-CatThy.Core.Map₁ where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Core.Boot.Map₁ as C
import 1-CatThy.Core.Cat       as C
import 1-CatThy.Core.Iso       as C
import 1-CatThy.Core.Map₂      as C

module M₁ where
  private
    module IdnDef (C : C.Cat) where
      _·⁰_ : C.⁰ C → C.⁰ C
      _·⁰_ = P.M.idn

      _·¹×²_ : {c⁰₁ c⁰₂ : C.⁰ C} →
        C.¹×² C c⁰₁ c⁰₂ S.⇒ C.¹×² C (_·⁰_ c⁰₁) (_·⁰_ c⁰₂)
      _·¹×²_ = S.M.idn

      is-⇒¹ : C.Is-⇒¹ C C _·⁰_ _·¹×²_
      is-⇒¹ = record
        { l-⇒¹×²-idn = S.idn (C.¹×²? C)
        ; l-⇒¹×²-cmp = S.idn (C.¹×²? C)
        }

  idn : (C : C.Cat) → C C.⇒¹ C
  idn C = record
    { _·⁰_   = _·⁰_
    ; _·¹×²_ = _·¹×²_
    ; is-⇒¹  = is-⇒¹
    }
    where
      open IdnDef C

  private
    module CmpDef (C₁ C₂ C₃ : C.Cat) (m¹₂ : C₂ C.⇒¹ C₃) (m¹₁ : C₁ C.⇒¹ C₂) where
      _·⁰_ : C.⁰ C₁ → C.⁰ C₃
      _·⁰_ = C._·⁰_ m¹₂ P.M.∘ C._·⁰_ m¹₁

      _·¹×²_ : {c⁰₁ c⁰₂ : C.⁰ C₁} →
        C.¹×² C₁ c⁰₁ c⁰₂ S.⇒ C.¹×² C₃ (_·⁰_ c⁰₁) (_·⁰_ c⁰₂)
      _·¹×²_ = C._·¹×²_ m¹₂ S.M.∘ C._·¹×²_ m¹₁

      is-⇒¹ : C.Is-⇒¹ C₁ C₃ _·⁰_ _·¹×²_
      is-⇒¹ = record
        { l-⇒¹×²-idn =
            S.[ C.¹×²? C₃ ] C.l-⇒¹×²-idn m¹₂ ∘ (m¹₂ C.·² C.l-⇒¹×²-idn m¹₁)
        ; l-⇒¹×²-cmp =
            S.[ C.¹×²? C₃ ] C.l-⇒¹×²-cmp m¹₂ ∘ (m¹₂ C.·² C.l-⇒¹×²-cmp m¹₁)
        }

  cmp : {C₁ C₂ C₃ : C.Cat} → (C₂ C.⇒¹ C₃) P.× (C₁ C.⇒¹ C₂) → C₁ C.⇒¹ C₃
  cmp {C₁} {C₂} {C₃} (m¹₂ , m¹₁) = record
    { _·⁰_   = _·⁰_
    ; _·¹×²_ = _·¹×²_
    ; is-⇒¹  = is-⇒¹
    }
    where
      open CmpDef C₁ C₂ C₃ m¹₂ m¹₁

  _∘_ : {C₁ C₂ C₃ : C.Cat} → _ → _ → _
  _∘_ {C₁} {C₂} {C₃} m¹₂ m¹₁ = cmp {C₁} {C₂} {C₃} (m¹₂ , m¹₁)

  private
    module ElmDef (C₁ C₂ : C.Cat) (c⁰₁ : C.⁰ C₁) where
      _·⁰_ : C.⁰ C₂ → C.⁰ C₁
      _·⁰_ = P.M.elm c⁰₁

      _·¹×²_ : {c⁰₁ c⁰₂ : C.⁰ C₂}
        → C.¹×² C₂ c⁰₁ c⁰₂ S.⇒ C.¹×² C₁ (_·⁰_ c⁰₁) (_·⁰_ c⁰₂)
      _·¹×²_ = S.M.elm (C.idn⁰ C₁)

      is-⇒¹ : C.Is-⇒¹ C₂ C₁ _·⁰_ _·¹×²_
      is-⇒¹ = record
        { l-⇒¹×²-idn = S.idn (C.¹×²? C₁)
        ; l-⇒¹×²-cmp = S.inv (C.¹×²? C₁) (C.l-cmp⁰-idn₁ C₁)
        }

  elm : {C₁ C₂ : C.Cat} → C.⁰ C₁ → C₂ C.⇒¹ C₁
  elm {C₁} {C₂} c⁰₁ = record
    { _·⁰_   = _·⁰_
    ; _·¹×²_ = _·¹×²_
    ; is-⇒¹  = is-⇒¹
    }
    where
      open ElmDef C₁ C₂ c⁰₁

  private
    module CatDef (C₁ C₂ : C.Cat) where
      ⁰ : Set
      ⁰ = C₁ C.⇒¹ C₂

      ¹×² : ⁰ → ⁰ → S.Std
      ¹×² = C.M₂.std

      idn⇒ : {m¹₁ : ⁰} → S.⊤ S.⇒ ¹×² m¹₁ m¹₁
      idn⇒ = S.M.elm (C.M₂.idn _)

      cmp⇒ : {m¹₁ m¹₂ m¹₃ : ⁰} → ¹×² m¹₂ m¹₃ S.× ¹×² m¹₁ m¹₂ S.⇒ ¹×² m¹₁ m¹₃
      cmp⇒ {f₁} {f₂} {f₃} = record
        { _·⁰_ = C.M₂.cmp
        ; _·¹_ = λ { (c²₂ , c²₁) → C.cmp¹ C₂ (c²₂ , c²₁) }
        }

      isCat : C.IsCat ⁰ ¹×² idn⇒ cmp⇒
      isCat = record
        { l-cmp⁰-idn₁ = C.l-cmp⁰-idn₁ C₂
        ; l-cmp⁰-idn₂ = C.l-cmp⁰-idn₂ C₂
        ; l-cmp⁰-ass  = C.l-cmp⁰-ass  C₂
        }

  cat : C.Cat → C.Cat → C.Cat
  cat C₁ C₂ = record
    { ⁰     = ⁰
    ; ¹×²   = ¹×²
    ; idn⇒  = idn⇒
    ; cmp⇒  = cmp⇒
    ; isCat = isCat
    }
    where
      open CatDef C₁ C₂

  std : C.Cat → C.Cat → S.Std
  std C₁ C₂ = C.I.std (cat C₁ C₂)

open import 1-CatThy.Core.Boot.Map₁ public
