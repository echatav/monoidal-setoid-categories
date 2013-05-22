{-# OPTIONS --type-in-type #-}
module 1-CatThy.Core.Prd where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Core.Map₁ as C
import 1-CatThy.Core.Cat  as C

infixr 1 _×_

private
  module PrdDef (C₁ C₂ : C.Cat) where
    ⁰ : Set
    ⁰ = C.⁰ C₁ P.× C.⁰ C₂

    ¹×² : ⁰ → ⁰ → S.Std
    ¹×² (c⁰₁₁ , c⁰₁₂) (c⁰₂₁ , c⁰₂₂) = C.¹×² C₁ c⁰₁₁ c⁰₂₁ S.× C.¹×² C₂ c⁰₁₂ c⁰₂₂

    idn⇒ : {c⁰₁ : ⁰} → S.⊤ S.⇒ ¹×² c⁰₁ c⁰₁
    idn⇒ = S.⟨ C.idn⇒ C₁ , C.idn⇒ C₂ ⟩

    cmp⇒ : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → ¹×² c⁰₂ c⁰₃ S.× ¹×² c⁰₁ c⁰₂ S.⇒ ¹×² c⁰₁ c⁰₃
    cmp⇒ = S.⟨       C.cmp⇒ C₁
               S.M.∘ S.⟨   S.π₁ {C.¹×²? C₁} (C.¹×²? C₂)
                         × S.π₁ {C.¹×²? C₁} (C.¹×²? C₂) ⟩
             ,       C.cmp⇒ C₂
               S.M.∘ S.⟨   S.π₂ (C.¹×²? C₁) {C.¹×²? C₂}
                         × S.π₂ (C.¹×²? C₁) {C.¹×²? C₂} ⟩
             ⟩

  module IsPrdDef (C₁ C₂ : C.Cat) where
    open PrdDef C₁ C₂

    l-cmp⁰-idn₁ : {c⁰₁ c⁰₂ : ⁰} {c¹₁ : S.⁰ (¹×² c⁰₁ c⁰₂)}
      → S.¹ (¹×² c⁰₁ c⁰₂) (cmp⇒ S.·⁰ ((idn⇒ S.·⁰ _) , c¹₁)) c¹₁
    l-cmp⁰-idn₁ = C.l-cmp⁰-idn₁ C₁ , C.l-cmp⁰-idn₁ C₂

    l-cmp⁰-idn₂ : {c⁰₁ c⁰₂ : ⁰} {c¹₁ : S.⁰ (¹×² c⁰₁ c⁰₂)}
      → S.¹ (¹×² c⁰₁ c⁰₂) (cmp⇒ S.·⁰ (c¹₁ , (idn⇒ S.·⁰ _))) c¹₁
    l-cmp⁰-idn₂ = C.l-cmp⁰-idn₂ C₁ , C.l-cmp⁰-idn₂ C₂

    l-cmp⁰-ass : {c⁰₁ c⁰₂ c⁰₃ c⁰₄ : ⁰}
            → {c¹₃ : S.⁰ (¹×² c⁰₃ c⁰₄)}
            → {c¹₂ : S.⁰ (¹×² c⁰₂ c⁰₃)}
            → {c¹₁ : S.⁰ (¹×² c⁰₁ c⁰₂)}
            → S.¹ (¹×² c⁰₁ c⁰₄)
                (cmp⇒ S.·⁰ ((cmp⇒ S.·⁰ (c¹₃ , c¹₂)) , c¹₁))
                (cmp⇒ S.·⁰ (c¹₃ , (cmp⇒ S.·⁰ (c¹₂ , c¹₁))))
    l-cmp⁰-ass = C.l-cmp⁰-ass C₁ , C.l-cmp⁰-ass C₂

    isCat : C.IsCat ⁰ ¹×² idn⇒ cmp⇒
    isCat = record
      { l-cmp⁰-idn₁ = l-cmp⁰-idn₁
      ; l-cmp⁰-idn₂ = l-cmp⁰-idn₂
      ; l-cmp⁰-ass  = l-cmp⁰-ass
      }

_×_ : C.Cat → C.Cat → C.Cat
C₁ × C₂ = record
  { ⁰   = ⁰
  ; ¹×²  = ¹×²
  ; idn⇒  = idn⇒
  ; cmp⇒  = cmp⇒
  ; isCat = isCat
  }
  where
    open   PrdDef C₁ C₂
    open IsPrdDef C₁ C₂

π₁ : {C₁ : C.Cat} (C₂ : C.Cat) → C₁ × C₂ C.⇒¹ C₁
π₁ {C₁} C₂ = record
  { _·⁰_   = P.π₁
  ; _·¹×²_ = S.π₁ (C.¹×²? C₂)
  ; is-⇒¹  = record
    { l-⇒¹×²-idn = S.idn (C.¹×²? C₁)
    ; l-⇒¹×²-cmp = S.idn (C.¹×²? C₁)
    }
  }

π₂ : (C₁ : C.Cat) {C₂ : C.Cat} → C₁ × C₂ C.⇒¹ C₂
π₂ C₁ {C₂} = record
  { _·⁰_   = P.π₂
  ; _·¹×²_ = S.π₂ (C.¹×²? C₁)
  ; is-⇒¹ = record
    { l-⇒¹×²-idn = S.idn (C.¹×²? C₂)
    ; l-⇒¹×²-cmp = S.idn (C.¹×²? C₂)
    }
  }

⟨_,_⟩ : {C₁ C₂ C₃ : C.Cat} → C₃ C.⇒¹ C₁ → C₃ C.⇒¹ C₂ → C₃ C.⇒¹ C₁ × C₂
⟨ m¹₁ , m¹₂ ⟩ = record
  { _·⁰_   = P.⟨ C._·⁰_   m¹₁ , C._·⁰_   m¹₂ ⟩
  ; _·¹×²_ = S.⟨ C._·¹×²_ m¹₁ , C._·¹×²_ m¹₂ ⟩
  ; is-⇒¹  = record
    { l-⇒¹×²-idn = C.l-⇒¹×²-idn m¹₁ , C.l-⇒¹×²-idn m¹₂
    ; l-⇒¹×²-cmp = C.l-⇒¹×²-cmp m¹₁ , C.l-⇒¹×²-cmp m¹₂
    }
  }

⟨_×_⟩ : {C₁ C₂ C₃ C₄ : C.Cat} → C₁ C.⇒¹ C₃ → C₂ C.⇒¹ C₄ → C₁ × C₂ C.⇒¹ C₃ × C₄
⟨ m¹₁ × m¹₂ ⟩ = record
  { _·⁰_   = P.⟨ C._·⁰_   m¹₁ × C._·⁰_   m¹₂ ⟩
  ; _·¹×²_ = S.⟨ C._·¹×²_ m¹₁ × C._·¹×²_ m¹₂ ⟩
  ; is-⇒¹ = record
    { l-⇒¹×²-idn = C.l-⇒¹×²-idn m¹₁ , C.l-⇒¹×²-idn m¹₂
    ; l-⇒¹×²-cmp = C.l-⇒¹×²-cmp m¹₁ , C.l-⇒¹×²-cmp m¹₂
    }
  }

×-ass : (C₁ C₂ C₃ : C.Cat) → (C₁ × C₂) × C₃ C.⇒¹ C₁ × (C₂ × C₃)
×-ass C₁ C₂ C₃ =
  ⟨ π₁ {C₁}      C₂ C.M₁.∘
    π₁ {C₁ × C₂} C₃
  , ⟨ π₂ C₁        {C₂} C.M₁.∘
      π₁ {C₁ × C₂}  C₃
    , π₂ (C₁ × C₂) {C₃} ⟩
  ⟩
