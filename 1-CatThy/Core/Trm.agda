{-# OPTIONS --type-in-type #-}
module 1-CatThy.Core.Trm where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Core.Map₁ as C
import 1-CatThy.Core.Cat  as C

⊤ : C.Cat
⊤ = record
  { ⁰     =         P.⊤
  ; ¹×²   = λ _ _ → S.⊤
  ; idn⇒  = _
  ; cmp⇒  = _
  ; isCat = _
  }

! : {C : C.Cat} → C C.⇒¹ ⊤
! = _
