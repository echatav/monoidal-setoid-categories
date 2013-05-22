{-# OPTIONS --type-in-type #-}
module StdThy.Trm where

open import Bundle.PreThy

import StdThy.Boot.Map as S
import StdThy.Std      as S

⊤ : S.Std
⊤ = record
  { ⁰ =         P.⊤
  ; ¹ = λ _ _ → P.⊤
  }

! : {S : S.Std} → S S.⇒ ⊤
! = _
