{-# OPTIONS --type-in-type #-}
module PreThy.Trm where

import PreThy.Map as P

record ⊤ : Set where
  constructor tt

! : {A : Set} → A P.⇒ ⊤
! _ = tt
