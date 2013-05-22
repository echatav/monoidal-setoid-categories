{-# OPTIONS --type-in-type #-}
module 1-CatThy.Str.CwF where

open import Bundle.1-CatThy

import 1-CatThy.Cat.Fam.Rel    as C
import 1-CatThy.Cat.Op         as C
import 1-CatThy.Cat.STD        as C
import 1-CatThy.Obj.CwF.CtxCmp as C
import 1-CatThy.Obj.Trm        as C

record CwF (A : C.Cat) : Set where
  field
    trm : C.O.Trm A
    T   : C.Op A C.⇒₁ C.FAM C.STD
    ctx : C.O.CtxCmp A T

  open   C.O.Trm                   trm public
  import 1-CatThy.Str.CwF.Core
  open   1-CatThy.Str.CwF.Core A T     public
  open   C.O.CtxCmp            A T ctx public

  ◇ : Ctx
  ◇ = ⊤
open CwF public
