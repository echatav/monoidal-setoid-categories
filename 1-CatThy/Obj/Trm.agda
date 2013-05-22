{-# OPTIONS --type-in-type #-}
module 1-CatThy.Obj.Trm where

open import Bundle.StdThy
open import Bundle.1-CatThy

module O where
  record IsTrm
    (A : C.Cat)
    (⊤ : C.obj A)
    (! : {a : C.obj A} → C.hom A a ⊤)
      : Set where
    field
      l-!-ump : {a : C.obj A} {m : C.hom A a ⊤} → S.[ C.* A ] m ≃ !

  record Trm (A : C.Cat) : Set where
    field
      ⊤ : C.obj A
      ! : {a : C.obj A} → C.hom A a ⊤
      isTrm : IsTrm A ⊤ !
    open IsTrm isTrm public
