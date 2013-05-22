{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Lambda
  (A   : C.Cat)
  (trm : C.O.Trm A)
  (prd : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

import 1-CatThy.Str.Mon.Car.One    as CM
import 1-CatThy.Str.Mon.Car.Tensor as CM

private
  module c = C.Cat A
  module o where
    open C.O.Trm trm public
    open C.O.Prd prd public

  one : C.obj A
  one = CM.one  A trm

  ⊗ : A C.× A C.⇒₁ A
  ⊗ = CM.×-⇒₁ A prd

λ′ : C.[ C.M₁.cat A A ]
         ⊗ C.M₁.∘ C.⟨ C.M₁.elm {A} one , C.M₁.idn A ⟩
       ≅ C.M₁.idn A
λ′ = record
  { fwd   = record
    { com   = λ _ → o.π₂
    ; l-nat = S.[ c.* ] o.l-π₂-β ⁻¹
    }
  ; bwd   = record
    { com   = λ _ → o.⟨ o.! , C.idn A ⟩
    ; l-nat = λ {a₁} {a₂} {m} → let open S.Eq c.* in
        proof

              o.⟨ c.idn c.∘ o.π₁ , m c.∘ o.π₂ ⟩ c.∘ o.⟨ o.! , c.idn ⟩

        {- ∘ distributes over ⟨,⟩ -}
        ↝⟨ o.l-⟨,⟩-∘ ⟩

              o.⟨ (c.idn c.∘ o.π₁) c.∘ o.⟨ o.! , c.idn ⟩
                , (m     c.∘ o.π₂) c.∘ o.⟨ o.! , c.idn ⟩ ⟩

        {- assocativity; β-reduction -}
        ↝⟨ o.⟨,⟩* S.⩪
             ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
             , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp) ⟩

              o.⟨ c.idn c.∘ o.! , m c.∘ c.idn ⟩

        {- universal property for !; identity laws -}
        ↝⟨     o.⟨,⟩*
           S.⩪ ( S.[ c.* ] S.[ c.* ] o.l-!-ump ⁻¹ ∘ c.l-idn₁
               , S.[ c.* ] S.[ c.* ] c.l-idn₁  ⁻¹ ∘ c.l-idn₂ ) ⟩

              o.⟨ o.! c.∘ m , c.idn c.∘ m ⟩

        {- ∘ distributes over ⟨,⟩ -}
        ↜⟨ o.l-⟨,⟩-∘ ⟩

              o.⟨ o.! , c.idn ⟩ c.∘ m

        ∎
    }
  ; isIso = record
    { l-fwd = λ {a} → let open S.Eq c.* in
        proof

              o.⟨ o.! , c.idn ⟩ c.∘ o.π₂

        {- ∘ distributes over ⟨,⟩ -}
        ↝⟨ o.l-⟨,⟩-∘ ⟩

              o.⟨ o.! c.∘ o.π₂ , c.idn c.∘ o.π₂ ⟩

        {- universal property of !; left identity law -}
        ↝⟨ o.⟨,⟩* S.⩪
             ( S.[ c.* ] S.[ c.* ] o.l-!-ump ⁻¹ ∘ o.l-!-ump
             , c.l-idn₁) ⟩

              o.⟨ o.π₁ , o.π₂ ⟩

        {- η-contraction for ⟨,⟩ -}
        ↝⟨ o.l-⟨,⟩-η ⟩

              c.idn

        ∎
    ; l-bwd = o.l-π₂-β
    }
  }
