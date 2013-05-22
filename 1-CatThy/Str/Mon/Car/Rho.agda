{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd as C
import 1-CatThy.Obj.Trm as C

module 1-CatThy.Str.Mon.Car.Rho
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

ρ : C.[ C.M₁.cat A A ]
         ⊗ C.M₁.∘ C.⟨ C.M₁.idn A , C.M₁.elm {A} one ⟩
       ≅ C.M₁.idn A
ρ = record
  { fwd   = record
    { com   = λ _ → o.π₁
    ; l-nat = S.[ C.* A ] o.l-π₁-β ⁻¹
    }
  ; bwd   = record
    { com   = λ _ → o.⟨ C.idn A , o.! ⟩
    ; l-nat = λ {a₁} {a₂} {m} → let open S.Eq c.* in
        proof

              o.⟨ m c.∘ o.π₁ , c.idn c.∘ o.π₂ ⟩ c.∘ o.⟨ c.idn , o.! ⟩

        {- ∘ distributes over ⟨,⟩-}
        ↝⟨ o.l-⟨,⟩-∘ ⟩

              o.⟨ (m     c.∘ o.π₁) c.∘ o.⟨ c.idn , o.! ⟩
                , (c.idn c.∘ o.π₂) c.∘ o.⟨ c.idn , o.! ⟩ ⟩

        {- associativity; β-reduction -}
        ↝⟨ o.⟨,⟩* S.⩪
             ( S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ∘ c.l-cmp
             , S.[ c.* ] c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ∘ c.l-cmp) ⟩

              o.⟨ m c.∘ c.idn , c.idn c.∘ o.! ⟩

        {- identity laws; universal property for ! -}
        ↝⟨ o.⟨,⟩* S.⩪
             ( S.[ c.* ] S.[ c.* ] c.l-idn₁  ⁻¹ ∘ c.l-idn₂
             , S.[ c.* ] S.[ c.* ] o.l-!-ump ⁻¹ ∘ c.l-idn₁ ) ⟩

              o.⟨ c.idn c.∘ m , o.! c.∘ m ⟩

        {- ∘ distributes over ⟨,⟩ -}
        ↜⟨ o.l-⟨,⟩-∘ ⟩

              o.⟨ c.idn , o.! ⟩ c.∘ m

        ∎
    }
  ; isIso = record
    { l-fwd = λ {a} → let open S.Eq c.* in
        proof

              o.⟨ c.idn , o.! ⟩ c.∘ o.π₁

        {- ∘ distributes over ⟨,⟩ -}
        ↝⟨ o.l-⟨,⟩-∘ ⟩

              o.⟨ c.idn c.∘ o.π₁ , o.! c.∘ o.π₁ ⟩

        {- left identity law; universal property of ! -}
        ↝⟨ o.⟨,⟩* S.⩪
             ( c.l-idn₁
             , S.[ c.* ] S.[ c.* ] o.l-!-ump ⁻¹ ∘ o.l-!-ump ) ⟩

              o.⟨ o.π₁ , o.π₂ ⟩

        {- η-contraction for ⟨,⟩ -}
        ↝⟨ o.l-⟨,⟩-η ⟩

              c.idn

        ∎
    ; l-bwd = o.l-π₁-β
    }
  }
