{-# OPTIONS --type-in-type #-}
open import Bundle.1-CatThy

import 1-CatThy.Obj.Prd.Core as C

module 1-CatThy.Obj.Prd.Map₁ (A : C.Cat) (φ : C.O.Prd A) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

private
  module ×-⇒₁Def where
    module c = C.Cat   A
    module o = C.O.Prd φ

    o⇒ : C.obj (A C.× A) → C.obj A
    o⇒ (a₁ , a₂) = a₁ o.× a₂

    h⇒ : {a₁ a₂ : _} → C.hom* (A C.× A) a₁ a₂ S.⇒ C.hom* A (o⇒ a₁) (o⇒ a₂)
    h⇒ = o.⟨×⟩*

    l-h⇒-cmp₁ : {a₁ a₂ a₃ : _}
      → {m₂ : C.hom (A C.× A) a₂ a₃}
      → {m₁ : C.hom (A C.× A) a₁ a₂}
      → S.[ c.* ]
                 o.π₁
            c.∘ (o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩)
          ≃     (P.π₁ m₂
            c.∘  P.π₁ m₁)
            c.∘  o.π₁
    l-h⇒-cmp₁ {_} {_} {_} {m₂} {m₁} = let open S.Eq c.* in
      proof

                 o.π₁
            c.∘ (o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩)

      {- associativity -}
      ↜⟨ c.l-cmp ⟩

                (o.π₁
            c.∘  o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩)
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩

      {- β-reduction -}
      ↝⟨ c.cmp* S.⩪ (o.l-π₁-β , S.idn c.*) ⟩

                (P.π₁ m₂
            c.∘  o.π₁)
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩

      {- associativity -}
      ↝⟨ c.l-cmp ⟩

                 P.π₁ m₂
            c.∘ (o.π₁
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩)

      {- β-reduction -}
      ↝⟨ c.cmp* S.⩪ (S.idn c.* , o.l-π₁-β) ⟩

                 P.π₁ m₂
            c.∘ (P.π₁ m₁
            c.∘  o.π₁)

      {- associativity -}
      ↜⟨ c.l-cmp ⟩

                (P.π₁ m₂
            c.∘  P.π₁ m₁)
            c.∘  o.π₁

      ∎

    l-h⇒-cmp₂ : {a₁ a₂ a₃ : _}
      → {m₂ : C.hom (A C.× A) a₂ a₃}
      → {m₁ : C.hom (A C.× A) a₁ a₂}
      → S.[ c.* ]
                 o.π₂
            c.∘ (o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩)
          ≃     (P.π₂ m₂
            c.∘  P.π₂ m₁)
            c.∘  o.π₂
    l-h⇒-cmp₂ {_} {_} {_} {m₂} {m₁} = let open S.Eq c.* in
      proof

                 o.π₂
            c.∘ (o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩)

      {- associativity -}
      ↜⟨ c.l-cmp ⟩

                (o.π₂
            c.∘  o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩)
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩

      {- β-reduction -}
      ↝⟨ c.cmp* S.⩪ (o.l-π₂-β , S.idn c.*) ⟩

                (P.π₂ m₂
            c.∘  o.π₂)
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩

      {- associativity -}
      ↝⟨ c.l-cmp ⟩

                 P.π₂ m₂
            c.∘ (o.π₂
            c.∘  o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩)

      {- β-reduction -}
      ↝⟨ c.cmp* S.⩪ (S.idn c.* , o.l-π₂-β) ⟩

                 P.π₂ m₂
            c.∘ (P.π₂ m₁
            c.∘  o.π₂)

      {- associativity -}
      ↜⟨ c.l-cmp ⟩

                (P.π₂ m₂
            c.∘  P.π₂ m₁)
            c.∘  o.π₂

      ∎

    is-⇒₁ : C.Is-⇒₁ (A C.× A) A o⇒ h⇒
    is-⇒₁ = record
      { l-h⇒-idn = λ {a} → let open S.Eq c.* in
          proof

                o.⟨×⟩* S.· C.idn (A C.× A)

          {- calculation -}
          ↭

                o.⟨ c.idn c.∘ o.π₁ , c.idn c.∘ o.π₂ ⟩

          {- commutativity of identity in both arguments of ⟨_,_⟩ -}
          ↝⟨     o.⟨,⟩*
             S.⩪ ( S.[ c.* ] S.[ c.* ] c.l-idn₂ ⁻¹ ∘ c.l-idn₁
                 , S.[ c.* ] S.[ c.* ] c.l-idn₂ ⁻¹ ∘ c.l-idn₁ )
           ⟩
                o.⟨ o.π₁ c.∘ c.idn , o.π₂ c.∘ c.idn ⟩

          {- universal mapping property for _×_ -}
          ↝⟨ o.l-⟨,⟩-ump (S.idn c.*) (S.idn c.*) ⟩

                c.idn

          ∎
      ; l-h⇒-cmp = λ {_} {_} {_} {m₂} {m₁} → let open S.Eq c.* in
          proof

                o.⟨×⟩* S.· (C.[ A C.× A ] m₂ ∘ m₁)

          {- calculation  -}
          ↭

                o.⟨ (P.π₁ m₂ c.∘ P.π₁ m₁) c.∘ o.π₁
                  , (P.π₂ m₂ c.∘ P.π₂ m₁) c.∘ o.π₂ ⟩

          {- universal mapping property of _×_ with lemmas -}
          ↝⟨ o.l-⟨,⟩-ump l-h⇒-cmp₁ l-h⇒-cmp₂ ⟩

                    o.⟨ P.π₁ m₂ c.∘ o.π₁ , P.π₂ m₂ c.∘ o.π₂ ⟩
                c.∘ o.⟨ P.π₁ m₁ c.∘ o.π₁ , P.π₂ m₁ c.∘ o.π₂ ⟩

          {- calculation  -}
          ↭

                o.⟨×⟩* S.· m₂ c.∘ o.⟨×⟩* S.· m₁

          ∎
      }

module O where
  ×-⇒₁ : A C.× A C.⇒₁ A
  ×-⇒₁ = record
    { o⇒    = o⇒
    ; h⇒    = h⇒
    ; is-⇒₁ = is-⇒₁
    }
    where
      open ×-⇒₁Def
