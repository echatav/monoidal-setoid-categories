{-# OPTIONS --type-in-type #-}
module 1-CatThy.Obj.Prd.Core where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

open import 1-CatThy.Core

module O where
  record IsPrd
    (A     : C.Cat)
    (_×_   : C.obj A → C.obj A → C.obj A)
    (π₁    : {a₁ a₂ : C.obj A} → C.hom A (a₁ × a₂) a₁)
    (π₂    : {a₁ a₂ : C.obj A} → C.hom A (a₁ × a₂) a₂)
    (⟨_,_⟩ : {a₁ a₂ a₃ : C.obj A}
      → C.hom A a₃ a₁
      → C.hom A a₃ a₂
      → C.hom A a₃ (a₁ × a₂))
      : Set
    where
      private
        module c = C.Cat A

      field
        l-π₁-β : {a₁ a₂ a₃ : c.obj}
          → {f₁ : c.hom a₃ a₁}
          → {f₂ : c.hom a₃ a₂}
          → S.[ c.* ] π₁ c.∘ ⟨ f₁ , f₂ ⟩ ≃ f₁

        l-π₂-β : {a₁ a₂ a₃ : c.obj}
          → {f₁ : c.hom a₃ a₁}
          → {f₂ : c.hom a₃ a₂}
          → S.[ c.* ] π₂ c.∘ ⟨ f₁ , f₂ ⟩ ≃ f₂

        l-⟨,⟩-ump  : {a₁ a₂ a₃ : c.obj}
          → {f₁ : c.hom a₃ a₁}
          → {f₂ : c.hom a₃ a₂}
          → {u  : c.hom a₃ (a₁ × a₂)}
          → S.[ c.* ] π₁ c.∘ u ≃ f₁
          → S.[ c.* ] π₂ c.∘ u ≃ f₂
          → S.[ c.* ] ⟨ f₁ , f₂ ⟩ ≃ u

      l-⟨,⟩-η-g : {a₁ a₂ a₃ : c.obj} {f : c.hom a₃ (a₁ × a₂)}
        → S.[ c.* ] ⟨ π₁ c.∘ f , π₂ c.∘ f ⟩ ≃ f
      l-⟨,⟩-η-g = l-⟨,⟩-ump (S.idn c.*) (S.idn c.*)

      l-⟨,⟩-∘ : {a₁ a₂ a₃ a₄ : c.obj}
        → {f₁ : c.hom a₃ a₁}
        → {f₂ : c.hom a₃ a₂}
        → {f  : c.hom a₄ a₃}
        → S.[ c.* ] ⟨ f₁ , f₂ ⟩ c.∘ f ≃ ⟨ f₁ c.∘ f , f₂ c.∘ f ⟩
      l-⟨,⟩-∘ =
        S.[ c.* ]
          l-⟨,⟩-ump
            (S.[ c.* ] c.cmp* S.⩪ (l-π₁-β , S.idn c.*) ∘ S.[ c.* ] c.l-cmp ⁻¹)
            (S.[ c.* ] c.cmp* S.⩪ (l-π₂-β , S.idn c.*) ∘ S.[ c.* ] c.l-cmp ⁻¹)
        ⁻¹

  record Prd (A : C.Cat) : Set where
    private
      module c = C.Cat A

    field
      _×_ : c.obj → c.obj → c.obj
      π₁ : {a₁ a₂ : c.obj} → c.hom (a₁ × a₂) a₁
      π₂ : {a₁ a₂ : c.obj} → c.hom (a₁ × a₂) a₂
      ⟨,⟩* : {a₁ a₂ a₃ : c.obj} →
        c.hom* a₁ a₂ S.× c.hom* a₁ a₃ S.⇒ c.hom* a₁ (a₂ × a₃)

    ⟨_,_⟩ : {a₁ a₂ a₃ : c.obj}
      → c.hom a₁ a₂
      → c.hom a₁ a₃
      → c.hom a₁ (a₂ × a₃)
    ⟨_,_⟩ f₁ f₂ = ⟨,⟩* S.· (f₁ , f₂)

    field
      isPrd : IsPrd A _×_ π₁ π₂ ⟨_,_⟩

    open IsPrd isPrd public

    ⟨×⟩* : {a₁ a₂ a₃ a₄ : C.obj A} →
      c.hom* a₁ a₃ S.× c.hom* a₂ a₄ S.⇒ c.hom* (a₁ × a₂) (a₃ × a₄)
    ⟨×⟩* = ⟨,⟩* S.M.∘
             S.⟨ c.cmp* S.M.∘ S.⟨ S.M.idn , S.M.elm {c.*} {c.*} π₁ ⟩
               × c.cmp* S.M.∘ S.⟨ S.M.idn , S.M.elm {c.*} {c.*} π₂ ⟩ ⟩

    ⟨_×_⟩ : {a₁ a₂ a₃ a₄ : C.obj A}
      → c.hom a₁ a₃
      → c.hom a₂ a₄
      → c.hom (a₁ × a₂) (a₃ × a₄)
    ⟨_×_⟩ f₁ f₂ = ⟨×⟩* S.· (f₁ , f₂)

    l-⟨,⟩-η : {a₁ a₂ : c.obj}
      → S.[ c.* ] ⟨ π₁ , π₂ ⟩ ≃ c.idn {a₁ × a₂}
    l-⟨,⟩-η = S.[ c.* ] l-⟨,⟩-η-g
            ∘ ⟨,⟩* S.⩪ (S.[ c.* ] c.l-idn₂ ⁻¹ , S.[ c.* ] c.l-idn₂ ⁻¹)

    [_]_×_ : _
    [_]_×_ = _×_

    [_]⟨_,_⟩ : {a₁ a₂ a₃ : c.obj}
      → c.hom a₁ a₂
      → c.hom a₁ a₃
      → c.hom a₁ (a₂ × a₃)
    [_]⟨_,_⟩ f₁ f₂ = ⟨_,_⟩ f₁ f₂

    [_]⟨_×_⟩ : {a₁ a₂ a₃ a₄ : C.obj A}
      → c.hom a₁ a₃
      → c.hom a₂ a₄
      → c.hom (a₁ × a₂) (a₃ × a₄)
    [_]⟨_×_⟩ f₁ f₂ = ⟨_×_⟩ f₁ f₂
  open Prd public

