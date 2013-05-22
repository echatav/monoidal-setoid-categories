{-# OPTIONS --type-in-type #-}
module 1-CatThy.Str.Mon.Core where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy
open import Bundle.1-CatThy

record IsMon
  (A   : C.Cat)
  (one : C.obj A)
  (⊗   : A C.× A C.⇒₁ A)
  (λ′  :
       C.[ C.M₁.cat A A ]
           ⊗ C.M₁.∘ C.⟨ C.M₁.elm {A} one , C.M₁.idn A ⟩
         ≅ C.M₁.idn A)
  (ρ   :
       C.[ C.M₁.cat A A ]
           ⊗ C.M₁.∘ C.⟨ C.M₁.idn A , C.M₁.elm {A} one ⟩
         ≅ C.M₁.idn A)
  (α   :
       C.[ C.M₁.cat ((A C.× A) C.× A) A ]
            ⊗ C.M₁.∘ C.⟨ ⊗ × C.M₁.idn A ⟩
         ≅ (⊗ C.M₁.∘ C.⟨ C.M₁.idn A × ⊗ ⟩) C.M₁.∘ C.×-α A A A)
    : Set
  where
    field
      l-coh-pnt : {a₁ a₂ a₃ a₄ : C.obj A} →
        S.[ C.* A ]
            C.[ A ] C.com (C.I.fwd α) ((a₁ , a₂) , C.o⇒ ⊗ (a₃ , a₄))
                  ∘ C.com (C.I.fwd α) ((C.o⇒ ⊗ (a₁ , a₂) , a₃) , a₄)
          ≃ C.[ A ] C.h⇒ ⊗ S.· (C.idn A , C.com (C.I.fwd α) ((a₂ , a₃) , a₄))
                  ∘ (C.[ A ] C.com (C.I.fwd α) ((a₁ , C.o⇒ ⊗ (a₂ , a₃)) , a₄)
                           ∘ C.h⇒ ⊗ S.· ( C.com (C.I.fwd α) ((a₁ , a₂) , a₃)
                                        , C.idn A))
      l-coh-tri : {a₁ a₂ : C.obj A} →
        S.[ C.* A ]
            C.[ A ] C.h⇒ ⊗ S.· (C.idn A , C.com (C.I.fwd λ′) a₂)
                  ∘ C.com (C.I.fwd α) ((C.o⇒ (C.M₁.idn A) a₁ , one) , a₂)
          ≃ C.h⇒ ⊗ S.· (C.com (C.I.fwd ρ) a₁ , C.idn A)

record Mon (A : C.Cat) : Set where
  field
    one : C.obj A
    ⊗   : A C.× A C.⇒₁ A
    λ′  : C.[ C.M₁.cat A A ]
              ⊗ C.M₁.∘ C.⟨ C.M₁.elm {A} one , C.M₁.idn A ⟩
            ≅ C.M₁.idn A
    ρ   : C.[ C.M₁.cat A A ]
              ⊗ C.M₁.∘ C.⟨ C.M₁.idn A , C.M₁.elm {A} one ⟩
            ≅ C.M₁.idn A
    α   : C.[ C.M₁.cat ((A C.× A) C.× A) A ]
               ⊗ C.M₁.∘ C.⟨ ⊗ × C.M₁.idn A ⟩
            ≅ ((⊗ C.M₁.∘ C.⟨ C.M₁.idn A × ⊗ ⟩) C.M₁.∘ C.×-α A A A)
    isMon : IsMon A one ⊗ λ′ ρ α
