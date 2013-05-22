{-# OPTIONS --type-in-type #-}
import 1-CatThy.Core.Cat as C

module 1-CatThy.Core.Iso where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

open import PreThy.Prd
  using
    ( _,_ )

module I where
  infix 0 [_]_≅_

  record IsIso
    (C       : C.Cat)
    {c⁰₁ c⁰₂ : C.⁰ C}
    (fwd     : C.¹ C c⁰₁ c⁰₂)
    (bwd     : C.¹ C c⁰₂ c⁰₁)
      : Set
    where
      field
        l-fwd : C.² C (C.[ C ] bwd ∘⁰ fwd) (C.idn⁰ C)
        l-bwd : C.² C (C.[ C ] fwd ∘⁰ bwd) (C.idn⁰ C)

  record [_]_≅_ (C : C.Cat) (c⁰₁ c⁰₂ : C.⁰ C) : Set where
    field
      fwd   : C.¹ C c⁰₁ c⁰₂
      bwd   : C.¹ C c⁰₂ c⁰₁
      isIso : IsIso C fwd bwd

    open IsIso isIso public
  open [_]_≅_ public

  private
    module StdDef (C : C.Cat) where
      module nC = C.Cat C

      ⁰ : Set
      ⁰ = nC.⁰

      ¹ : ⁰ → ⁰ → Set
      ¹ = [_]_≅_ C

      idn : {c⁰₁ : ⁰} → ¹ c⁰₁ c⁰₁
      idn {c⁰₁} = record
        { fwd   = nC.idn⁰
        ; bwd   = nC.idn⁰
        ; isIso = record
          { l-fwd = nC.l-cmp⁰-idn₁
          ; l-bwd = nC.l-cmp⁰-idn₂
          }
        }

      cmp : {c⁰₁ c⁰₂ c⁰₃ : ⁰} → ¹ c⁰₂ c⁰₃ P.× ¹ c⁰₁ c⁰₂ → ¹ c⁰₁ c⁰₃
      cmp {c⁰₁} {c⁰₂} {c⁰₃} (c¹₂ , c¹₁) = record
        { fwd   = fwd c¹₂ nC.∘⁰ fwd c¹₁
        ; bwd   = bwd c¹₁ nC.∘⁰ bwd c¹₂
        ; isIso = record
          { l-fwd = let open S.Eq nC.¹×²? in
              proof

                    (bwd c¹₁ nC.∘⁰ bwd c¹₂) nC.∘⁰ (fwd c¹₂ nC.∘⁰ fwd c¹₁)

              {- associativity -}
              ↝⟨ nC.l-cmp⁰-ass ⟩

                    bwd c¹₁ nC.∘⁰ (bwd c¹₂ nC.∘⁰ (fwd c¹₂ nC.∘⁰ fwd c¹₁))

              {- associativity -}
              ↝⟨ S.idn nC.¹×²? nC.∘¹ S.inv nC.¹×²? nC.l-cmp⁰-ass ⟩

                    bwd c¹₁ nC.∘⁰ ((bwd c¹₂ nC.∘⁰ fwd c¹₂) nC.∘⁰ fwd c¹₁)

              {- bwd c¹₂ ∘ fwd c¹₂ is identity -}
              ↝⟨ S.idn nC.¹×²? nC.∘¹ (l-fwd c¹₂ nC.∘¹ S.idn nC.¹×²?) ⟩

                    bwd c¹₁ nC.∘⁰ (nC.idn⁰ nC.∘⁰ fwd c¹₁)

              {- left identity law -}
              ↝⟨ S.idn nC.¹×²? nC.∘¹ nC.l-cmp⁰-idn₁ ⟩

                    C.[ C ] bwd c¹₁ ∘⁰ fwd c¹₁

              {- bwd c¹₁ ∘ fwd c¹₁ is identity -}
              ↝⟨ l-fwd c¹₁ ⟩

                    nC.idn⁰

              ∎

          ; l-bwd = let open S.Eq nC.¹×²? in
              proof

                    ((fwd c¹₂ nC.∘⁰ fwd c¹₁)) nC.∘⁰ (bwd c¹₁ nC.∘⁰ bwd c¹₂)

              {- associativity -}
              ↝⟨ nC.l-cmp⁰-ass ⟩

                    fwd c¹₂ nC.∘⁰ (fwd c¹₁ nC.∘⁰ (bwd c¹₁ nC.∘⁰ bwd c¹₂))

              {- associativity -}
              ↝⟨ S.idn nC.¹×²? nC.∘¹ S.inv nC.¹×²? nC.l-cmp⁰-ass ⟩

                    fwd c¹₂ nC.∘⁰ (((fwd c¹₁ nC.∘⁰ bwd c¹₁)) nC.∘⁰ bwd c¹₂)

              {- fwd c¹₁ ∘ bwd c¹₁ is identity -}
              ↝⟨ S.idn nC.¹×²? nC.∘¹ (l-bwd c¹₁ nC.∘¹ S.idn nC.¹×²?) ⟩

                    fwd c¹₂ nC.∘⁰ (nC.idn⁰ nC.∘⁰ bwd c¹₂)

              {- left identity law -}
              ↝⟨ S.idn nC.¹×²? nC.∘¹ nC.l-cmp⁰-idn₁ ⟩

                    fwd c¹₂ nC.∘⁰ bwd c¹₂

              {- fwd c¹₂ ∘ bwd c¹₂ is identity -}
              ↝⟨ l-bwd c¹₂ ⟩

                    nC.idn⁰

              ∎
          }
        }

      inv : {c⁰₁ c⁰₂ : ⁰} → ¹ c⁰₁ c⁰₂ → ¹ c⁰₂ c⁰₁
      inv {c⁰₁} {c⁰₂} m = record
        { fwd   = bwd m
        ; bwd   = fwd m
        ; isIso = record
          { l-fwd = l-bwd m
          ; l-bwd = l-fwd m
          }
        }

  std : (C : C.Cat) → S.Std
  std C = record
    { ⁰ = ⁰
    ; ¹ = ¹
    ; idn = λ {c⁰} → idn {c⁰}
    ; cmp = λ {c⁰₁} {c⁰₂} {c⁰₃} → cmp {c⁰₁} {c⁰₂} {c⁰₃}
    ; inv = λ {c⁰₁} {c⁰₂} → inv {c⁰₁} {c⁰₂}
    }
    where
      open StdDef C

open I public
  using
    ( [_]_≅_ )
