{-# OPTIONS --type-in-type #-}
open import Bundle.StdThy
open import Bundle.1-CatThy

import 1-CatThy.Cat.Fam.Rel  as C
import 1-CatThy.Cat.Op       as C
import 1-CatThy.Cat.STD      as C
import 1-CatThy.Str.CwF.Core

module 1-CatThy.Obj.CwF.CtxCmp (C : C.Cat) (T : C.Op C C.⇒₁ C.FAM C.STD) where
open 1-CatThy.Str.CwF.Core C T

module O where
  record IsCtxCmp
    (_▸_ : (Γ : Ctx) → Tp Γ → Ctx)
    (wkn : (Γ : Ctx) (A : Tp Γ) → Sub (Γ ▸ A) Γ)
    (var : (Γ : Ctx) (A : Tp Γ) → Tm (Γ ▸ A) (A Tp[ wkn Γ A ]))
    (ext : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁)
      → Tm Γ₂ (A Tp[ γ ]) → Sub Γ₂ (Γ₁ ▸ A))
    : Set where
    open Coe _▸_ wkn var
    field
      l-wkn : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A Tp[ γ ]))
        → S.[ Sub* Γ₂ Γ₁ ] C.[ C ] wkn Γ₁ A ∘ ext γ A x ≃ γ

      l-var : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A Tp[ γ ]))
        → S.[ Tm* Γ₂ (A Tp[ γ ]) ]
                  C.F.* C.STD (T C.· Γ₂) (coe ext l-wkn γ A x)
              S.· (var Γ₁ A Tm[ ext γ A x ])
            ≃ x

      l-ump :
          (u     : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁)
            → Tm Γ₂ (A Tp[ γ ]) → Sub Γ₂ (Γ₁ ▸ A))
        → (φ-wkn : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A Tp[ γ ]))
            → S.[ Sub* Γ₂ Γ₁ ] C.[ C ] wkn Γ₁ A ∘ u γ A x ≃ γ)
        → (φ-var : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A Tp[ γ ]))
            → S.[ Tm* Γ₂ (A Tp[ γ ]) ]
                      C.F.* C.STD (T C.· Γ₂) (coe u φ-wkn γ A x)
                  S.· (var Γ₁ A Tm[ u γ A x ])
                ≃ x)
        → ({Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁) (x : Tm Γ₂ (A Tp[ γ ]))
            → S.[ Sub* Γ₂ (Γ₁ ▸ A) ] ext γ A x ≃ u γ A x)

  record CtxCmp : Set where
    field
      _▸_      : (Γ : Ctx) → Tp Γ → Ctx
      wkn      : (Γ : Ctx) (A : Tp Γ) → Sub (Γ ▸ A) Γ
      var      : (Γ : Ctx) (A : Tp Γ) → Tm (Γ ▸ A) (A Tp[ wkn Γ A ])
      ext      : {Γ₁ Γ₂ : Ctx} (γ : Sub Γ₂ Γ₁) (A : Tp Γ₁)
        → Tm Γ₂ (A Tp[ γ ]) → Sub Γ₂ (Γ₁ ▸ A)
      isCtxCmp : IsCtxCmp _▸_ wkn var ext

    open IsCtxCmp isCtxCmp public
  open CtxCmp public
