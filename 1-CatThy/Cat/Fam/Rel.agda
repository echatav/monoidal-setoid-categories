{-# OPTIONS --type-in-type #-}
import 1-CatThy.Core.Cat as C

module 1-CatThy.Cat.Fam.Rel (A : C.Cat) where

open import Bundle.Prelude
open import Bundle.PreThy
open import Bundle.StdThy

private
  module c = C.Cat A

module F where
  infixr 0 _⇒_
  infix  0 _≃_

  record Fam : Set where
    field
      B   : S.Std

    private
      module s = S.Std B

    field
      fib : s.obj → c.obj
      ↑   : {b₁ b₂ : s.obj} → b₁ s.≃ b₂ → c.hom (fib b₁) (fib b₂)

    field
      l-idn : {b : s.obj} →
        S.[ c.* ] ↑ s.idn ≃ c.idn {fib b}

      l-cmp : {b₁ b₂ b₃ : s.obj} {φ₂ : b₂ s.≃ b₃} {φ₁ : b₁ s.≃ b₂} →
        S.[ c.* ] ↑ φ₂ c.∘ ↑ φ₁ ≃ ↑ (φ₂ s.∘ φ₁)

      l-inv₁ : {b₁ b₂ : s.obj} {φ : b₁ s.≃ b₂} →
        S.[ c.* ] ↑ (φ s.⁻¹) c.∘ ↑ φ ≃ c.idn

      l-inv₂ : {b₁ b₂ : s.obj} {φ : b₁ s.≃ b₂} →
        S.[ c.* ] ↑ φ c.∘ ↑ (φ s.⁻¹) ≃ c.idn
  open Fam public

  record _⇒_ (f₁ f₂ : Fam) : Set where
    field
      B⇒    : B f₁ S.⇒ B f₂
      fib⇒  : {b : S.obj (B f₁)} → c.hom (fib f₁ b) (fib f₂ (B⇒ S.· b))
      l-nat : {b₁ b₂ : S.obj (B f₁)} {φ : S.[ B f₁ ] b₁ ≃ b₂} →
        S.[ c.* {fib f₁ b₁} {fib f₂ (B⇒ S.· b₂)} ] fib⇒ c.∘ ↑ f₁ φ ≃ ↑ f₂ (B⇒ S.⩪ φ) c.∘ fib⇒
  open _⇒_ public

  record _≃_ {f₁ f₂ : Fam} (m₁ m₂ : f₁ ⇒ f₂) : Set where
    field
      B≃   : S.[ S.M.std (B f₁) (B f₂) ] B⇒ m₁ ≃ B⇒ m₂
      fib≃ : {b : S.obj (B f₁)} →
        S.[ c.* ] ↑ f₂ B≃ c.∘ fib⇒ m₁ {b} ≃ fib⇒ m₂ {b}
  open _≃_ public

  private
    module StdDef (f₁ f₂ : Fam) where
      idn : {m : f₁ ⇒ f₂} → m ≃ m
      idn {m} = record
        { B≃   = S.idn (B f₂)
        ; fib≃ = let open S.Eq c.* in
            proof

                  ↑ f₂ (S.idn (B f₂)) c.∘ fib⇒ m

            {- identity lifts to identity -}
            ↝⟨ c.cmp* S.⩪ (l-idn f₂ , S.idn c.*) ⟩

                  c.idn c.∘ fib⇒ m

            {- left identity law -}
            ↝⟨ c.l-idn₁ ⟩

                  fib⇒ m

            ∎
        }

      cmp : {m₁ m₂ m₃ : f₁ ⇒ f₂} → (m₂ ≃ m₃) P.× (m₁ ≃ m₂) → m₁ ≃ m₃
      cmp {m₁} {m₂} {m₃} (p₂ , p₁) = record
        { B≃   = S.[ B f₂ ] B≃ p₂ ∘ B≃ p₁
        ; fib≃ = let open S.Eq c.* in
            proof

                  ↑ f₂ (S.[ B f₂ ] B≃ p₂ ∘ B≃ p₁) c.∘ fib⇒ m₁

            {- ∘ lifts to ∘ -}
            ↝⟨ c.cmp* S.⩪ (S.[ c.* ] l-cmp f₂ ⁻¹ , S.idn c.*) ⟩

                  (↑ f₂ (B≃ p₂) c.∘ ↑ f₂ (B≃ p₁)) c.∘ fib⇒ m₁

            {- associativity -}
            ↝⟨ c.l-cmp ⟩

                  ↑ f₂ (B≃ p₂) c.∘ (↑ f₂ (B≃ p₁) c.∘ fib⇒ m₁)

            {- fiber map equivalence -}
            ↝⟨ c.cmp* S.⩪ (S.idn c.* , fib≃ p₁) ⟩

                  ↑ f₂ (B≃ p₂) c.∘ fib⇒ m₂

            {- fiber map equivalence -}
            ↝⟨ fib≃ p₂ ⟩

                  fib⇒ m₃

            ∎
        }

      inv : {m₁ m₂ : f₁ ⇒ f₂} → m₁ ≃ m₂ → m₂ ≃ m₁
      inv {m₁} {m₂} p = record
        { B≃   = S.[ B f₂ ] B≃ p ⁻¹
        ; fib≃ = let open S.Eq c.* in
            proof

                  ↑ f₂ S.[ B f₂ ] B≃ p ⁻¹ c.∘ fib⇒ m₂

            {- inverse fiber map equivalence -}
            ↝⟨ c.cmp* S.⩪ (S.idn c.* , S.[ c.* ] fib≃ p ⁻¹) ⟩

                       ↑ f₂ S.[ B f₂ ] B≃ p ⁻¹
                  c.∘ (↑ f₂ (B≃ p) c.∘ fib⇒ m₁)

            {- associativity -}
            ↜⟨ c.l-cmp ⟩

                      (↑ f₂ S.[ B f₂ ] B≃ p ⁻¹ c.∘ ↑ f₂ (B≃ p))
                  c.∘  fib⇒ m₁

            {- left inverse law -}
            ↝⟨ c.cmp* S.⩪ (l-inv₁ f₂ , S.idn c.*) ⟩

                  c.idn c.∘ fib⇒ m₁

            {- left identity law -}
            ↝⟨ c.l-idn₁ ⟩

                  fib⇒ m₁

            ∎
        }

  std : Fam → Fam → S.Std
  std f₁ f₂ = record
    { obj = f₁ ⇒ f₂
    ; hom = _≃_
    ; idn = λ {m} → idn {m}
    ; cmp = λ {m₁} {m₂} {m₃} → cmp {m₁} {m₂} {m₃}
    ; inv = λ {m₁} {m₂} → inv {m₁} {m₂}
    }
    where
      open StdDef f₁ f₂

  idn : {f : Fam} → f ⇒ f
  idn {f} = record
    { B⇒    = S.M.idn
    ; fib⇒  = c.idn
    ; l-nat = λ {_} {_} {φ} → let open S.Eq c.* in
        proof

              c.idn c.∘ ↑ f φ

        {- left/right identity laws -}
        ↝⟨ S.[ c.* ] S.[ c.* ] c.l-idn₂ ⁻¹ ∘ c.l-idn₁ ⟩

              ↑ f φ c.∘ c.idn

        ∎
    }

  cmp : {f₁ f₂ f₃ : Fam} → (f₂ ⇒ f₃) P.× (f₁ ⇒ f₂) → f₁ ⇒ f₃
  cmp {f₁} {f₂} {f₃} (m₂ , m₁) = record
    { B⇒    = B⇒   m₂ S.M.∘ B⇒   m₁
    ; fib⇒  = fib⇒ m₂   c.∘ fib⇒ m₁
    ; l-nat = λ {_} {_} {φ} → let open S.Eq c.* in
        proof

              (fib⇒ m₂ c.∘ fib⇒ m₁) c.∘ ↑ f₁ φ

        {- associativity -}
        ↝⟨ c.l-cmp ⟩

              fib⇒ m₂ c.∘ (fib⇒ m₁ c.∘ ↑ f₁ φ)

        {- naturality -}
        ↝⟨ c.cmp* S.⩪ (S.idn c.* , l-nat m₁) ⟩

              fib⇒ m₂ c.∘ (↑ f₂ (B⇒ m₁ S.⩪ φ) c.∘ fib⇒ m₁)

        {- associativity -}
        ↜⟨ c.l-cmp ⟩

              (fib⇒ m₂ c.∘ ↑ f₂ (B⇒ m₁ S.⩪ φ)) c.∘ fib⇒ m₁

        {- naturality -}
        ↝⟨ c.cmp* S.⩪ (l-nat m₂ , S.idn c.*) ⟩

              (↑ f₃ (B⇒ m₂ S.⩪ (B⇒ m₁ S.⩪ φ)) c.∘ fib⇒ m₂) c.∘ fib⇒ m₁

        {- associativity -}
        ↝⟨ c.l-cmp ⟩

              ↑ f₃ (B⇒ m₂ S.M.∘ B⇒ m₁ S.⩪ φ) c.∘ fib⇒ m₂ c.∘ fib⇒ m₁

        ∎
    }

private
  module FamDef where
    obj : Set
    obj = F.Fam

    hom* : obj → obj → S.Std
    hom* = F.std

    idn* : {f : obj} → S.One S.⇒ hom* f f
    idn* {f} = record
      { o⇒ = P.M.elm (F.idn)
      ; h⇒ = P.M.elm (S.idn (F.std f f))
      }

    cmp* : {f₁ f₂ f₃ : obj} → hom* f₂ f₃ S.× hom* f₁ f₂ S.⇒ hom* f₁ f₃
    cmp* {f₁} {f₂} {f₃} = record
      { o⇒ = F.cmp
      ; h⇒ =  λ {m₁} {m₂} p → record
        { B≃   = S.[ F.B f₃ ]
                     F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p)
                   ∘ F.B≃ (P.π₁ p)
        ; fib≃ = λ {b} → let open S.Eq c.* in
            proof

                       F.↑ f₃ (S.[ F.B f₃ ]
                                F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p)
                              ∘ F.B≃ (P.π₁ p))
                  c.∘  F.fib⇒ (F.cmp m₁)

            {- calculation -}
            ↭

                      F.↑ f₃ (S.[ F.B f₃ ]
                                F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p)
                              ∘ F.B≃ (P.π₁ p))
                  c.∘ (F.fib⇒ (P.π₁ m₁) c.∘ F.fib⇒ (P.π₂ m₁))

            {- ∘ lifts to ∘ -}
            ↝⟨ c.cmp* S.⩪ (S.[ c.* ] F.l-cmp f₃ ⁻¹ , S.idn c.*) ⟩

                      (    F.↑ f₃ (F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p))
                       c.∘ F.↑ f₃ (F.B≃ (P.π₁ p)))
                  c.∘ (    F.fib⇒ (P.π₁ m₁)
                       c.∘ F.fib⇒ (P.π₂ m₁))

            {- associativity -}
            ↝⟨ S.[ c.* ] c.cmp* S.⩪ ( S.idn c.*
                                    , S.[ c.* ] c.l-cmp ⁻¹ ) ∘ c.l-cmp ⟩


                       F.↑ f₃ (F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p))
                  c.∘ (    (    F.↑ f₃ (F.B≃ (P.π₁ p))
                            c.∘ F.fib⇒ (P.π₁ m₁))
                       c.∘  F.fib⇒ (P.π₂ m₁))

            {- fiber map equivalence -}
            ↝⟨ c.cmp* S.⩪ ( S.idn c.*
                          , c.cmp* S.⩪ ( F.fib≃ (P.π₁ p)
                                         , S.idn c.*)) ⟩

                       F.↑ f₃ (F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p))
                  c.∘ (     F.fib⇒ (P.π₁ m₂)
                       c.∘  F.fib⇒ (P.π₂ m₁))

            {- associativity -}
            ↜⟨ c.l-cmp ⟩

                      (     F.↑ f₃ (F.B⇒ (P.π₁ m₂) S.⩪ F.B≃ (P.π₂ p))
                       c.∘  F.fib⇒ (P.π₁ m₂))
                  c.∘  F.fib⇒ (P.π₂ m₁)

            {- naturality -}
            ↝⟨ c.cmp* S.⩪ (S.[ c.* ] F.l-nat (P.π₁ m₂) ⁻¹ , S.idn c.*) ⟩

                      (     F.fib⇒ (P.π₁ m₂)
                       c.∘  F.↑ f₂ (F.B≃ (P.π₂ p)))
                  c.∘  F.fib⇒ (P.π₂ m₁)

            {- associativity -}
            ↝⟨ c.l-cmp ⟩


                       F.fib⇒ (P.π₁ m₂)
                  c.∘ (     F.↑ f₂ (F.B≃ (P.π₂ p))
                       c.∘  F.fib⇒ (P.π₂ m₁))

            {- fiber map equivalence -}
            ↝⟨ c.cmp* S.⩪ (S.idn c.* , F.fib≃ (P.π₂ p)) ⟩

                       F.fib⇒ (P.π₁ m₂)
                  c.∘  F.fib⇒ (P.π₂ m₂)

            {- calculation -}
            ↭

                       F.fib⇒ (F.cmp m₂)

            ∎
        }
      }

    isCat : C.IsCat obj hom* idn* cmp*
    isCat = record
      { l-idn₁ = λ {_} {f₂} {m} → record
        { B≃   = S.idn (F.B f₂)
        ; fib≃ = let open S.Eq c.* in
            proof

                      F.↑ f₂ (S.idn (F.B f₂))
                  c.∘ F.fib⇒ (cmp* S.· (idn* S.· tt , m))

            {- calculation -}
            ↭

                       F.↑ f₂ (S.idn (F.B f₂))
                  c.∘ (c.idn c.∘ F.fib⇒ m)

            {- identity lifts to identity; left identity law -}
            ↝⟨ c.cmp* S.⩪ (F.l-idn f₂ , c.l-idn₁) ⟩

                      c.idn
                  c.∘ F.fib⇒ m

            {- left identity law -}
            ↝⟨ c.l-idn₁ ⟩

                      F.fib⇒ m

            ∎
        }
      ; l-idn₂ = λ {f₁} {f₂} {m} → record
        { B≃   = S.idn (F.B f₂)
        ; fib≃ = let open S.Eq c.* in
            proof

                      F.↑ f₂ (S.idn (F.B f₂))
                  c.∘ F.fib⇒ (cmp* S.· (m , idn* S.· tt))

            {- calculation -}
            ↭

                       F.↑ f₂ (S.idn (F.B f₂))
                  c.∘ (F.fib⇒ m c.∘ c.idn)

            {- identity lifts to identity; right identity law -}
            ↝⟨ c.cmp* S.⩪ (F.l-idn f₂ , c.l-idn₂) ⟩

                      c.idn
                  c.∘ F.fib⇒ m

            {- left identity law -}
            ↝⟨ c.l-idn₁ ⟩

                      F.fib⇒ m

            ∎
        }

      ; l-cmp  = λ {f₁} {f₂} {f₃} {f₄} {m₃} {m₂} {m₁} → record
        { B≃   = S.idn (F.B f₄)
        ; fib≃ = let open S.Eq c.* in
            proof

                      F.↑ f₄ (S.idn (F.B f₄))
                  c.∘ F.fib⇒ (cmp* S.· (cmp* S.· (m₃ , m₂) , m₁))

            {- identity lifts to identity; calculation -}
            ↝⟨ c.cmp* S.⩪ (F.l-idn f₄ , S.idn c.*) ⟩

                      c.idn
                  c.∘ ((F.fib⇒ m₃ c.∘ F.fib⇒ m₂) c.∘ F.fib⇒ m₁)

            {- left identity law -}
            ↝⟨ c.l-idn₁ ⟩

                  (F.fib⇒ m₃ c.∘ F.fib⇒ m₂) c.∘ F.fib⇒ m₁

            {- associativity -}
            ↝⟨ c.l-cmp ⟩

                  F.fib⇒ m₃ c.∘ (F.fib⇒ m₂ c.∘ F.fib⇒ m₁)

            {- calculation -}
            ↭

                  F.fib⇒ (cmp* S.· (m₃ , cmp* S.· (m₂ , m₁)))

            ∎
        }
      }

FAM : C.Cat
FAM = record
  { obj   = obj
  ; hom*  = hom*
  ; idn*  = λ {f} → idn* {f}
  ; cmp*  = λ {f₁} {f₂} {f₃} → cmp* {f₁} {f₂} {f₃}
  ; isCat = isCat
  }
  where
    open FamDef
