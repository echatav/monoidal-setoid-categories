{-# OPTIONS --type-in-type #-}
module PreThy.Prd where

import PreThy.Boot.Map as P

infixr 1 _×_
infixr 0 _,_

record _×_ (A₁ A₂ : Set) : Set where
  constructor _,_
  field
    π₁ : A₁
    π₂ : A₂
open _×_ public

⟨_,_⟩ : {A₁ A₂ A₃ : Set} → A₃ P.⇒ A₁ → A₃ P.⇒ A₂ → A₃ P.⇒ A₁ × A₂
⟨ m₁ , m₂ ⟩ = λ x → m₁ x , m₂ x

⟨_×_⟩ : {A₁ A₂ A₃ A₄ : Set} → A₁ P.⇒ A₃ → A₂ P.⇒ A₄ → A₁ × A₂ P.⇒ A₃ × A₄
⟨ m₁ × m₂ ⟩ = ⟨ (λ x → m₁ (π₁ x)) , (λ x → m₂ (π₂ x)) ⟩
