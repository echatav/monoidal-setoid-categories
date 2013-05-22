module Bundle.PreThy where

-- preset theory
module P where
  open import PreThy.CoNat public
  open import PreThy.Id    public
  open import PreThy.Map   public
  open import PreThy.Prd   public
    hiding
      ( _,_ )
  open import PreThy.Trm   public
    hiding
      ( tt )
