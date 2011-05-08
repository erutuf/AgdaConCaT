
{-# OPTIONS --universe-polymorphism #-}

module Map where

open import Level
open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Core

-----------------------------------------------------------
-- Map

mapLaw : ∀ {c1 c2 ℓ1 ℓ2} (A : Setoid c1 ℓ1) -> (B : Setoid c2 ℓ2) -> (Setoid.Carrier A -> Setoid.Carrier B) -> Set (c1 ⊔ ℓ1 ⊔ ℓ2)
mapLaw A B f = ∀ (x y : Setoid.Carrier A) -> Setoid._≈_ A x y -> Setoid._≈_ B (f x) (f y)

record Map {c1 c2 ℓ1 ℓ2} (A : Setoid c1 ℓ1) (B : Setoid c2 ℓ2) : Set (suc (c1 ⊔ c2 ⊔ ℓ1 ⊔ ℓ2)) where
    field
      Ap    : Setoid.Carrier A -> Setoid.Carrier B
      Press : mapLaw A B Ap

ext : ∀{a1 a2 b1 b2} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> Map A B -> Map A B -> Set (a1 ⊔ b2)
ext A B F G = ∀ (x : Setoid.Carrier A) -> Setoid._≈_ B (Map.Ap F x) (Map.Ap G x) 

extIsEquivalence : ∀{a1 a2 b1 b2} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> IsEquivalence (ext A B)
extIsEquivalence A B = record
    { refl  = \x -> IsEquivalence.refl (Setoid.isEquivalence B)
    ; sym   = \f x -> IsEquivalence.sym (Setoid.isEquivalence B) (f x)
    ; trans = \x y z -> IsEquivalence.trans (Setoid.isEquivalence B) (x z) (y z)
    }

mapSetoid : ∀{a1 a2 b1 b2} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> Setoid (suc (b2 ⊔ b1 ⊔ a2 ⊔ a1)) (b2 ⊔ a1)
mapSetoid A B = record
    { Carrier       = Map A B
    ; _≈_          = ext A B
    ; isEquivalence = extIsEquivalence A B
    }

eqMap : ∀{a1 a2 b1 b2} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (F G : Map A B) -> ext A B F G -> (x : Setoid.Carrier A) -> Setoid._≈_ B (Map.Ap F x) (Map.Ap G x)
eqMap A B F G F=G x = F=G x

-- id on Setoid

idS : ∀{c ℓ}(A : Setoid c ℓ) -> Setoid.Carrier A -> Setoid.Carrier A
idS A x = x

idSMapLaw : ∀{a b}(A : Setoid a b) -> mapLaw A A (idS A)
idSMapLaw A = \ x y p -> p

idSMap : ∀{c ℓ}(A : Setoid c ℓ) -> Map A A
idSMap A = record
    { Ap    = idS A
    ; Press = idSMapLaw A
    }

-- compose on Setoid

compS : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3) -> Map A B -> Map B C -> Setoid.Carrier A -> Setoid.Carrier C
compS A B C F G x = Map.Ap G (Map.Ap F x)

compSMapLaw : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3) -> (F : Map A B) -> (G : Map B C) -> mapLaw A C (compS A B C F G)
compSMapLaw A B C F G = \ x y p -> Map.Press G (Map.Ap F x) (Map.Ap F y) (Map.Press F x y p)

compSMap : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3) -> Map A B -> Map B C -> Map A C
compSMap A B C F G = record
    { Ap    = compS A B C F G
    ; Press = compSMapLaw A B C F G
    }

-----------------------------------------------------------
-- Product of Setoids

record SetoidProd {c1 c2 ℓ1 ℓ2} (A : Setoid c1 ℓ1) (B : Setoid c2 ℓ2) : Set (suc (c1 ⊔ c2 ⊔ ℓ1 ⊔ ℓ2)) where
    field
      SProdl : Setoid.Carrier A
      SProdr : Setoid.Carrier B

eqSetoidProd : ∀ {a1 a2 b1 b2} (A : Setoid a1 b1)(B : Setoid a2 b2) -> SetoidProd A B -> SetoidProd A B -> Set (b1 ⊔ b2)
eqSetoidProd A B s1 s2 = Setoid._≈_ A (SetoidProd.SProdl s1) (SetoidProd.SProdl s2) × Setoid._≈_ B (SetoidProd.SProdr s1) (SetoidProd.SProdr s2)

eqSPIsEquiValence : ∀ {a1 a2 b1 b2} (A : Setoid a1 b1)(B : Setoid a2 b2) -> IsEquivalence (eqSetoidProd A B)
eqSPIsEquiValence A B = record
    { refl  = IsEquivalence.refl (Setoid.isEquivalence A) , IsEquivalence.refl (Setoid.isEquivalence B)
    ; sym   = \x -> IsEquivalence.sym (Setoid.isEquivalence A) (proj₁ x) , IsEquivalence.sym (Setoid.isEquivalence B) (proj₂ x)
    ; trans = \x y -> IsEquivalence.trans (Setoid.isEquivalence A) (proj₁ x) (proj₁ y) , IsEquivalence.trans (Setoid.isEquivalence B) (proj₂ x) (proj₂ y) 
    }

sprodSetoid : ∀ {a1 a2 b1 b2} (A : Setoid a1 b1) (B : Setoid a2 b2) -> Setoid (suc (a1 ⊔ a2 ⊔ b1 ⊔ b2)) (b1 ⊔ b2)
sprodSetoid A B = record
    { Carrier       = SetoidProd A B
    ; _≈_          = eqSetoidProd A B
    ; isEquivalence = eqSPIsEquiValence A B
    }

-- SProdl, SProdr are Map

SProdlMapLaw : ∀{a1 b1 a2 b2} (A : Setoid a1 b1) (B : Setoid a2 b2) -> mapLaw (sprodSetoid A B) A SetoidProd.SProdl
SProdlMapLaw A B = \x y p -> proj₁ p

SProdlMap : ∀{a1 a2 b1 b2} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> Map (sprodSetoid A B) A
SProdlMap A B = record
    { Ap    = SetoidProd.SProdl
    ; Press = SProdlMapLaw A B
    }

SProdrMapLaw : ∀{a1 b1 a2 b2} (A : Setoid a1 b1) (B : Setoid a2 b2) -> mapLaw (sprodSetoid A B) B SetoidProd.SProdr
SProdrMapLaw A B = \x y p -> proj₂ p

SProdrMap : ∀{a1 a2 b1 b2} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> Map (sprodSetoid A B) B
SProdrMap A B = record
    { Ap    = SetoidProd.SProdr
    ; Press = SProdrMapLaw A B
    }

-----------------------------------------------------------
-- Map2

Map2 : ∀{c1 c2 c3 ℓ1 ℓ2 ℓ3} ->  Setoid c1 ℓ1 -> Setoid c2 ℓ2 -> Setoid c3 ℓ3 -> Set (suc $ suc ℓ3 ⊔ suc ℓ2 ⊔ ℓ1 ⊔ suc c3 ⊔ suc c2 ⊔ c1)
Map2 A B C = Map A (mapSetoid B C)

map2MapLaw : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3) -> (F : Map2 A B C) -> (a : Setoid.Carrier A) -> mapLaw B C $ Map.Ap $  Map.Ap F a
map2MapLaw A B C F a = \x y p -> Map.Press (Map.Ap F a) x y p

Ap2 : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3) -> (F : Map2 A B C) -> Setoid.Carrier A -> Setoid.Carrier B -> Setoid.Carrier C
Ap2 A B C F a b = Map.Ap (Map.Ap F a) b

map2Congl : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3)
  -> (F : Map2 A B C) -> (a : Setoid.Carrier A) -> (b1 b2 : Setoid.Carrier B) -> Setoid._≈_ B b1 b2 -> Setoid._≈_ C (Ap2 A B C F a b1) (Ap2 A B C F a b2)
map2Congl A B C F a b1 b2 b1=b2 = Map.Press (Map.Ap F a) b1 b2 b1=b2

map2Congr : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3)
  -> (F : Map2 A B C) -> (a1 a2 : Setoid.Carrier A) -> (b : Setoid.Carrier B) -> Setoid._≈_ A a1 a2 -> Setoid._≈_ C (Ap2 A B C F a1 b) (Ap2 A B C F a2 b)
map2Congr A B C F a1 a2 b a1=a2 = (Map.Press F a1 a2 a1=a2) b

map2Cong : ∀{a1 a2 a3 b1 b2 b3} (A : Setoid a1 b1) -> (B : Setoid a2 b2) -> (C : Setoid a3 b3) -> (F : Map2 A B C)
  -> (a1 a2 : Setoid.Carrier A) -> (b1 b2 : Setoid.Carrier B) -> Setoid._≈_ A a1 a2 -> Setoid._≈_ B b1 b2 -> Setoid._≈_ C (Ap2 A B C F a1 b1) (Ap2 A B C F a2 b2)
map2Cong A B C F a1 a2 b1 b2 a1=a2 b1=b2 = IsEquivalence.trans (Setoid.isEquivalence C) (map2Congl A B C F a1 b1 b2 b1=b2) (map2Congr A B C F a1 a2 b2 a1=a2)
