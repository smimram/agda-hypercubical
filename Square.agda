---
--- Additional operations on squares
---

open import Cubical.Foundations.Prelude

-- flip around diagonal
flip :
  {ℓ : Level} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} →
  Square a₀₋ a₁₋ a₋₀ a₋₁ → Square a₋₀ a₋₁ a₀₋ a₁₋
flip α i j = α j i

-- clockwise rotation
rotate :
  {ℓ : Level} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} →
  Square a₀₋ a₁₋ a₋₀ a₋₁ → Square (sym a₋₀) (sym a₋₁) a₁₋ a₀₋
rotate α i j = α (~ j) i

-- anticlockwise rotation
rotate' :
  {ℓ : Level} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} →
  Square a₀₋ a₁₋ a₋₀ a₋₁ → Square a₋₁ a₋₀ (sym a₀₋) (sym a₁₋)
rotate' α i j = α j (~ i)

--- A dependent cube
Hypercube :
  {ℓ : Level} {A : Type ℓ}
  {a₀₀₀₀ a₀₀₀₁ a₀₀₁₀ a₀₀₁₁ a₀₁₀₀ a₀₁₀₁ a₀₁₁₀ a₀₁₁₁ a₁₀₀₀ a₁₀₀₁ a₁₀₁₀ a₁₀₁₁ a₁₁₀₀ a₁₁₀₁ a₁₁₁₀ a₁₁₁₁ : A}
  {a₀₀₀₋ : a₀₀₀₀ ≡ a₀₀₀₁}           
  {a₀₀₋₀ : a₀₀₀₀ ≡ a₀₀₁₀}
  {a₀₋₀₀ : a₀₀₀₀ ≡ a₀₁₀₀}
  {a₋₀₀₀ : a₀₀₀₀ ≡ a₁₀₀₀}
  {a₀₀₁₋ : a₀₀₁₀ ≡ a₀₀₁₁}
  {a₀₀₋₁ : a₀₀₀₁ ≡ a₀₀₁₁}
  {a₀₋₀₁ : a₀₀₀₁ ≡ a₀₁₀₁}
  {a₋₀₀₁ : a₀₀₀₁ ≡ a₁₀₀₁}
  {a₀₁₀₋ : a₀₁₀₀ ≡ a₀₁₀₁}
  {a₀₁₋₀ : a₀₁₀₀ ≡ a₀₁₁₀}
  {a₀₋₁₀ : a₀₀₁₀ ≡ a₀₁₁₀}
  {a₋₀₁₀ : a₀₀₁₀ ≡ a₁₀₁₀}
  {a₀₁₁₋ : a₀₁₁₀ ≡ a₀₁₁₁}
  {a₀₁₋₁ : a₀₁₀₁ ≡ a₀₁₁₁}
  {a₀₋₁₁ : a₀₀₁₁ ≡ a₀₁₁₁}
  {a₋₀₁₁ : a₀₀₁₁ ≡ a₁₀₁₁}
  {a₁₀₀₋ : a₁₀₀₀ ≡ a₁₀₀₁}
  {a₁₀₋₀ : a₁₀₀₀ ≡ a₁₀₁₀}
  {a₁₋₀₀ : a₁₀₀₀ ≡ a₁₁₀₀}
  {a₋₁₀₀ : a₀₁₀₀ ≡ a₁₁₀₀}
  {a₁₀₁₋ : a₁₀₁₀ ≡ a₁₀₁₁}
  {a₁₀₋₁ : a₁₀₀₁ ≡ a₁₀₁₁}
  {a₁₋₀₁ : a₁₀₀₁ ≡ a₁₁₀₁}
  {a₋₁₀₁ : a₀₁₀₁ ≡ a₁₁₀₁}
  {a₁₁₀₋ : a₁₁₀₀ ≡ a₁₁₀₁}
  {a₁₁₋₀ : a₁₁₀₀ ≡ a₁₁₁₀}
  {a₁₋₁₀ : a₁₀₁₀ ≡ a₁₁₁₀}
  {a₋₁₁₀ : a₀₁₁₀ ≡ a₁₁₁₀}
  {a₁₁₁₋ : a₁₁₁₀ ≡ a₁₁₁₁}
  {a₁₁₋₁ : a₁₁₀₁ ≡ a₁₁₁₁}
  {a₁₋₁₁ : a₁₀₁₁ ≡ a₁₁₁₁}
  {a₋₁₁₁ : a₀₁₁₁ ≡ a₁₁₁₁}
  {a₀₀₋₋ : Square a₀₀₀₋ a₀₀₁₋ a₀₀₋₀ a₀₀₋₁}
  {a₀₋₀₋ : Square a₀₀₀₋ a₀₁₀₋ a₀₋₀₀ a₀₋₀₁}
  {a₋₀₀₋ : Square a₀₀₀₋ a₁₀₀₋ a₋₀₀₀ a₋₀₀₁}
  {a₀₋₋₀ : Square a₀₀₋₀ a₀₁₋₀ a₀₋₀₀ a₀₋₁₀}
  {a₋₀₋₀ : Square a₀₀₋₀ a₁₀₋₀ a₋₀₀₀ a₋₀₁₀}
  {a₋₋₀₀ : Square a₀₋₀₀ a₁₋₀₀ a₋₀₀₀ a₋₁₀₀}
  {a₀₁₋₋ : Square a₀₁₀₋ a₀₁₁₋ a₀₁₋₀ a₀₁₋₁}
  {a₀₋₁₋ : Square a₀₀₁₋ a₀₁₁₋ a₀₋₁₀ a₀₋₁₁}
  {a₋₀₁₋ : Square a₀₀₁₋ a₁₀₁₋ a₋₀₁₀ a₋₀₁₁}
  {a₀₋₋₁ : Square a₀₀₋₁ a₀₁₋₁ a₀₋₀₁ a₀₋₁₁}
  {a₋₀₋₁ : Square a₀₀₋₁ a₁₀₋₁ a₋₀₀₁ a₋₀₁₁}
  {a₋₋₀₁ : Square a₀₋₀₁ a₁₋₀₁ a₋₀₀₁ a₋₁₀₁}
  {a₁₀₋₋ : Square a₁₀₀₋ a₁₀₁₋ a₁₀₋₀ a₁₀₋₁}
  {a₁₋₀₋ : Square a₁₀₀₋ a₁₁₀₋ a₁₋₀₀ a₁₋₀₁}
  {a₋₁₀₋ : Square a₀₁₀₋ a₁₁₀₋ a₋₁₀₀ a₋₁₀₁}
  {a₁₋₋₀ : Square a₁₀₋₀ a₁₁₋₀ a₁₋₀₀ a₁₋₁₀}
  {a₋₁₋₀ : Square a₀₁₋₀ a₁₁₋₀ a₋₁₀₀ a₋₁₁₀}
  {a₋₋₁₀ : Square a₀₋₁₀ a₁₋₁₀ a₋₀₁₀ a₋₁₁₀}
  {a₁₁₋₋ : Square a₁₁₀₋ a₁₁₁₋ a₁₁₋₀ a₁₁₋₁}
  {a₁₋₁₋ : Square a₁₀₁₋ a₁₁₁₋ a₁₋₁₀ a₁₋₁₁}
  {a₋₁₁₋ : Square a₀₁₁₋ a₁₁₁₋ a₋₁₁₀ a₋₁₁₁}
  {a₁₋₋₁ : Square a₁₀₋₁ a₁₁₋₁ a₁₋₀₁ a₁₋₁₁}
  {a₋₁₋₁ : Square a₀₁₋₁ a₁₁₋₁ a₋₁₀₁ a₋₁₁₁}
  {a₋₋₁₁ : Square a₀₋₁₁ a₁₋₁₁ a₋₀₁₁ a₋₁₁₁}
  (a₀₋₋₋ : Cube a₀₀₋₋ a₀₁₋₋ a₀₋₀₋ a₀₋₁₋ a₀₋₋₀ a₀₋₋₁)
  (a₁₋₋₋ : Cube a₁₀₋₋ a₁₁₋₋ a₁₋₀₋ a₁₋₁₋ a₁₋₋₀ a₁₋₋₁)
  (a₋₀₋₋ : Cube a₀₀₋₋ a₁₀₋₋ a₋₀₀₋ a₋₀₁₋ a₋₀₋₀ a₋₀₋₁)
  (a₋₁₋₋ : Cube a₀₁₋₋ a₁₁₋₋ a₋₁₀₋ a₋₁₁₋ a₋₁₋₀ a₋₁₋₁)
  (a₋₋₀₋ : Cube a₀₋₀₋ a₁₋₀₋ a₋₀₀₋ a₋₁₀₋ a₋₋₀₀ a₋₋₀₁)
  (a₋₋₁₋ : Cube a₀₋₁₋ a₁₋₁₋ a₋₀₁₋ a₋₁₁₋ a₋₋₁₀ a₋₋₁₁)
  (a₋₋₋₀ : Cube a₀₋₋₀ a₁₋₋₀ a₋₀₋₀ a₋₁₋₀ a₋₋₀₀ a₋₋₁₀)
  (a₋₋₋₁ : Cube a₀₋₋₁ a₁₋₋₁ a₋₀₋₁ a₋₁₋₁ a₋₋₀₁ a₋₋₁₁)
  → Type _
Hypercube a₀₋₋₋ a₁₋₋₋ a₋₀₋₋ a₋₁₋₋ a₋₋₀₋ a₋₋₁₋ a₋₋₋₀ a₋₋₋₁ =
  PathP (λ i → Cube (a₋₀₋₋ i) (a₋₁₋₋ i) (a₋₋₀₋ i) (a₋₋₁₋ i) (a₋₋₋₀ i) (a₋₋₋₁ i)) a₀₋₋₋ a₁₋₋₋
