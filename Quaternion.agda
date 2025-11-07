---
--- The quaternion group
---

open import Cubical.Foundations.Prelude

-- Quaternions
data Q : Type where
  Qe Qi Qj Qk : Q
  Qe' Qi' Qj' Qk' : Q

-- Multiplication on quaternions
-- https://en.wikipedia.org/wiki/Quaternion_group
_·_ : Q → Q → Q
Qe · q = q
Qi · Qe = Qi
Qi · Qi = Qe'
Qi · Qj = Qk
Qi · Qk = Qj'
Qi · Qe' = Qi'
Qi · Qi' = Qe
Qi · Qj' = Qk'
Qi · Qk' = Qj
Qj · Qe = Qj
Qj · Qi = Qk'
Qj · Qj = Qe'
Qj · Qk = Qi
Qj · Qe' = Qj'
Qj · Qi' = Qk
Qj · Qj' = Qe
Qj · Qk' = Qi'
Qk · Qe = Qk
Qk · Qi = Qj
Qk · Qj = Qi'
Qk · Qk = Qe'
Qk · Qe' = Qk'
Qk · Qi' = Qj'
Qk · Qj' = Qi
Qk · Qk' = Qe
Qe' · Qe = Qe'
Qe' · Qi = Qi'
Qe' · Qj = Qj'
Qe' · Qk = Qk'
Qe' · Qe' = Qe
Qe' · Qi' = Qi
Qe' · Qj' = Qj
Qe' · Qk' = Qk
Qi' · Qe = Qi'
Qi' · Qi = Qe
Qi' · Qj = Qk'
Qi' · Qk = Qj
Qi' · Qe' = Qi
Qi' · Qi' = Qe'
Qi' · Qj' = Qk
Qi' · Qk' = Qj'
Qj' · Qe = Qj'
Qj' · Qi = Qk
Qj' · Qj = Qe
Qj' · Qk = Qi'
Qj' · Qe' = Qj
Qj' · Qi' = Qk'
Qj' · Qj' = Qe'
Qj' · Qk' = Qi
Qk' · Qe = Qk'
Qk' · Qi = Qj'
Qk' · Qj = Qi
Qk' · Qk = Qe
Qk' · Qe' = Qk
Qk' · Qi' = Qj
Qk' · Qj' = Qi'
Qk' · Qk' = Qe'

Q-unit-r : (x : Q) → x · Qe ≡ x
Q-unit-r Qe = refl
Q-unit-r Qi = refl
Q-unit-r Qj = refl
Q-unit-r Qk = refl
Q-unit-r Qe' = refl
Q-unit-r Qi' = refl
Q-unit-r Qj' = refl
Q-unit-r Qk' = refl

postulate
  Q-assoc : (x y z : Q) → (x · y) · z ≡ x · (y · z)

