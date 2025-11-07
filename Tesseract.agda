{-# OPTIONS --rewriting #-}

---
--- Showing that the fiber of the projection of the hypercubical manifold to the delooping of Q is a tesseract.
---

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool

open import Square
open import Quaternion

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE Q-unit-r #-}
{-# REWRITE Q-assoc #-}

-- The 0-skeleton of the hypercubical manifold
data C0 : Type where
  Ca Cb : C0

-- The 1-cells of the hypercubical manifold
data C1 : Type where
  Cx Cy Cz Cw : C1

-- Action of Q on 1-cells
ϕ1 : C1 → Q
ϕ1 Cx = Qi
ϕ1 Cy = Qj
ϕ1 Cz = Qk'
ϕ1 Cw = Qe

-- The 2-cells of the hypercubical manifold
data C2 : Type where
  Cα Cβ Cγ : C2

-- The fiber of the canonical map K → BQ encoding the action of Q on the hypercubical manifold K, as computed in the paper
data F : Type where
  F0 : C0 → Q → F
  F1 : (p : C1) (q : Q) → F0 Ca q ≡ F0 Cb (q · ϕ1 p)
  F2α : (q : Q) →
    Square
      (F1 Cy q)
      (sym (F1 Cw (q · Qi)))
      (F1 Cx q)
      (sym (F1 Cz (q · Qi)))
  F2β : (q : Q) →
    Square
      (F1 Cy q)
      (sym (F1 Cx (q · Qj)))
      (F1 Cz q)
      (sym (F1 Cw (q · Qj)))
  F2γ : (q : Q) →
    Square
      (F1 Cz q)
      (sym (F1 Cy (q · Qk')))
      (F1 Cx q)
      (sym (F1 Cw (q · Qk')))
  F3 : (q : Q) →
    Cube
      (flip (F2β q))
      (flip (rotate' (F2β (q · Qk'))))
      (F2γ q)
      (rotate' (F2γ (q · Qi)))
      (F2α q)
      (flip (rotate' (flip (F2α (q · Qj)))))

-- A hollow tesseract
data Tesseract : Type where
  T : Bool → Bool → Bool → Bool → Tesseract
  T0 : (a b c : Bool) → T false a b c ≡ T true a b c
  T1 : (a b c : Bool) → T a false b c ≡ T a true b c
  T2 : (a b c : Bool) → T a b false c ≡ T a b true c
  T3 : (a b c : Bool) → T a b c false ≡ T a b c true
  T01 : (a b : Bool) → Square (T1 false a b) (T1 true a b) (T0 false a b) (T0 true a b)
  T02 : (a b : Bool) → Square (T2 false a b) (T2 true a b) (T0 a false b) (T0 a true b)
  T03 : (a b : Bool) → Square (T3 false a b) (T3 true a b) (T0 a b false) (T0 a b true)
  T12 : (a b : Bool) → Square (T2 a false b) (T2 a true b) (T1 a false b) (T1 a true b)
  T13 : (a b : Bool) → Square (T3 a false b) (T3 a true b) (T1 a b false) (T1 a b true)
  T23 : (a b : Bool) → Square (T3 a b false) (T3 a b true) (T2 a b false) (T2 a b true)
  T012 : (a : Bool) → Cube (T12 false a) (T12 true a) (T02 false a) (T02 true a) (T01 false a) (T01 true a)
  T013 : (a : Bool) → Cube (T13 false a) (T13 true a) (T03 false a) (T03 true a) (T01 a false) (T01 a true)
  T023 : (a : Bool) → Cube (T23 false a) (T23 true a) (T03 a false) (T03 a true) (T02 a false) (T02 a true)
  T123 : (a : Bool) → Cube (T23 a false) (T23 a true) (T13 a false) (T13 a true) (T12 a false) (T12 a true)

-- Our main theorem: the fiber as computed in the paper is equivalent to the tesseract
theorem : F ≃ Tesseract
theorem = isoToEquiv (iso f g fg gf)
  where
  f : F → Tesseract
  f (F0 Ca Qe) = T false false false false
  f (F0 Cb Qe) = T false false false true
  f (F0 Ca Qi) = T true true false false
  f (F0 Cb Qi) = T true false false false
  f (F0 Ca Qj) = T false true true false
  f (F0 Cb Qj) = T false true false false
  f (F0 Ca Qk) = T false true false true
  f (F0 Cb Qk) = T true true false true
  f (F0 Ca Qe') = T true true true true
  f (F0 Cb Qe') = T true true true false
  f (F0 Ca Qi') = T false false true true
  f (F0 Cb Qi') = T false true true true
  f (F0 Ca Qj') = T true false false true
  f (F0 Cb Qj') = T true false true true
  f (F0 Ca Qk') = T true false true false
  f (F0 Cb Qk') = T false false true false
  f (F1 Cx Qe i) = T0 false false false i
  f (F1 Cy Qe i) = T1 false false false i
  f (F1 Cz Qe i) = T2 false false false i
  f (F1 Cw Qe i) = T3 false false false i
  f (F1 Cx Qi i) = T2 true true false i
  f (F1 Cy Qi i) = T3 true true false i
  f (F1 Cz Qi i) = T0 true false false (~ i)
  f (F1 Cw Qi i) = T1 true false false (~ i)
  f (F1 Cx Qj i) = T1 false true false (~ i)
  f (F1 Cy Qj i) = T0 true true false i
  f (F1 Cz Qj i) = T3 false true true i
  f (F1 Cw Qj i) = T2 false true false (~ i)
  f (F1 Cx Qk i) = T3 false true false (~ i)
  f (F1 Cy Qk i) = T2 false true true i
  f (F1 Cz Qk i) = T1 false false true (~ i)
  f (F1 Cw Qk i) = T0 true false true i
  f (F1 Cx Qe' i) = T0 true true true (~ i)
  f (F1 Cy Qe' i) = T1 true true true (~ i)
  f (F1 Cz Qe' i) = T2 true true true (~ i)
  f (F1 Cw Qe' i) = T3 true true true (~ i)
  f (F1 Cx Qi' i) = T2 false false true (~ i)
  f (F1 Cy Qi' i) = T3 false false true (~ i)
  f (F1 Cz Qi' i) = T0 false true true i
  f (F1 Cw Qi' i) = T1 false true true i
  f (F1 Cx Qj' i) = T1 true false true i
  f (F1 Cy Qj' i) = T0 false false true (~ i)
  f (F1 Cz Qj' i) = T3 true false false (~ i)
  f (F1 Cw Qj' i) = T2 true false true i
  f (F1 Cx Qk' i) = T3 true false true i
  f (F1 Cy Qk' i) = T2 true false false (~ i)
  f (F1 Cz Qk' i) = T1 true true false i
  f (F1 Cw Qk' i) = T0 false true false (~ i)
  f (F2α Qe i j) = T01 false false i j
  f (F2α Qi i j) = T23 true true i j
  f (F2α Qj i j) = T01 true false j (~ i)
  f (F2α Qk i j) = T23 false true j (~ i)
  f (F2α Qe' i j) = T01 true true (~ i) (~ j)
  f (F2α Qi' i j) = T23 false false (~ i) (~ j)
  f (F2α Qj' i j) = T01 false true (~ j) i
  f (F2α Qk' i j) = T23 true false (~ j) i
  f (F2β Qe i j) = T12 false false j i
  f (F2β Qi i j) = T03 true false (~ i) j
  f (F2β Qj i j) = T03 true true j i
  f (F2β Qk i j) = T12 false true (~ i) j
  f (F2β Qe' i j) = T12 true true (~ j) (~ i)
  f (F2β Qi' i j) = T03 false true i (~ j)
  f (F2β Qj' i j) = T03 false false (~ j) (~ i)
  f (F2β Qk' i j) = T12 true false i (~ j)
  f (F2γ Qe i j) = T02 false false i j
  f (F2γ Qi i j) = T02 true false (~ j) i
  f (F2γ Qj i j) = T13 false true (~ i) j
  f (F2γ Qk i j) = T13 false false (~ j) (~ i)
  f (F2γ Qe' i j) = T02 true true (~ i) (~ j)
  f (F2γ Qi' i j) = T02 false true j (~ i)
  f (F2γ Qj' i j) = T13 true false i (~ j)
  f (F2γ Qk' i j) = T13 true true j i
  f (F3 Qe i j k) = T012 false i j k
  f (F3 Qi i j k) = T023 true (~ k) i j
  f (F3 Qj i j k) = T013 true j (~ i) k
  f (F3 Qk i j k) = T123 false (~ k) j (~ i)
  f (F3 Qe' i j k) = T012 true (~ i) (~ j) (~ k)
  f (F3 Qi' i j k) = T023 false k (~ i) (~ j)
  f (F3 Qj' i j k) = T013 false (~ j) i (~ k)
  f (F3 Qk' i j k) = T123 true k (~ j) i

  g : Tesseract → F
  g (T false false false false) = F0 Ca Qe
  g (T false false false true) = F0 Cb Qe
  g (T false false true false) = F0 Cb Qk'
  g (T false false true true) = F0 Ca Qi'
  g (T false true false false) = F0 Cb Qj
  g (T false true false true) = F0 Ca Qk
  g (T false true true false) = F0 Ca Qj
  g (T false true true true) = F0 Cb Qi'
  g (T true false false false) = F0 Cb Qi
  g (T true false false true) = F0 Ca Qj'
  g (T true false true false) = F0 Ca Qk'
  g (T true false true true) = F0 Cb Qj'
  g (T true true false false) = F0 Ca Qi
  g (T true true false true) = F0 Cb Qk
  g (T true true true false) = F0 Cb Qe'
  g (T true true true true) = F0 Ca Qe'
  g (T0 false false false i) = F1 Cx Qe i
  g (T0 false false true i) = F1 Cy Qj' (~ i)
  g (T0 false true false i) = F1 Cw Qk' (~ i)
  g (T0 false true true i) = F1 Cz Qi' i
  g (T0 true false false i) = F1 Cz Qi (~ i)
  g (T0 true false true i) = F1 Cw Qk i
  g (T0 true true false i) = F1 Cy Qj i
  g (T0 true true true i) = F1 Cx Qe' (~ i)
  g (T1 false false false i) = F1 Cy Qe i
  g (T1 false false true i) = F1 Cz Qk (~ i)
  g (T1 false true false i) = F1 Cx Qj (~ i)
  g (T1 false true true i) = F1 Cw Qi' i
  g (T1 true false false i) = F1 Cw Qi (~ i)
  g (T1 true false true i) = F1 Cx Qj' i
  g (T1 true true false i) = F1 Cz Qk' i
  g (T1 true true true i) = F1 Cy Qe' (~ i)
  g (T2 false false false i) = F1 Cz Qe i
  g (T2 false false true i) = F1 Cx Qi' (~ i)
  g (T2 false true false i) = F1 Cw Qj (~ i)
  g (T2 false true true i) = F1 Cy Qk i
  g (T2 true false false i) = F1 Cy Qk' (~ i)
  g (T2 true false true i) = F1 Cw Qj' i
  g (T2 true true false i) = F1 Cx Qi i
  g (T2 true true true i) = F1 Cz Qe' (~ i)
  g (T3 false false false i) = F1 Cw Qe i
  g (T3 false false true i) = F1 Cy Qi' (~ i)
  g (T3 false true false i) = F1 Cx Qk (~ i)
  g (T3 false true true i) = F1 Cz Qj i
  g (T3 true false false i) = F1 Cz Qj' (~ i)
  g (T3 true false true i) = F1 Cx Qk' i
  g (T3 true true false i) = F1 Cy Qi i
  g (T3 true true true i) = F1 Cw Qe' (~ i)
  g (T01 false false i j) = F2α Qe i j
  g (T01 false true i j) = F2α Qj' j (~ i)
  g (T01 true false i j) = F2α Qj (~ j) i
  g (T01 true true i j) = F2α Qe' (~ i) (~ j)
  g (T02 false false i j) = F2γ Qe i j
  g (T02 false true i j) = F2γ Qi' (~ j) i
  g (T02 true false i j) = F2γ Qi j (~ i)
  g (T02 true true i j) = F2γ Qe' (~ i) (~ j)
  g (T03 false false i j) = F2β Qj' (~ j) (~ i)
  g (T03 false true i j) = F2β Qi' i (~ j)
  g (T03 true false i j) = F2β Qi (~ i) j
  g (T03 true true i j) = F2β Qj j i
  g (T12 false false i j) = F2β Qe j i
  g (T12 false true i j) = F2β Qk (~ i) j
  g (T12 true false i j) = F2β Qk' i (~ j)
  g (T12 true true i j) = F2β Qe' (~ j) (~ i)
  g (T13 false false i j) = F2γ Qk (~ j) (~ i)
  g (T13 false true i j) = F2γ Qj (~ i) j
  g (T13 true false i j) = F2γ Qj' i (~ j)
  g (T13 true true i j) = F2γ Qk' j i
  g (T23 false false i j) = F2α Qi' (~ i) (~ j)
  g (T23 false true i j) = F2α Qk (~ j) i
  g (T23 true false i j) = F2α Qk' j (~ i)
  g (T23 true true i j) = F2α Qi i j
  g (T012 false i j k) = F3 Qe i j k
  g (T012 true i j k) = F3 Qe' (~ i) (~ j) (~ k)
  g (T013 false i j k) = F3 Qj' j (~ i) (~ k)
  g (T013 true i j k) = F3 Qj (~ j) i k
  g (T023 false i j k) = F3 Qi' (~ j) (~ k) i
  g (T023 true i j k) = F3 Qi j k (~ i)
  g (T123 false i j k) = F3 Qk (~ k) j (~ i)
  g (T123 true i j k) = F3 Qk' k (~ j) i

  gf : (x : F) → g (f x) ≡ x
  gf (F0 Ca Qe) = refl
  gf (F0 Ca Qi) = refl
  gf (F0 Ca Qj) = refl
  gf (F0 Ca Qk) = refl
  gf (F0 Ca Qe') = refl
  gf (F0 Ca Qi') = refl
  gf (F0 Ca Qj') = refl
  gf (F0 Ca Qk') = refl
  gf (F0 Cb Qe) = refl
  gf (F0 Cb Qi) = refl
  gf (F0 Cb Qj) = refl
  gf (F0 Cb Qk) = refl
  gf (F0 Cb Qe') = refl
  gf (F0 Cb Qi') = refl
  gf (F0 Cb Qj') = refl
  gf (F0 Cb Qk') = refl
  gf (F1 Cx Qe i) = refl
  gf (F1 Cx Qi i) = refl
  gf (F1 Cx Qj i) = refl
  gf (F1 Cx Qk i) = refl
  gf (F1 Cx Qe' i) = refl
  gf (F1 Cx Qi' i) = refl
  gf (F1 Cx Qj' i) = refl
  gf (F1 Cx Qk' i) = refl
  gf (F1 Cy Qe i) = refl
  gf (F1 Cy Qi i) = refl
  gf (F1 Cy Qj i) = refl
  gf (F1 Cy Qk i) = refl
  gf (F1 Cy Qe' i) = refl
  gf (F1 Cy Qi' i) = refl
  gf (F1 Cy Qj' i) = refl
  gf (F1 Cy Qk' i) = refl
  gf (F1 Cz Qe i) = refl
  gf (F1 Cz Qi i) = refl
  gf (F1 Cz Qj i) = refl
  gf (F1 Cz Qk i) = refl
  gf (F1 Cz Qe' i) = refl
  gf (F1 Cz Qi' i) = refl
  gf (F1 Cz Qj' i) = refl
  gf (F1 Cz Qk' i) = refl
  gf (F1 Cw Qe i) = refl
  gf (F1 Cw Qi i) = refl
  gf (F1 Cw Qj i) = refl
  gf (F1 Cw Qk i) = refl
  gf (F1 Cw Qe' i) = refl
  gf (F1 Cw Qi' i) = refl
  gf (F1 Cw Qj' i) = refl
  gf (F1 Cw Qk' i) = refl
  gf (F2α Qe i j) = refl
  gf (F2α Qi i j) = refl
  gf (F2α Qj i j) = refl
  gf (F2α Qk i j) = refl
  gf (F2α Qe' i j) = refl
  gf (F2α Qi' i j) = refl
  gf (F2α Qj' i j) = refl
  gf (F2α Qk' i j) = refl
  gf (F2β Qe i j) = refl
  gf (F2β Qi i j) = refl
  gf (F2β Qj i j) = refl
  gf (F2β Qk i j) = refl
  gf (F2β Qe' i j) = refl
  gf (F2β Qi' i j) = refl
  gf (F2β Qj' i j) = refl
  gf (F2β Qk' i j) = refl
  gf (F2γ Qe i j) = refl
  gf (F2γ Qi i j) = refl
  gf (F2γ Qj i j) = refl
  gf (F2γ Qk i j) = refl
  gf (F2γ Qe' i j) = refl
  gf (F2γ Qi' i j) = refl
  gf (F2γ Qj' i j) = refl
  gf (F2γ Qk' i j) = refl
  gf (F3 Qe i j k) = refl
  gf (F3 Qi i j k) = refl
  gf (F3 Qj i j k) = refl
  gf (F3 Qk i j k) = refl
  gf (F3 Qe' i j k) = refl
  gf (F3 Qi' i j k) = refl
  gf (F3 Qj' i j k) = refl
  gf (F3 Qk' i j k) = refl

  fg : (x : Tesseract) → f (g x) ≡ x
  fg (T false false false false) = refl
  fg (T false false false true) = refl
  fg (T false false true false) = refl
  fg (T false false true true) = refl
  fg (T false true false false) = refl
  fg (T false true false true) = refl
  fg (T false true true false) = refl
  fg (T false true true true) = refl
  fg (T true false false false) = refl
  fg (T true false false true) = refl
  fg (T true false true false) = refl
  fg (T true false true true) = refl
  fg (T true true false false) = refl
  fg (T true true false true) = refl
  fg (T true true true false) = refl
  fg (T true true true true) = refl
  fg (T0 false false false i) = refl
  fg (T0 false false true i) = refl
  fg (T0 false true false i) = refl
  fg (T0 false true true i) = refl
  fg (T0 true false false i) = refl
  fg (T0 true false true i) = refl
  fg (T0 true true false i) = refl
  fg (T0 true true true i) = refl
  fg (T1 false false false i) = refl
  fg (T1 false false true i) = refl
  fg (T1 false true false i) = refl
  fg (T1 false true true i) = refl
  fg (T1 true false false i) = refl
  fg (T1 true false true i) = refl
  fg (T1 true true false i) = refl
  fg (T1 true true true i) = refl
  fg (T2 false false false i) = refl
  fg (T2 false false true i) = refl
  fg (T2 false true false i) = refl
  fg (T2 false true true i) = refl
  fg (T2 true false false i) = refl
  fg (T2 true false true i) = refl
  fg (T2 true true false i) = refl
  fg (T2 true true true i) = refl
  fg (T3 false false false i) = refl
  fg (T3 false false true i) = refl
  fg (T3 false true false i) = refl
  fg (T3 false true true i) = refl
  fg (T3 true false false i) = refl
  fg (T3 true false true i) = refl
  fg (T3 true true false i) = refl
  fg (T3 true true true i) = refl
  fg (T01 false false i j) = refl
  fg (T01 false true i j) = refl
  fg (T01 true false i j) = refl
  fg (T01 true true i j) = refl
  fg (T02 false false i j) = refl
  fg (T02 false true i j) = refl
  fg (T02 true false i j) = refl
  fg (T02 true true i j) = refl
  fg (T03 false false i j) = refl
  fg (T03 false true i j) = refl
  fg (T03 true false i j) = refl
  fg (T03 true true i j) = refl
  fg (T12 false false i j) = refl
  fg (T12 false true i j) = refl
  fg (T12 true false i j) = refl
  fg (T12 true true i j) = refl
  fg (T13 false false i j) = refl
  fg (T13 false true i j) = refl
  fg (T13 true false i j) = refl
  fg (T13 true true i j) = refl
  fg (T23 false false i j) = refl
  fg (T23 false true i j) = refl
  fg (T23 true false i j) = refl
  fg (T23 true true i j) = refl
  fg (T012 false i j k) = refl
  fg (T012 true i j k) = refl
  fg (T013 false i j k) = refl
  fg (T013 true i j k) = refl
  fg (T023 false i j k) = refl
  fg (T023 true i j k) = refl
  fg (T123 false i j k) = refl
  fg (T123 true i j k) = refl
