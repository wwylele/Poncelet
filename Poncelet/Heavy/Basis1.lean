import Poncelet.Grobner

namespace Detail
open CPoly

scoped notation "x" => (X 0 : CPoly 0 9)
scoped notation "y" => (X 1 : CPoly 0 9)
scoped notation "z" => (X 2 : CPoly 0 9)
scoped notation "a" => (X 3 : CPoly 0 9)
scoped notation "b" => (X 4 : CPoly 0 9)
scoped notation "c" => (X 5 : CPoly 0 9)
scoped notation "u" => (X 6 : CPoly 0 9)
scoped notation "r" => (X 7 : CPoly 0 9)
scoped notation "k" => (X 8 : CPoly 0 9)

def basis1 : List (CPoly 0 9) := [
  x^2 - 2*x*z*u + y^2 - 2*z^2*u*r - 2*z^2*r^2 + z^2*k^2 + z^2,
  x*y*b - x*z*c - y^2*a - 2*y*z*b*u + 2*z^2*a*u*r + 2*z^2*a*r^2 - z^2*a*k^2 - z^2*a + 2*z^2*c*u,
  x*y*c^2 - x*z*b*c - y*z*a*c - 2*y*z*b^2*u + 2*z^2*a*b*u*r +
    2*z^2*a*b*r^2 - z^2*a*b*k^2 - z^2*a*b + 2*z^2*b*c*u,
  x*a + y*b - z*c,
  x*b^2 - x*c^2 - y*a*b + z*a*c,
  y^2*c^2 + 2*y*z*a*b*u - 2*y*z*b*c - 2*z^2*a*c*u + 2*z^2*b^2*u*r +
    2*z^2*b^2*r^2 - z^2*b^2*k^2 - z^2*b^2 - 2*z^2*c^2*u*r - 2*z^2*c^2*r^2
    + z^2*c^2*k^2 + 2*z^2*c^2,
  a^2 + b^2 - c^2,
  u^2 + 2*u*r + r^2 - k^2 - 1
]

end Detail

theorem forall_basis1 {K : Type*} [Field K] [CharZero K] (x y z a b c u r k : K)
    (ho : (x - u * z) ^ 2 + y ^ 2 = r ^ 2 * z ^ 2)
    (hi : a ^ 2 + b ^ 2 = c ^ 2)
    (hpq : x * a + y * b = z * c)
    (hk : k ^ 2 = (u + r) ^ 2 - 1) :
    Detail.basis1.Forall (·.eval ![x,y,z,a,b,c,u,r,k] = 0) := by
  rw [List.forall_iff_forall_mem]
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  fin_cases i
  all_goals
  · simp [Detail.basis1]
    grind
