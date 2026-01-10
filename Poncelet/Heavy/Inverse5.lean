import Poncelet.Grobner

namespace Detail5
open CPoly

scoped notation "x" => (X 0 : CPoly 0 8)
scoped notation "y" => (X 1 : CPoly 0 8)
scoped notation "z" => (X 2 : CPoly 0 8)
scoped notation "a" => (X 3 : CPoly 0 8)
scoped notation "b" => (X 4 : CPoly 0 8)
scoped notation "u" => (X 5 : CPoly 0 8)
scoped notation "r" => (X 6 : CPoly 0 8)
scoped notation "k" => (X 7 : CPoly 0 8)

def basis5 : List (CPoly 0 8) := [
  x^2 - 2*x*z*u + y^2 - 2*z^2*u*r - 2*z^2*r^2 + z^2*k^2 + z^2,
 x*y*b - y^2*a - 2*y*z*b*u + 2*z^2*a*u*r + 2*z^2*a*r^2 - z^2*a*k^2 - z^2*a,
 x*a + y*b,
 x*b^2 - y*a*b,
 2*y*z*a*b*u + 2*z^2*b^2*u*r + 2*z^2*b^2*r^2 - z^2*b^2*k^2 - z^2*b^2,
 2*y*z*a*b*r^2 - 2*y*z*a*b*k^2 - 2*y*z*a*b - 2*z^2*b^2*u*r^2 + z^2*b^2*u*k^2
  + z^2*b^2*u - 2*z^2*b^2*r^3,
 2*y*z*b^2*u - 2*z^2*a*b*u*r - 2*z^2*a*b*r^2 + z^2*a*b*k^2 + z^2*a*b,
 2*y*z*b^2*r^2 - 2*y*z*b^2*k^2 - 2*y*z*b^2 + 2*z^2*a*b*u*r^2 - z^2*a*b*u*k^2
  - z^2*a*b*u + 2*z^2*a*b*r^3,
 a^2 + b^2,
 u^2 + 2*u*r + r^2 - k^2 - 1
]

def target5 : CPoly 0 8 := (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
        u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
      (((u + r) ^ 2 - 1) *
              (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) -
                u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
            (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
              u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
          y +
        k * z *
          (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) *
              (r * (u + r) * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
                2 * (r * ((u + r) * a) * ((u + r) * b) * z) * (1 - r * (u + r))) +
            u ^ 2 * (u + r) * (r * ((u + r) * a) * ((u + r) * b) * z) ^ 2)) *
    b -(
  -(k *
        (-((r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
                  u * (r * ((u + r) * a) * ((u + r) * b) * z)) ^
                3 *
              y) +
          (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) -
                  u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
                k *
              z *
            (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) *
                (r * (u + r) *
                    ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
                  2 * (r * ((u + r) * a) * ((u + r) * b) * z) * (1 - r * (u + r))) +
              u ^ 2 * (u + r) * (r * ((u + r) * a) * ((u + r) * b) * z) ^ 2)) *
      a))

end Detail5

theorem forall_basis5 {K : Type*} [Field K] [CharZero K] (x y z a b u r k : K)
    (ho : (x - u * z) ^ 2 + y ^ 2 = r ^ 2 * z ^ 2)
    (hi : a ^ 2 + b ^ 2 = 0)
    (hpq : x * a + y * b = 0)
    (hk : k ^ 2 = (u + r) ^ 2 - 1) :
    Detail5.basis5.Forall (·.eval ![x,y,z,a,b,u,r,k] = 0) := by
  rw [List.forall_iff_forall_mem]
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  fin_cases i
  all_goals
  · simp [Detail5.basis5]
    grind

theorem inverse5 {K : Type*} [Field K] [CharZero K] (x y z a b u r k : K)
    (ho : (x - u * z) ^ 2 + y ^ 2 = r ^ 2 * z ^ 2)
    (hi : a ^ 2 + b ^ 2 = 0)
    (hpq : x * a + y * b = 0)
    (hk : k ^ 2 = (u + r) ^ 2 - 1) :
    (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
        u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
      (((u + r) ^ 2 - 1) *
              (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) -
                u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
            (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
              u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
          y +
        k * z *
          (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) *
              (r * (u + r) * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
                2 * (r * ((u + r) * a) * ((u + r) * b) * z) * (1 - r * (u + r))) +
            u ^ 2 * (u + r) * (r * ((u + r) * a) * ((u + r) * b) * z) ^ 2)) *
    b =
  -(k *
        (-((r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
                  u * (r * ((u + r) * a) * ((u + r) * b) * z)) ^
                3 *
              y) +
          (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) -
                  u * (r * ((u + r) * a) * ((u + r) * b) * z)) *
                k *
              z *
            (r * ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) *
                (r * (u + r) *
                    ((2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b) * z) +
                  2 * (r * ((u + r) * a) * ((u + r) * b) * z) * (1 - r * (u + r))) +
              u ^ 2 * (u + r) * (r * ((u + r) * a) * ((u + r) * b) * z) ^ 2)) *
      a) := by
  rw [← sub_eq_zero]
  suffices Detail5.target5.eval ![x,y,z,a,b,u,r,k] = 0 by
    simpa [Detail5.target5]
  apply CPoly.eq_zero_of_reduceRepeat_eq_zero
    (forall_basis5 x y z a b u r k ho hi hpq hk) 1000
  suffices CPoly.reduceRepeat Detail5.target5 Detail5.basis5 1000 = 0 by simp [this]
  native_decide
