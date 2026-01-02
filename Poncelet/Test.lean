import Poncelet.Inverse



variable {K : Type*} [Field K]
variable (cf : Config K)



abbrev cfq : Config ℚ where
  u := 2 / 5
  r := 11 / 5
  hu := by simp
  hr := by simp
  k := 12 / 5
  k_sq := by norm_num

abbrev right : P2 ℚ × P2 ℚ := ⟨P2.mk ![cfq.u + cfq.r, 0, 1] (by simp),
  P2.mk ![1, cfq.k, cfq.u + cfq.r] (by simp)⟩

theorem right_mem_dom : right ∈ dom cfq := by decide +kernel

#eval right

def a1 := next cfq right
#eval a1

def y_sq (x : K) := x * (cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2) / cf.r ^ 2

def x1 := exNormal cfq a1
def y1 := eyNormal cfq a1

#eval x1 -- 4 / 121
#eval y1

lemma x1y1 : (elliptic cfq).Nonsingular x1 y1 := by
  rw [nonsingular_elliptic]
  decide +kernel

def p1 : (elliptic cfq).Point := .some x1y1

#eval f cfq p1
