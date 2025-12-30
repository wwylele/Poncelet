import Poncelet.Elliptic

abbrev cf : Config ℚ where
  u := 2 / 5
  r := 11 / 5
  hu := by simp
  hr := by simp
  k := 12 / 5
  k_sq := by norm_num

def right : P2 ℚ × P2 ℚ := ⟨P2.mk ![cf.u + cf.r, 0, 1] (by simp),
  P2.mk ![1, cf.k, cf.u + cf.r] (by simp)⟩

theorem right_mem_dom : right ∈ dom cf := by decide +kernel

#eval right

#eval next cf right
