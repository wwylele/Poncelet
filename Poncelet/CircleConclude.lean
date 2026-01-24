import Poncelet.Inverse
import Poncelet.Transfer

variable {K : Type*} [Field K]
variable (cf : Config K)

theorem e_f [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) (p : (elliptic cf).Point) :
    e cf (f cf p) = p := by
  rw [← (f_injective cf hk).eq_iff, f_e cf hk (mapsTo_f₀ cf hk (by simp))]

theorem leftInverse_e_f [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) :
    Function.LeftInverse (e cf) (f cf) := by
  intro p
  rw [e_f cf hk]

theorem iterate_next_eq_self_of_n_torsion [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {p : P2 K × P2 K} (hp : p ∈ dom cf) {n : ℕ}
    (hg : n • g cf = 0) :
    (next cf)^[n] p = p := by
  by_cases hdom0 : p ∈ dom₀ cf
  · rw [← f_e cf hk hdom0, ← f_add_smul_g, hg]
    simp
  · rw [mem_dom₀] at hdom0
    have : p = (P2.mk ![1, 0, 1] (by simp), P2.mk ![1, 0, 1] (by simp)) ∨
        p = (P2.mk ![-1, 0, 1] (by simp), P2.mk ![-1, 0, 1] (by simp)) := by
      simpa [hp, Classical.or_iff_not_imp_left] using hdom0
    obtain heq := (next_eq_self' cf hp).mpr this
    clear hg
    induction n with
    | zero => simp
    | succ n ih =>
      simp [heq, ih]

theorem iterate_next_eq_self_iff_of_k_ne_zero [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {p : P2 K × P2 K} (hp : p ∈ dom₀ cf) (n : ℕ) :
    (next cf)^[n] p = p ↔ n • g cf = 0 := by
  rw [← f_e cf hk hp]
  rw [← f_add_smul_g]
  rw [(f_injective cf hk).eq_iff]
  simp

theorem iterate_next_eq_self_iff_of_isAlgClosed
    [DecidableEq K] [CharZero K] [IsAlgClosed K]
    {p : P2 K × P2 K} (hp : p ∈ dom₀ cf) (n : ℕ) :
    (next cf)^[n] p = p ↔ n • g cf = 0 := by
  by_cases hk : cf.k = 0
  · obtain ⟨k', hk'sq⟩ := IsAlgClosed.exists_pow_nat_eq ((cf.u - cf.r) ^ 2 - 1) (show 0 < 2 by simp)
    let cf' : Config K := {
      u := cf.u
      r := -cf.r
      hu := cf.hu
      hr := by simpa using cf.hr
      k := k'
      k_sq := by rw [hk'sq, ← sub_eq_add_neg]
    }
    have hk' : cf'.k ≠ 0 := by
      by_contra! hk'
      rw [← sq_eq_zero_iff, cf'.k_sq] at hk'
      simp only [cf'] at hk'
      rw [← sq_eq_zero_iff, cf.k_sq] at hk
      obtain _ := cf.hu
      obtain _ := cf.hr
      grind
    rw [dom₀_eq_of_r_eq_neg cf cf' rfl rfl] at hp
    rw [next_eq_of_r_eq_neg cf cf' rfl rfl]
    rw [iterate_next_eq_self_iff_of_k_ne_zero cf' hk' hp n]
    conv_rhs =>
      rw [← (ellipticNegRAddEquiv cf cf' rfl rfl).injective.eq_iff]
    simp [g_eq_neg_of_r_eq_neg]
  · exact iterate_next_eq_self_iff_of_k_ne_zero cf hk hp n

/--
Poncelet's closure theorem, two-circle configuration:
Given a circle unit circle $D$ at $(0, 0)$ and a circle $C$ with radius $r$ at $(u, 0)$,
($u ≠ 0$, $r ≠ 0$, $u + r ≠ ±1$)
if one can draw an `n`-gon simutaneously inscribed in $C$ and circumscribed around $D$,
then one can draw another one starting from any point on $D$ as a vertex.
-/
theorem iterate_next_eq_self [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {p p' : P2 K × P2 K} (hp : p ∈ dom₀ cf) (hp' : p' ∈ dom₀ cf)
    {n : ℕ} (h : (next cf)^[n] p = p) :
    (next cf)^[n] p' = p' := by
  rw [iterate_next_eq_self_iff_of_k_ne_zero cf hk hp] at h
  rw [iterate_next_eq_self_iff_of_k_ne_zero cf hk hp']
  exact h

/--
An alternative version of `iterate_next_eq_self` that doesn't require `cf.k ≠ 0` but
requires `IsAlgClosed K`.
-/
theorem iterate_next_eq_self_of_isAlgClosed [DecidableEq K] [CharZero K] [IsAlgClosed K]
    {p p' : P2 K × P2 K} (hp : p ∈ dom₀ cf) (hp' : p' ∈ dom₀ cf)
    {n : ℕ} (h : (next cf)^[n] p = p) :
    (next cf)^[n] p' = p' := by
  rw [iterate_next_eq_self_iff_of_isAlgClosed cf hp] at h
  rw [iterate_next_eq_self_iff_of_isAlgClosed cf hp']
  exact h
