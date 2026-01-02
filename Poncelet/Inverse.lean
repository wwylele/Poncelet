import Poncelet.Elliptic

open WeierstrassCurve.Affine

variable {K : Type*} [Field K]
variable (cf : Config K)

def eDeno (p q : Fin 3 → K) :=
  (cf.r * ((cf.u + cf.r) * q 0 - q 2) * ((cf.u + cf.r) * q 1 + cf.k * q 2)) * p 2

def eNume (p q : Fin 3 → K) :=
  (cf.k * p 0 + ((cf.u + cf.r) ^ 2 - 1) * p 1) * q 2 ^ 2
  + (2 * cf.u * cf.k * q 0 ^ 2 + cf.u *((cf.u + cf.r) ^ 2 - 2) * q 0 * q 1
  + (cf.r * (cf.u + cf.r) - 2) * cf.k * q 0 * q 2 +
  (2 - (cf.u + cf.r) * (cf.u + 2 * cf.r)) *  q 1 * q 2 - cf.u * cf.k * q 2 ^ 2) * p 2

def eSingular (pq : P2 K × P2 K) : Prop := P2.lift₂ (fun p q hp hq ↦
  eDeno cf p q = 0)
  (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp_rw [eDeno, hl, hm]
    simp only [Pi.smul_apply, smul_eq_mul]
    grind
  ) pq.1 pq.2

def exNormal (pq : P2 K × P2 K) : K := P2.lift₂ (fun p q hp hq ↦ eNume cf p q / eDeno cf p q) (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp only
    have heq :
      cf.r * ((cf.u + cf.r) * q 0 - q 2) * ((cf.u + cf.r) * q 1 + cf.k * q 2) * p 2 = 0 ↔
      cf.r * ((cf.u + cf.r) * q' 0 - q' 2) * ((cf.u + cf.r) * q' 1 + cf.k * q' 2) * p' 2 = 0 := by
      simp_rw [hl, hm, Pi.smul_apply, smul_eq_mul]
      conv_rhs =>
        rw [← mul_left_inj' (show m ^ 2 * l ≠ 0 by simp [hl0, hm0])]
      constructor <;> intro h <;> linear_combination h
    by_cases hdeno :
      cf.r * ((cf.u + cf.r) * q 0 - q 2) * ((cf.u + cf.r) * q 1 + cf.k * q 2) * p 2 = 0
    · simp [eDeno, hdeno, heq.mp hdeno]
    have hdeno' := heq.ne.mp hdeno
    rw [eNume, eNume, eDeno, eDeno, div_eq_div_iff hdeno hdeno']
    simp_rw [hl, hm, Pi.smul_apply, smul_eq_mul]
    ring
  ) pq.1 pq.2

@[simp]
theorem exNormal_mk {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0) :
    exNormal cf ⟨(P2.mk p hp), (P2.mk q hq)⟩ =
    eNume cf p q / eDeno cf p q := rfl

def eyNormal (pq : P2 K × P2 K) : K :=
  (cf.r * exNormal cf pq + cf.u) ^ 2 / (-2 * cf.r ^ 2 * cf.k) *
  P2.lift₂ (fun p q hp hq ↦ p 1 / p 2) (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp_rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    grind
  ) pq.1 pq.2

theorem equation_exNormal_eyNormal [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hes : ¬eSingular cf pq) :
    (elliptic cf).Equation (exNormal cf pq) (eyNormal cf pq) := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  simp only [eSingular, P2.lift₂_mk] at hes
  have hp2 : p 2 ≠ 0 := by
    contrapose! hes with hp2
    simp [eDeno, hp2]
  obtain _ := cf.hr
  obtain _ := cf.hu
  rw [equation_elliptic]
  simp only [eyNormal, exNormal_mk, P2.lift₂_mk]
  field_simp
  suffices (cf.r * eNume cf p q + eDeno cf p q * cf.u) ^ 4 * p 1 ^ 2 =
    cf.r ^ 2 * 2 ^ 2 * cf.k ^ 2 * p 2 ^ 2 *
    (cf.r ^ 2 * (eNume cf p q ^ 3 * eDeno cf p q)
    + (1 - cf.u ^ 2 - cf.r ^ 2) * (eNume cf p q ^ 2 * eDeno cf p q ^ 2)
    + cf.u ^ 2 * eNume cf p q * eDeno cf p q ^ 3)   by
    linear_combination this
  unfold eNume eDeno
  obtain hk := cf.k_sq
  -- grobner?
  sorry

theorem nonsingular_exNormal_eyNormal [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬eSingular cf pq) :
    (elliptic cf).Nonsingular (exNormal cf pq) (eyNormal cf pq) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  by_contra! hs
  obtain hequation := equation_exNormal_eyNormal cf hk hpq hes
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  obtain ⟨hux, hy⟩ := (singular_elliptic cf _ _).mp ⟨hequation, hs⟩
  obtain heq := (equation_elliptic cf _ _).mp hequation
  simp only [eSingular, P2.lift₂_mk] at hes
  have hp2 : p 2 ≠ 0 := by
    contrapose! hes with hp2
    simp [eDeno, hp2]
  obtain hx2 | hy : cf.r * (eNume cf p q / eDeno cf p q) + cf.u = 0 ∨ p 1 = 0 := by
    simpa [eyNormal, cf.hr, hk, hp2] using hy
  · have hx2 : eNume cf p q / eDeno cf p q = - cf.u / cf.r := by
      grind
    rw [nonsingular_elliptic] at hs
    simp only [heq, true_and, not_or, not_not] at hs
    obtain ⟨hx, _⟩ := hs
    simp only [exNormal_mk, hx2] at hx
    field_simp at hx
    have : 2 * cf.u * ((cf.u + cf.r) ^ 2 - 1) = 0 := by
      linear_combination hx
    have : (cf.u + cf.r) ^ 2 - 1 = 0 := by simpa [cf.hu] using this
    contrapose! hk
    rw [← sq_eq_zero_iff, cf.k_sq, this]
  obtain ⟨hu, hx⟩ | ⟨hu, hx⟩ := hux
  · obtain hu | hu := hu
    · rw [hy, hu] at ho
      have hxz : (p 0 + p 2) * (p 0 + (1 - 2 * cf.r) * p 2) = 0 := by
        linear_combination ho
      obtain hxz | hxz : p 0 + p 2 = 0 ∨ p 0 + (1 - 2 * cf.r) * p 2 = 0 := by simpa using hxz
      · contrapose! hleft
        rw [P2.mk_eq_mk']
        use -p 0
        suffices p = ![p 0, 0, -p 0] by simpa
        ext i
        fin_cases i
        · rfl
        · exact hy
        · simp [eq_neg_iff_add_eq_zero.mpr hxz]
      have hp0 : p 0 = (2 * cf.r - 1) * p 2 := by linear_combination hxz
      rw [hp0, hy] at hpq
      have hq2 : q 2 = (2 * cf.r - 1) * q 0 := by
        rw [← mul_left_inj' hp2]
        linear_combination -hpq
      suffices eNume cf p q = 0 by
        symm at hx
        simp [this, cf.hr, ← hu, cf.hu] at hx
      rw [eNume, hp0, hq2, hu, hy]
      suffices cf.k * q 0 - q 1 = 0 by
        linear_combination 8 * (cf.r - 1) * q 0 * p 2 * cf.r ^ 2 * this
      rw [hq2] at hi
      have : q 1 ^ 2 = (cf.k * q 0) ^ 2 := by
        rw [mul_pow, cf.k_sq, hu]
        linear_combination hi
      obtain hi | hi := eq_or_eq_neg_of_sq_eq_sq _ _ this
      · simp [hi]
      absurd hes
      rw [eDeno, hi, hq2, hu]
      ring
    · contrapose! hk
      rw [← sq_eq_zero_iff, cf.k_sq, hu]
      ring
  · obtain hu | hu := hu
    · rw [hy, hu] at ho
      have hxz : (p 0 - p 2) * (p 0 - (1 + 2 * cf.r) * p 2) = 0 := by
        linear_combination ho
      obtain hxz | hxz : p 0 - p 2 = 0 ∨ p 0 - (1 + 2 * cf.r) * p 2 = 0 := by simpa using hxz
      · contrapose! hright
        simp only
        rw [P2.mk_eq_mk']
        use p 0
        suffices p = ![p 0, 0, p 0] by simpa
        ext i
        fin_cases i
        · rfl
        · exact hy
        · simp [sub_eq_zero.mp hxz]
      have hp0 : p 0 = (2 * cf.r + 1) * p 2 := by linear_combination hxz
      rw [hp0, hy] at hpq
      have hq2 : q 2 = (2 * cf.r + 1) * q 0 := by
        rw [← mul_left_inj' hp2]
        linear_combination -hpq
      suffices eNume cf p q = 0 by
        symm at hx
        simp [this, cf.hr, ← hu, cf.hu] at hx
      rw [eNume, hp0, hq2, hu, hy]
      suffices cf.k * q 0 - q 1 = 0 by
        linear_combination 8 * (cf.r + 1) * q 0 * p 2 * cf.r ^ 2 * this
      rw [hq2] at hi
      have : q 1 ^ 2 = (cf.k * q 0) ^ 2 := by
        rw [mul_pow, cf.k_sq, hu]
        linear_combination hi
      obtain hi | hi := eq_or_eq_neg_of_sq_eq_sq _ _ this
      · simp [hi]
      absurd hes
      rw [eDeno, hi, hq2, hu]
      ring
    · contrapose! hk
      rw [← sq_eq_zero_iff, cf.k_sq, hu]
      ring

def eNormal [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬eSingular cf pq) :=
  Point.some (nonsingular_exNormal_eyNormal cf hk hpq hleft hright hes)

theorem fPoint_eNormal [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬eSingular cf pq) :
    fPoint cf (eNormal cf hk hpq hleft hright hes) = pq.1 := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  have hes : eDeno cf p q ≠ 0 := by simpa [eSingular] using hes
  have hp2 : p 2 ≠ 0 := by
    contrapose! hes
    simp [eDeno, hes]
  suffices P2.mk
    ![cf.r ^ 2 * (cf.u + cf.r) * (eNume cf p q / eDeno cf p q) ^ 2 +
        2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * (eNume cf p q / eDeno cf p q) +
        cf.u ^ 2 * (cf.u + cf.r),
      -(2 * cf.r ^ 2 * cf.k *
        ((cf.r * (eNume cf p q / eDeno cf p q) + cf.u) ^ 2 /
        -(2 * cf.r ^ 2 * cf.k) * (p 1 / p 2))),
      (cf.r * (eNume cf p q / eDeno cf p q) + cf.u) ^ 2]
    _ =
    P2.mk p hp by
    simpa [fPoint, fPointRaw, eNormal, eyNormal]

  simp_rw [← P2.mk'_eq hp]
  apply P2.mk'_eq_mk'_of_third _ hp2
  · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    unfold eNume eDeno
    --grobner
    sorry
  · simp only [Fin.isValue, Matrix.cons_val]
    field_simp
