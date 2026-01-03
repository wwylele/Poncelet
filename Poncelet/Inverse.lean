import Poncelet.Elliptic

open WeierstrassCurve.Affine

variable {K : Type*} [Field K]
variable (cf : Config K)

------------- p 2 = 0 --------------

def ZeroZ (pq : P2 K × P2 K) : Prop := P2.lift₂ (fun p q hp hq ↦ p 2 = 0) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp [hl, hl0]
  ) pq.1 pq.2

def eyZeroZ (pq : P2 K × P2 K) : K := P2.lift₂
  (fun p q hp hq ↦ - p 1 * cf.u * cf.k / (p 0 * cf.r ^ 2))
  (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp [hl]
    grind
  ) pq.1 pq.2

theorem nonsingular_eyZeroZ [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hz : ZeroZ pq) :
    (elliptic cf).Nonsingular (-cf.u / cf.r) (eyZeroZ cf pq) := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain _ := cf.k_sq
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hp2 : p 2 = 0 := by simpa [ZeroZ] using hz
  rw [hp2] at ho
  have hp0 : p 0 ≠ 0 := by
    by_contra! hp0
    have hp1 : p 1 = 0 := by simpa [hp0] using ho
    have : p = 0 := by
      ext i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    exact hp this
  have hp1 : p 1 ≠ 0 := by
    contrapose! hp0 with hp1
    simpa [hp1] using ho
  rw [nonsingular_elliptic]
  constructor
  · simp only [eyZeroZ, ne_eq, Fin.isValue, neg_mul, P2.lift₂_mk]
    field_simp
    grind
  · right
    simp [eyZeroZ, cf.hu, cf.hr, hk, hp0, hp1]

def eZeroZ [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (hz : ZeroZ pq) :=
  Point.some (nonsingular_eyZeroZ cf hk hpq hz)

theorem fPoint_eZeroZ [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (hz : ZeroZ pq) :
    fPoint cf (eZeroZ cf hk hpq hz) = pq.1 := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain _ := cf.k_sq
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hp2 : p 2 = 0 := by simpa [ZeroZ] using hz
  rw [hp2] at ho
  have hp0 : p 0 ≠ 0 := by
    by_contra! hp0
    have hp1 : p 1 = 0 := by simpa [hp0] using ho
    have : p = 0 := by
      ext i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    exact hp this
  have hp1 : p 1 ≠ 0 := by
    contrapose! hp0 with hp1
    simpa [hp1] using ho
  suffices P2.mk
      ![cf.r ^ 2 * (cf.u + cf.r) * (-cf.u / cf.r) ^ 2 +
        2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * (-cf.u / cf.r) +
        cf.u ^ 2 * (cf.u + cf.r),
      -(2 * cf.r ^ 2 * cf.k * (-(p 1 * cf.u * cf.k) / (p 0 * cf.r ^ 2))),
       (cf.r * (-cf.u / cf.r) + cf.u) ^ 2] _ =
      P2.mk p hp by
    simpa [eZeroZ, fPoint, fPointRaw, eyZeroZ]
  refine P2.mk_eq_mk_of_third_zero _ _ ?_ hp2 ?_
  · simp
    field
  · simp
    field_simp
    grind

theorem fChord_eZeroZ [DecidableEq K] [hchar : NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (hz : ZeroZ pq) :
    fChord cf (eZeroZ cf hk hpq hz) = pq.2 := by
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  have hk2 : (cf.u + cf.r) ^ 2 - 1 ≠ 0 := by
    contrapose! hk
    rw [← sq_eq_zero_iff, cf.k_sq, hk]
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain _ := cf.k_sq
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hp2 : p 2 = 0 := by simpa [ZeroZ] using hz
  rw [hp2] at ho hpq
  have hp0 : p 0 ≠ 0 := by
    by_contra! hp0
    have hp1 : p 1 = 0 := by simpa [hp0] using ho
    have : p = 0 := by
      ext i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    exact hp this
  have hp1 : p 1 ≠ 0 := by
    contrapose! hp0 with hp1
    simpa [hp1] using ho
  have ho : p 0 ^ 2 = - p 1 ^ 2 := by linear_combination ho
  have hpq : p 0 * q 0 = -p 1 * q 1 := by linear_combination hpq
  have hpq2 : p 0 ^ 2 * q 0 ^ 2 = p 1 ^ 2 * q 1 ^ 2 := by linear_combination congr($hpq ^ 2)
  rw [ho] at hpq2
  have hq01 : q 0 ^ 2 = - q 1 ^ 2 := by
    rw [← mul_left_inj' hp1, ← mul_left_inj' hp1]
    linear_combination -hpq2
  have hq2 : q 2 = 0 := by
    simpa [hq01] using hi.symm
  have hs : ¬SingularAbc cf (-cf.u / cf.r) (-(p 1 * cf.u * cf.k) / (p 0 * cf.r ^ 2)) := by
    by_contra! h
    obtain ha := h.a_eq_zero
    field_simp at ha
    have : -4 * cf.k * cf.u ^ 2 * p 1 * ((cf.u + cf.r) ^ 2 - 1) = 0 := by
      linear_combination ha
    simp [hp1, cf.hu, h4, hk, hk2] at this
  suffices P2.mk (fChordNormal cf (-cf.u / cf.r) (-(p 1 * cf.u * cf.k) / (p 0 * cf.r ^ 2))) _
      = P2.mk q hq by
    simpa [fChord, fChordRaw, eZeroZ, eyZeroZ, hs]
  unfold fChordNormal
  apply P2.mk_eq_mk_of_third_zero _ _ ?_ hq2 ?_
  · simp
    grind
  · simp
    field_simp
    grind

theorem f_eZeroZ [DecidableEq K] [hchar : NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (hz : ZeroZ pq) :
    f cf (eZeroZ cf hk hpq hz) = pq := by
  rw [f, fChord_eZeroZ cf hk hpq hz, fPoint_eZeroZ cf hk hpq hz]

------------- (u+r) * q 0 = q 2 --------------

/-
([u + r : 0 : 1], [1 : k : u + r]) -> o = (0, 0)

([(u - r) * (u + r) ^ 2 + 2 * r, 2 * k * r, (u + r) ^ 2],
  [1 : k : u + r]) -> w - o = -g = (1, - 1/r)

-/

def SingularA (pq : P2 K × P2 K) : Prop := P2.lift₂
  (fun p q hp hq ↦ (cf.u + cf.r) * q 0 = q 2 ∧ (cf.u + cf.r) * q 1 ≠ -cf.k * q 2) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    congrm ?_ ∧ ?_
    · simp [hm]
      grind
    · contrapose!
      simp [hm]
      grind
  ) pq.1 pq.2

theorem SingularA.u_add_r_ne_zero {pq : P2 K × P2 K} (h : SingularA cf pq) :
    cf.u + cf.r ≠ 0 := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  by_contra!
  simp [SingularA, P2.lift₂_mk, this] at h
  grind

theorem SingularA.q1_eq {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
    (h : SingularA cf ⟨P2.mk p hp, P2.mk q hq⟩) (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    (cf.u + cf.r) * q 1 = cf.k * q 2 := by
  simp only [SingularA, P2.lift₂_mk] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have : ((cf.u + cf.r) * q 1) ^ 2 = (cf.k * q 2) ^ 2 := by
    simp_rw [mul_pow, cf.k_sq]
    linear_combination (cf.u + cf.r) ^ 2 * hi - congr($h1 ^ 2)
  obtain h | h := eq_or_eq_neg_of_sq_eq_sq _ _ this
  · exact h
  · simp [h] at h2

theorem SingularA.q_eq {pq : P2 K × P2 K} (h : SingularA cf pq) (hpq : pq ∈ dom cf) :
    pq.2 = P2.mk ![1, cf.k, cf.u + cf.r] (by simp) := by
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  simp only
  conv_rhs => rw [← P2.mk'_eq _]
  apply P2.mk'_eq_mk'_of_third _ (by simpa using h.u_add_r_ne_zero) ?_
  · suffices q 1 * (cf.u + cf.r) = q 2 * cf.k by simpa
    linear_combination h.q1_eq cf hpq
  · suffices q 0 * (cf.u + cf.r) = q 2 by simpa
    simp only [SingularA, P2.lift₂_mk] at h
    linear_combination h.1

theorem SingularA.p2_ne_zero {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
    (h : SingularA cf ⟨P2.mk p hp, P2.mk q hq⟩) (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    p 2 ≠ 0 := by
  by_contra! hp2
  obtain hqeq := h.q_eq cf hpq
  simp only at hqeq
  rw [P2.mk_eq_mk] at hqeq
  obtain ⟨l, hl0, hl⟩ := hqeq
  simp_rw [Matrix.smul_vec3, smul_eq_mul] at hl
  have hq0eq : q 0 = l := by simpa using congr($hl 0)
  have hq1eq : q 1 = l * cf.k := by simpa using congr($hl 1)
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hpq : p 0 * q 0 + p 1 * q 1 = 0 := by simpa [hp2] using hpq
  have hpq' : p 0 ^ 2 * q 0 ^ 2 = p 1 ^ 2 * q 1 ^ 2 := by
    linear_combination congr($(add_eq_zero_iff_eq_neg.mp hpq) ^ 2)
  have ho : p 0 ^ 2 + p 1 ^ 2 = 0 := by simpa [hp2] using ho
  have hp1 : p 1 ≠ 0 := by
    by_contra hp1
    have hp0 : p 0 = 0 := by simpa [hp1] using ho
    have hp' : p = 0 := by
      ext i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    exact hp hp'
  have ho' : p 0 ^ 2 = - p 1 ^ 2 := by linear_combination ho
  rw [ho'] at hpq'
  have hq01 : q 0 ^ 2 = -q 1 ^ 2 := by
    rw [← mul_left_inj' hp1, ← mul_left_inj' hp1]
    linear_combination -hpq'
  rw [hq1eq, hq0eq, mul_pow, cf.k_sq] at hq01
  have : (cf.u + cf.r) ^ 2 = 0 := by
    rw [← mul_left_inj' hl0, ← mul_left_inj' hl0]
    linear_combination hq01
  simp [h.u_add_r_ne_zero] at this

theorem SingularA.p_equation {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
    (h : SingularA cf ⟨P2.mk p hp, P2.mk q hq⟩) (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    p 1 * ((cf.u + cf.r) ^ 2 * p 1 - 2 * cf.k * cf.r * p 2) = 0 := by
  obtain hqeq := h.q_eq cf hpq
  simp only at hqeq
  rw [P2.mk_eq_mk] at hqeq
  obtain ⟨l, hl0, hl⟩ := hqeq
  simp_rw [Matrix.smul_vec3, smul_eq_mul] at hl
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hq0eq : q 0 = l := by simpa using congr($hl 0)
  have hq1eq : q 1 = l * cf.k := by simpa using congr($hl 1)
  have hq2eq : q 2 = l * (cf.u + cf.r) := by simpa using congr($hl 2)
  rw [hq0eq, hq1eq, hq2eq] at hpq
  have hpeq : p 0 = (cf.u + cf.r) * p 2 - cf.k * p 1 := by
    rw [← mul_left_inj' hl0]
    linear_combination hpq
  rw [hpeq] at ho
  have hk := cf.k_sq
  grind

theorem SingularA.p01_eq {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
    (h : SingularA cf ⟨P2.mk p hp, P2.mk q hq⟩) (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    (p 0 = (cf.u + cf.r) * p 2 ∧ p 1 = 0) ∨
    (p 0 = ((cf.u - cf.r) * (cf.u + cf.r) ^ 2 + 2 * cf.r) * p 2 / (cf.u + cf.r) ^ 2 ∧
      p 1 = 2 * cf.k * cf.r * p 2 / (cf.u + cf.r) ^ 2) := by
  obtain hqeq := h.q_eq cf hpq
  simp only at hqeq
  rw [P2.mk_eq_mk] at hqeq
  obtain ⟨l, hl0, hl⟩ := hqeq
  have hq0eq : q 0 = l := by simpa using congr($hl 0)
  have hq1eq : q 1 = l * cf.k := by simpa using congr($hl 1)
  have hq2eq : q 2 = l * (cf.u + cf.r) := by simpa using congr($hl 2)
  obtain h0 := mul_eq_zero.mp <| h.p_equation cf hpq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  rw [hq0eq, hq1eq, hq2eq] at hpq
  obtain h0 | h0 := h0
  · left
    rw [h0] at hpq
    refine ⟨?_, h0⟩
    rw [← mul_left_inj' hl0]
    linear_combination hpq
  right
  obtain _ := h.u_add_r_ne_zero
  have hp1 : p 1 = 2 * cf.k * cf.r * p 2 / (cf.u + cf.r) ^ 2 := by
    field_simp
    linear_combination h0
  constructor
  · rw [hp1] at hpq
    field_simp at ⊢ hpq
    rw [cf.k_sq] at hpq
    linear_combination hpq
  · exact hp1

def exSingularA (pq : P2 K × P2 K) : K := P2.lift₂
  (fun p q hp hq ↦ (cf.u + cf.r) ^ 2 * p 1 / (2 * cf.k * cf.r * p 2))
  (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp [hl]
    grind
  ) pq.1 pq.2

def eySingularA (pq : P2 K × P2 K) : K := P2.lift₂
  (fun p q hp hq ↦ -(cf.u + cf.r) ^ 2 * p 1 / (2 * cf.k * cf.r ^ 2 * p 2))
  (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp [hl]
    grind
  ) pq.1 pq.2

theorem nonsingular_exSingularA_eySingularA [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularA cf pq) :
    (elliptic cf).Nonsingular (exSingularA cf pq) (eySingularA cf pq) := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain _ := cf.k_sq
  obtain _ := h.u_add_r_ne_zero
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hp01 := h.p01_eq cf hpq
  obtain hp2 := h.p2_ne_zero cf hpq
  obtain hpeq := h.p_equation cf hpq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  rw [nonsingular_elliptic]
  constructor
  · simp only [eySingularA, exSingularA, P2.lift₂_mk]
    obtain ⟨_, hp1⟩ | ⟨_, hp1⟩ := hp01
    · simp [hp1]
    rw [hp1]
    field
  · simp only [eySingularA, exSingularA, P2.lift₂_mk]
    obtain ⟨_, hp1⟩ | ⟨_, hp1⟩ := hp01
    · simp [hp1, cf.hu]
    right
    rw [hp1]
    field_simp
    simp [cf.hr]

def eSingularA [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularA cf pq) :=
  Point.some (nonsingular_exSingularA_eySingularA cf hk hpq h)

theorem fPoint_eSingularA [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularA cf pq) :
    fPoint cf (eSingularA cf hk hpq h) = pq.1 := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain _ := cf.k_sq
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hp01 := h.p01_eq cf hpq
  obtain hp2 := h.p2_ne_zero cf hpq
  obtain _ := h.u_add_r_ne_zero
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  suffices P2.mk
    ![cf.r ^ 2 * (cf.u + cf.r) * ((cf.u + cf.r) ^ 2 * p 1 / (2 * cf.k * cf.r * p 2)) ^ 2 +
      2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) *
      ((cf.u + cf.r) ^ 2 * p 1 / (2 * cf.k * cf.r * p 2)) + cf.u ^ 2 * (cf.u + cf.r),
    -(2 * cf.r ^ 2 * cf.k * (-((cf.u + cf.r) ^ 2 * p 1) / (2 * cf.k * cf.r ^ 2 * p 2))),
    (cf.r * ((cf.u + cf.r) ^ 2 * p 1 / (2 * cf.k * cf.r * p 2)) + cf.u) ^ 2] _ =
      P2.mk p hp by
    simpa [fPoint, fPointRaw, eSingularA, exSingularA, eySingularA]
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ hp2 ?_ ?_
  · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val]
    obtain ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩ := hp01
    · field_simp
      grind
    · rw [hp0, hp1]
      field_simp
      grind
  · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, neg_mul, Matrix.cons_val]
    obtain ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩ := hp01
    · field_simp
      grind
    · rw [hp1]
      field_simp
      grind

theorem fChord_eSingularA [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularA cf pq) :
    fChord cf (eSingularA cf hk hpq h) = pq.2 := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain _ := cf.k_sq
  obtain hur := h.u_add_r_ne_zero
  obtain hnonsingular := nonsingular_exSingularA_eySingularA cf hk hpq h
  rw [h.q_eq cf hpq]
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hp01 := h.p01_eq cf hpq
  obtain hp2 := h.p2_ne_zero cf hpq
  obtain _ := h.u_add_r_ne_zero
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  obtain ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩ := hp01
  · have hs : ¬ SingularAbc cf (exSingularA cf (P2.mk p hp, P2.mk q hq))
        (eySingularA cf (P2.mk p hp, P2.mk q hq)) := by
      by_contra! hs
      obtain hc := hs.c_factor_eq_zero cf hnonsingular
      contrapose! hc
      simp [exSingularA, hp1, cf.hu, hur]
    suffices P2.mk (fChordNormal cf (exSingularA cf (P2.mk p hp, P2.mk q hq))
        (eySingularA cf (P2.mk p hp, P2.mk q hq))) _ =
        P2.mk ![1, cf.k, cf.u + cf.r] _ by
      simpa [fChord, fChordRaw, eSingularA, hs]
    conv_rhs => rw [← P2.mk'_eq]
    refine P2.mk'_eq_mk'_of_third _ hur ?_ ?_
    · simp [fChordNormal, exSingularA, eySingularA, hp1]
      ring
    · simp [fChordNormal, exSingularA, eySingularA, hp1]
      ring
  · by_cases hs : SingularAbc cf (exSingularA cf (P2.mk p hp, P2.mk q hq))
      (eySingularA cf (P2.mk p hp, P2.mk q hq))
    · have hc := hs.a_eq_zero
      simp only [exSingularA, P2.lift₂_mk, hp1, eySingularA] at hc
      field_simp at hc
      have hur2 : (cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r = 0 := by
        linear_combination hc
      suffices P2.mk
        ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
          (cf.r * (cf.u + cf.r) ^ 2 * exSingularA cf (P2.mk p hp, P2.mk q hq)
          - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
          8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ = P2.mk ![1, cf.k, cf.u + cf.r] _ by
        simpa [fChord, fChordRaw, eSingularA, hs]
      conv_rhs => rw [← P2.mk'_eq]
      refine P2.mk'_eq_mk'_of_third _ hur ?_ ?_
      · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val, mul_one]
        linear_combination 2 * cf.k * cf.u * (cf.u + cf.r) * hur2
      · simp only [exSingularA, Fin.isValue, P2.lift₂_mk, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.cons_val]
        rw [hp1]
        field_simp
        rw [cf.k_sq]
        linear_combination (cf.u + cf.r) *
          (cf.r ^ 3 + cf.r ^ 2 * cf.u - cf.r * cf.u ^ 2 - cf.u ^ 3 - 2 * cf.u) * hur2
    · suffices P2.mk (fChordNormal cf (exSingularA cf (P2.mk p hp, P2.mk q hq))
          (eySingularA cf (P2.mk p hp, P2.mk q hq))) _ =
          P2.mk ![1, cf.k, cf.u + cf.r] _ by
        simpa [fChord, fChordRaw, eSingularA, hs]
      conv_rhs => rw [← P2.mk'_eq]
      refine P2.mk'_eq_mk'_of_third _ hur ?_ ?_
      · simp [fChordNormal, exSingularA, eySingularA, hp1]
        field
      · simp [fChordNormal, exSingularA, eySingularA, hp1]
        field

theorem f_eSingularA [DecidableEq K] [hchar : NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularA cf pq) :
    f cf (eSingularA cf hk hpq h) = pq := by
  rw [f, fChord_eSingularA cf hk hpq h, fPoint_eSingularA cf hk hpq h]

------------- (u+r) * q 0 = q 2, (u + r) * q 1 = -k * q 2 --------------

def SingularAB (pq : P2 K × P2 K) : Prop := P2.lift₂
  (fun p q hp hq ↦ (cf.u + cf.r) * q 0 = q 2 ∧ (cf.u + cf.r) * q 1 = -cf.k * q 2) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    congrm ?_ ∧ ?_
    · simp [hm]
      grind
    · contrapose!
      simp [hm]
      grind
  ) pq.1 pq.2

------------- Subcase: SingularAbc casePos --------------

theorem SingularAB.q_eq_of_casePos [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : SingularAB cf pq)
    (hur : cf.u + cf.r = 0) (hpq : pq ∈ dom cf) :
    (pq.2 = P2.mk ![1, cf.k, 0] (by simp) ∧
      (pq.1 = P2.mk ![0, 0, 1] (by simp) ∨ (pq.1 = P2.mk ![1, cf.k, 0] (by simp)))) ∨
    (pq.2 = P2.mk ![1, -cf.k, 0] (by simp) ∧
      (pq.1 = P2.mk ![0, 0, 1] (by simp) ∨ (pq.1 = P2.mk ![1, -cf.k, 0] (by simp)))) := by
  have hk : cf.k ≠ 0 := by
    rw [← sq_eq_zero_iff.ne, cf.k_sq, hur]
    simp
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  simp only [SingularAB, P2.lift₂_mk] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hq2 : q 2 = 0 := by simpa [hur] using h1.symm
  rw [hq2] at hi
  have hi' : (q 0 * cf.k) ^ 2 = q 1 ^ 2 := by
    rw [mul_pow, cf.k_sq, hur]
    linear_combination -hi
  have hq0 : q 0 ≠ 0 := by
    by_contra! hq0
    suffices q = 0 from hq this
    ext i
    fin_cases i
    · simpa using hq0
    · simpa [hq0] using hi
    · simpa using hq2
  obtain h | h := eq_or_eq_neg_of_sq_eq_sq _ _ hi'
  · left
    simp only
    constructor
    · apply P2.mk_eq_mk_of_third_zero _ _ hq2 rfl
      simpa using h
    · rw [← h, hq2] at hpq
      have hp01 : p 0 = -cf.k * p 1 := by
        rw [← mul_left_inj' hq0]
        linear_combination hpq
      have : p 1 ^ 2 = - p 0 ^ 2 := by
        obtain h := congr($hp01 ^ 2)
        rw [mul_pow, neg_sq, cf.k_sq, hur] at h
        linear_combination h
      rw [this] at ho
      have : p 0 * cf.u * p 2 * 2 = p 2 ^ 2 * (cf.u - cf.r) * (cf.u + cf.r) := by
        linear_combination -ho
      obtain h0 | h0 : p 0 = 0 ∨ p 2 = 0 := by simpa [hur, cf.hu, hchar.out] using this
      · left
        rw [P2.mk_eq_mk']
        use p 2
        ext i
        fin_cases i
        · simpa using h0
        · simpa [h0, hk] using hp01.symm
        · simp
      · right
        rw [P2.mk_eq_mk']
        use p 0
        ext i
        fin_cases i
        · simp
        · suffices p 1 = -(cf.k * p 1 * cf.k) by
            simpa [hp01]
          suffices p 1 = -(p 1 * cf.k ^ 2) by linear_combination this
          simp [cf.k_sq, hur]
        · simpa using h0
  · right
    simp only
    constructor
    · apply P2.mk_eq_mk_of_third_zero _ _ hq2 rfl
      simpa using congr(-$h)
    · have h' : q 1 = - q 0 * cf.k := by linear_combination h
      rw [h', hq2] at hpq
      have hp01 : p 0 = cf.k * p 1 := by
        rw [← mul_left_inj' hq0]
        linear_combination hpq
      have : p 1 ^ 2 = -p 0 ^ 2 := by
        obtain h := congr($hp01 ^ 2)
        rw [mul_pow, cf.k_sq, hur] at h
        linear_combination h
      rw [this] at ho
      have : p 0 * cf.u * p 2 * 2 = p 2 ^ 2 * (cf.u - cf.r) * (cf.u + cf.r) := by
        linear_combination -ho
      obtain h0 | h0 : p 0 = 0 ∨ p 2 = 0 := by simpa [hur, cf.hu, hchar.out] using this
      · left
        rw [P2.mk_eq_mk']
        use p 2
        ext i
        fin_cases i
        · simpa using h0
        · simpa [h0, hk] using hp01.symm
        · simp
      · right
        rw [P2.mk_eq_mk']
        use p 0
        ext i
        fin_cases i
        · simp
        · suffices p 1 = -(cf.k * p 1 * cf.k) by
            simpa [hp01]
          suffices p 1 = -(p 1 * cf.k ^ 2) by linear_combination this
          simp [cf.k_sq, hur]
        · simpa using h0

def eSingularABcasePos [DecidableEq K] [NeZero (2 : K)]
    (pq : P2 K × P2 K) (hur : cf.u + cf.r = 0) : (elliptic cf).Point :=
  if pq.2 = P2.mk ![1, cf.k, 0] (by simp) then
    if pq.1 = P2.mk ![0, 0, 1] (by simp) then
      .some (show (elliptic cf).Nonsingular 0 0 by
        rw [nonsingular_elliptic]
        simp [cf.hu]
      )
    else
      .some (show (elliptic cf).Nonsingular 1 (1 / cf.u) by
        rw [nonsingular_elliptic]
        have hr : cf.r = - cf.u := by linear_combination hur
        simp [cf.hu, hr]
      )
  else
    if pq.1 = P2.mk ![0, 0, 1] (by simp) then
      .zero
    else
      .some (show (elliptic cf).Nonsingular 1 (- 1 / cf.u) by
        rw [nonsingular_elliptic]
        have hr : cf.r = - cf.u := by linear_combination hur
        simp [cf.hu, hr, div_pow]
      )

theorem f_eSingularABcasePos [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : SingularAB cf pq) (hk : cf.k ≠ 0)
    (hur : cf.u + cf.r = 0) (hpq : pq ∈ dom cf) :
    f cf (eSingularABcasePos cf pq hur) = pq := by
  have hur' : cf.r + cf.u = 0 := by linear_combination hur
  have hr : cf.r = - cf.u := by linear_combination hur
  obtain hcases := SingularAB.q_eq_of_casePos cf h hur hpq
  by_cases hq : pq.2 = P2.mk ![1, cf.k, 0] (by simp)
  · obtain ⟨_, hpcases⟩ := hcases.resolve_right (by
      apply not_and_of_not_left
      rw [hq]
      contrapose! hk with h
      rw [P2.mk_eq_mk] at h
      obtain ⟨l, hl0, hl⟩ := h
      have : l = 1 := by simpa using congr($hl.symm 0)
      have : cf.k = -cf.k := by simpa [this] using congr($hl 1)
      rw [eq_neg_iff_add_eq_zero, ← two_mul] at this
      simpa [hchar.out] using this
    )
    by_cases hp : pq.1 = P2.mk ![0, 0, 1] (by simp)
    · have hs : SingularAbc cf 0 0 := by
        simp [SingularAbc, fChordNormal, hur]
      suffices (P2.mk ![0, 0, cf.u ^ 2] _,
          P2.mk ![2 * cf.u * cf.k * (4 * cf.u ^ 2), -(cf.u * 2 * (4 * cf.u ^ 2)), 0] _) = pq by
        simpa [eSingularABcasePos, hp, hq, f, fPoint, fChord, fPointRaw, fChordRaw, hs, hr]
      ext
      · simp_rw [hp]
        rw [P2.mk_eq_mk']
        use cf.u ^ 2
        simp
      · simp_rw [hq]
        apply P2.mk_eq_mk_of_third_zero _ _ rfl rfl
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
        suffices 2 * cf.u * cf.k ^ 2 * (4 * cf.u ^ 2) = -(cf.u * 2 * (4 * cf.u ^ 2)) by
          linear_combination this
        rw [cf.k_sq, hur]
        ring
    · obtain hpcase := hpcases.resolve_left hp
      have hs : ¬ SingularAbc cf 1 cf.u⁻¹ := by
        suffices -cf.u - cf.u ≠ 0 by simpa [SingularAbc, fChordNormal, hr, hk, cf.hu, hchar.out]
        rw [← neg_add', ← two_mul]
        simp [hchar.out, cf.hu]
      suffices (P2.mk ![-(2 * cf.u * (1 - cf.u ^ 2 + cf.u * cf.u)),
            -(2 * cf.u ^ 2 * cf.k * cf.u⁻¹), 0] _,
          P2.mk ![2 * cf.u ^ 2 * (-cf.u - cf.u) * cf.u⁻¹,
            cf.k * ((-cf.u - cf.u) * (2 * cf.u)), 0] _) = pq by
        simpa [eSingularABcasePos, hp, hq, f, fPoint, fChord, fPointRaw, fChordRaw, hs, hr,
          fChordNormal]
      ext
      · simp_rw [hpcase]
        apply P2.mk_eq_mk_of_third_zero _ _ rfl rfl
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field [cf.hu]
      · simp_rw [hq]
        apply P2.mk_eq_mk_of_third_zero _ _ rfl rfl
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field
  · obtain ⟨hqeq, hpcases⟩ := hcases.resolve_left (by
      apply not_and_of_not_left
      exact hq
    )
    by_cases hp : pq.1 = P2.mk ![0, 0, 1] (by simp)
    · suffices (P2.mk ![cf.u + cf.r, 0, 1] _, P2.mk ![1, -cf.k, cf.u + cf.r] _) = pq by
        simpa [eSingularABcasePos, hp, hq, f, fPoint, fChord, fPointRaw, fChordRaw]
      ext
      · simp [hp, hur]
      · simp [hqeq, hur]
    · obtain hpcases := hpcases.resolve_left hp
      have hs : ¬ SingularAbc cf 1 (-1 / cf.u) := by
        suffices -cf.u - cf.u ≠ 0 by simpa [SingularAbc, fChordNormal, hr, hk, cf.hu, hchar.out]
        rw [← neg_add', ← two_mul]
        simp [hchar.out, cf.hu]
      suffices (P2.mk ![-(2 * cf.u * (1 - cf.u ^ 2 + cf.u * cf.u)),
            -(2 * cf.u ^ 2 * cf.k * (-1 / cf.u)), 0] _,
          P2.mk ![2 * cf.u ^ 2 * (-cf.u - cf.u) * (-1 / cf.u),
            cf.k * ((-cf.u - cf.u) * (2 * cf.u)), 0] _)= pq by
        simpa [eSingularABcasePos, hp, hq, f, fPoint, fChord, fPointRaw, fChordRaw, hs, hr,
          fChordNormal]
      ext
      · simp_rw [hpcases]
        apply P2.mk_eq_mk_of_third_zero _ _ rfl rfl
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field [cf.hu]
      · simp_rw [hqeq]
        apply P2.mk_eq_mk_of_third_zero _ _ rfl rfl
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field

------------- SingularAB general --------------

theorem SingularAB.q_eq {pq : P2 K × P2 K} (h : SingularAB cf pq) (hur : cf.u + cf.r ≠ 0) :
    pq.2 = P2.mk ![1, -cf.k, cf.u + cf.r] (by simp) := by
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  simp only [SingularAB, P2.lift₂_mk] at h
  obtain ⟨h1, h2⟩ := h
  simp only
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ (by simpa using hur) ?_ ?_
  · rw [mul_comm] at h1
    simpa using h1
  · rw [mul_comm _ (q 1), mul_comm _ (q 2)] at h2
    simpa using h2

theorem SingularAB.p_eq (hk : cf.k ≠ 0) {pq : P2 K × P2 K} (h : SingularAB cf pq)
    (hpq : pq ∈ dom cf) (hur : cf.u + cf.r ≠ 0) :
    pq.1 = P2.mk ![cf.u + cf.r, 0, 1] (by simp) ∨
    pq.1 = P2.mk ![(cf.u + cf.r) ^ 2 * (cf.u - cf.r) + 2 * cf.r,
      -2 * cf.r * cf.k, (cf.u + cf.r) ^ 2] (fun h ↦ by simpa [hur] using congr($h 2)) := by
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  simp only [SingularAB, P2.lift₂_mk] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have hq2 : q 2 ≠ 0 := by
    by_contra! hq2
    suffices q = 0 from hq this
    ext i
    fin_cases i
    · simpa [hq2, hur] using h1
    · simpa [hq2, hur] using h2
    · exact hq2
  have hp01 : cf.k * p 1 = p 0 - (cf.u + cf.r) * p 2 := by
    rw [← mul_left_inj' hq2]
    linear_combination -(cf.u + cf.r) * hpq + p 0 * h1 + p 1 * h2
  have ho' : ((cf.u + cf.r) ^ 2 - 1) * (p 0 - cf.u * p 2) ^ 2 + (cf.k * p 1) ^ 2 =
      ((cf.u + cf.r) ^ 2 - 1) * cf.r ^ 2 * p 2 ^ 2 := by
    rw [← cf.k_sq]
    linear_combination cf.k ^ 2 * ho
  rw [hp01] at ho'
  have : (p 0 - (cf.u + cf.r) * p 2) *
      ((cf.u + cf.r) ^ 2 * p 0 - ((cf.u + cf.r) ^ 2 * (cf.u - cf.r) + 2 * cf.r) * p 2) = 0 := by
    linear_combination ho'
  obtain h0 | h0 := mul_eq_zero.mp this
  · rw [sub_eq_zero] at h0
    left
    conv_rhs => rw [← P2.mk'_eq]
    refine P2.mk'_eq_mk'_of_third _ (by simp) ?_ ?_
    · rw [mul_comm] at h0
      simpa using h0
    · rw [h0] at hp01
      simpa [hk] using hp01
  · right
    conv_rhs => rw [← P2.mk'_eq]
    refine P2.mk'_eq_mk'_of_third _ (by simp [hur]) ?_ ?_
    · simp only [Matrix.cons_val, Matrix.cons_val_zero]
      linear_combination h0
    · simp only [Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero]
      suffices cf.k * p 1 * (cf.u + cf.r) ^ 2 =
          ((cf.u + cf.r) ^ 2 - 1) * (-2 * cf.r) * p 2 by
        rw [← cf.k_sq] at this
        rw [← mul_left_inj' hk]
        linear_combination this
      rw [hp01]
      linear_combination h0

def eSingularAB [DecidableEq K] [NeZero (2 : K)]
    (pq : P2 K × P2 K) : (elliptic cf).Point :=
  if pq.1 = P2.mk ![cf.u + cf.r, 0, 1] (by simp) then
    .zero
  else
    .some (nonsingular_w cf)

theorem f_eSingularABcase [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : SingularAB cf pq) (hk : cf.k ≠ 0)
    (hur : cf.u + cf.r ≠ 0) (hpq : pq ∈ dom cf) :
    f cf (eSingularAB cf pq) = pq := by
  by_cases hcases : pq.1 = P2.mk ![cf.u + cf.r, 0, 1] (by simp)
  · suffices (P2.mk ![cf.u + cf.r, 0, 1] _, P2.mk ![1, -cf.k, cf.u + cf.r] _) = pq by
      simpa [eSingularAB, hcases]
    ext
    · simp [hcases]
    · simp [h.q_eq cf hur]
  · obtain hp := (h.p_eq cf hk hpq hur).resolve_left hcases
    simp only [f, fPoint, fPointRaw, eSingularAB, hcases, ↓reduceIte, fChord, fChordRaw]
    ext
    · simp_rw [hp]
      conv_rhs => rw [← P2.mk'_eq]
      refine P2.mk'_eq_mk'_of_third _ (by simpa using hur) ?_ ?_
      · simp
        field [cf.hr]
      · simp
        field [cf.hr]
    · simp_rw [h.q_eq cf hur]
      by_cases hs : SingularAbc cf (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 3)
      · obtain hc := hs.c_factor_eq_zero cf (nonsingular_w cf)
        field_simp [cf.hr] at hc
        simp only [hs, ↓reduceIte]
        conv_rhs => rw [← P2.mk'_eq]
        refine P2.mk'_eq_mk'_of_third _ (by simpa using hur) ?_ ?_
        · simp
          grind
        · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
          field_simp [cf.hr]
          rw [cf.k_sq]
          grind
      simp only [hs, ↓reduceIte, fChordNormal]
      conv_rhs => rw [← P2.mk'_eq]
      refine P2.mk'_eq_mk'_of_third _ (by simpa using hur) ?_ ?_
      · simp
        field [cf.hr]
      · simp
        field [cf.hr]

------------- (u+r) * q 0 = -q 2, (u + r) * q 1 = -k * q 2 --------------


------------- general case --------------

def eDeno (p q : Fin 3 → K) :=
  (cf.r * ((cf.u + cf.r) * q 0 - q 2) * ((cf.u + cf.r) * q 1 + cf.k * q 2)) * p 2

def eNume (p q : Fin 3 → K) :=
  (cf.k * p 0 + ((cf.u + cf.r) ^ 2 - 1) * p 1) * q 2 ^ 2
  + (2 * cf.u * cf.k * q 0 ^ 2 + cf.u *((cf.u + cf.r) ^ 2 - 2) * q 0 * q 1
  + (cf.r * (cf.u + cf.r) - 2) * cf.k * q 0 * q 2 +
  (2 - (cf.u + cf.r) * (cf.u + 2 * cf.r)) *  q 1 * q 2 - cf.u * cf.k * q 2 ^ 2) * p 2

def SingularE (pq : P2 K × P2 K) : Prop := P2.lift₂ (fun p q hp hq ↦
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
    (hes : ¬SingularE cf pq) :
    (elliptic cf).Equation (exNormal cf pq) (eyNormal cf pq) := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  simp only [SingularE, P2.lift₂_mk] at hes
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
    (hes : ¬SingularE cf pq) :
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
  simp only [SingularE, P2.lift₂_mk] at hes
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
    (hes : ¬SingularE cf pq) :=
  Point.some (nonsingular_exNormal_eyNormal cf hk hpq hleft hright hes)

theorem fPoint_eNormal [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬SingularE cf pq) :
    fPoint cf (eNormal cf hk hpq hleft hright hes) = pq.1 := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  classical
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  have hes : eDeno cf p q ≠ 0 := by simpa [SingularE] using hes
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
