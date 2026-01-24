import Poncelet.Elliptic
import Poncelet.Heavy.Inverse1
import Poncelet.Heavy.Inverse2
import Poncelet.Heavy.Inverse3
import Poncelet.Heavy.Inverse4
import Poncelet.Heavy.Inverse5
import Poncelet.Heavy.Inverse6

open WeierstrassCurve.Affine

variable {K : Type*} [Field K]
variable (cf : Config K)

------------- p 2 = 0 --------------

def ZeroZ [DecidableEq K] (pq : P2 K × P2 K) : Prop := P2.lift₂ (fun p q hp hq ↦ p 2 = 0) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp [hl, hl0]
  ) pq.1 pq.2
deriving Decidable

def eyZeroZ (pq : P2 K × P2 K) : K := P2.lift₂
  (fun p q hp hq ↦ - p 1 * cf.u * cf.k / (p 0 * cf.r ^ 2))
  (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp [hl]
    grind
  ) pq.1 pq.2

theorem nonsingular_eyZeroZ [DecidableEq K] [NeZero (2 : K)]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
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

def eZeroZ [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (hz : ZeroZ pq) :=
  Point.some (nonsingular_eyZeroZ cf hk hpq hz)

theorem fPoint_eZeroZ [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0)
    {pq : P2 K × P2 K}
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

def SingularA [DecidableEq K] (pq : P2 K × P2 K) : Prop := P2.lift₂
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
deriving Decidable

theorem SingularA.u_add_r_ne_zero [DecidableEq K] {pq : P2 K × P2 K} (h : SingularA cf pq) :
    cf.u + cf.r ≠ 0 := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  by_contra!
  simp [SingularA, P2.lift₂_mk, this] at h
  grind

theorem SingularA.q1_eq [DecidableEq K] {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
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

theorem SingularA.q_eq [DecidableEq K] {pq : P2 K × P2 K} (h : SingularA cf pq)
    (hpq : pq ∈ dom cf) :
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

theorem SingularA.p2_ne_zero [DecidableEq K] {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
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

theorem SingularA.p_equation [DecidableEq K] {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
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

theorem SingularA.p01_eq [DecidableEq K] {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
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

theorem nonsingular_exSingularA_eySingularA [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0)
    {pq : P2 K × P2 K} (hpq : pq ∈ dom cf) (h : SingularA cf pq) :
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

def eSingularA [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularA cf pq) :=
  Point.some (nonsingular_exSingularA_eySingularA cf hk hpq h)

theorem fPoint_eSingularA [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
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

def SingularAB [DecidableEq K] (pq : P2 K × P2 K) : Prop := P2.lift₂
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
deriving Decidable

------------- Subcase: SingularAbc casePos --------------

theorem SingularAB.q_eq_of_casePos [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : SingularAB cf pq)
    (hur : cf.u + cf.r = 0) (hpq : pq ∈ dom cf) (hz : ¬ ZeroZ pq) :
    (pq.2 = P2.mk ![1, cf.k, 0] (by simp) ∧ pq.1 = P2.mk ![0, 0, 1] (by simp)) ∨
    (pq.2 = P2.mk ![1, -cf.k, 0] (by simp) ∧ pq.1 = P2.mk ![0, 0, 1] (by simp)) := by
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
      · rw [P2.mk_eq_mk']
        use p 2
        ext i
        fin_cases i
        · simpa using h0
        · simpa [h0, hk] using hp01.symm
        · simp
      · contrapose! hz
        simpa using h0
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
      · rw [P2.mk_eq_mk']
        use p 2
        ext i
        fin_cases i
        · simpa using h0
        · simpa [h0, hk] using hp01.symm
        · simp
      · contrapose! hz
        simpa using h0

def eSingularABcasePos [DecidableEq K] [NeZero (2 : K)]
    (pq : P2 K × P2 K) : (elliptic cf).Point :=
  if pq.2 = P2.mk ![1, cf.k, 0] (by simp) then
    .some (show (elliptic cf).Nonsingular 0 0 by
      rw [nonsingular_elliptic]
      simp [cf.hu]
    )
  else
    .zero

theorem f_eSingularABcasePos [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : SingularAB cf pq) (hk : cf.k ≠ 0)
    (hur : cf.u + cf.r = 0) (hpq : pq ∈ dom cf) (hz : ¬ ZeroZ pq) :
    f cf (eSingularABcasePos cf pq) = pq := by
  have hur' : cf.r + cf.u = 0 := by linear_combination hur
  have hr : cf.r = - cf.u := by linear_combination hur
  obtain hcases := SingularAB.q_eq_of_casePos cf h hur hpq hz
  by_cases hq : pq.2 = P2.mk ![1, cf.k, 0] (by simp)
  · obtain ⟨_, hp⟩ := hcases.resolve_right (by
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
    have hs : SingularAbc cf 0 0 := by
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
  · obtain ⟨hqeq, hp⟩ := hcases.resolve_left (by
      apply not_and_of_not_left
      exact hq
    )
    suffices (P2.mk ![cf.u + cf.r, 0, 1] _, P2.mk ![1, -cf.k, cf.u + cf.r] _) = pq by
      simpa [eSingularABcasePos, hp, hq, f, fPoint, fChord, fPointRaw, fChordRaw]
    ext
    · simp [hp, hur]
    · simp [hqeq, hur]

------------- SingularAB general --------------

theorem SingularAB.q_eq [DecidableEq K] {pq : P2 K × P2 K} (h : SingularAB cf pq)
    (hur : cf.u + cf.r ≠ 0) :
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

theorem SingularAB.p_eq [DecidableEq K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (h : SingularAB cf pq) (hpq : pq ∈ dom cf) (hur : cf.u + cf.r ≠ 0) :
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

theorem f_eSingularAB [DecidableEq K] [hchar : NeZero (2 : K)]
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

def SingularB [DecidableEq K] (pq : P2 K × P2 K) : Prop := P2.lift₂
  (fun p q hp hq ↦ (cf.u + cf.r) * q 1 = -cf.k * q 2 ∧ (cf.u + cf.r) * q 0 ≠ q 2) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    congrm ?_ ∧ ?_
    · simp [hm]
      grind
    · contrapose!
      simp [hm]
      grind
  ) pq.1 pq.2
deriving Decidable

theorem SingularB.u_add_r_ne_zero [DecidableEq K] {pq : P2 K × P2 K} (h : SingularB cf pq) :
    cf.u + cf.r ≠ 0 := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  by_contra!
  simp [SingularB, P2.lift₂_mk, this] at h
  grind

theorem SingularB.q0_eq [DecidableEq K] {p q : Fin 3 → K} {hp : p ≠ 0} {hq : q ≠ 0}
    (h : SingularB cf ⟨P2.mk p hp, P2.mk q hq⟩) (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    (cf.u + cf.r) * q 0 = -q 2 := by
  simp only [SingularB, P2.lift₂_mk] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  have : ((cf.u + cf.r) * q 0) ^ 2 = (q 2) ^ 2 := by
    simp_rw [mul_pow]
    obtain h12 := congr($h1 ^ 2)
    simp_rw [mul_pow, neg_sq, cf.k_sq] at h12
    linear_combination -congr($h12) + (cf.u + cf.r) ^ 2 * hi
  obtain h | h := eq_or_eq_neg_of_sq_eq_sq _ _ this
  · simp [h] at h2
  · exact h

theorem SingularB.q_eq [DecidableEq K] [NeZero (2 : K)] {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) :
    pq.2 = P2.mk ![-1, -cf.k, cf.u + cf.r] (by simp) := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  simp only
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ (by simpa using h.u_add_r_ne_zero) ?_ ?_
  · simpa [mul_comm (q 0)] using h.q0_eq cf hpq
  · simp only [SingularB, P2.lift₂_mk] at h
    simpa [mul_comm (q _)] using h.1

theorem SingularB.p1_equation [DecidableEq K] [NeZero (2 : K)]
    {p : Fin 3 → K} {hp : p ≠ 0} {q : P2 K}
    (hpq : ⟨P2.mk p hp, q⟩ ∈ dom cf) (h : SingularB cf ⟨P2.mk p hp, q⟩) :
    -cf.k * p 1 = p 0 + (cf.u + cf.r) * p 2 := by
  obtain hq := h.q_eq cf hpq
  simp only at hq
  rw [hq] at hpq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp _ |>.mp hpq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hpq
  linear_combination hpq

theorem SingularB.p_equation [DecidableEq K] [NeZero (2 : K)]
    {p : Fin 3 → K} {hp : p ≠ 0} {q : P2 K}
    (hpq : ⟨P2.mk p hp, q⟩ ∈ dom cf) (h : SingularB cf ⟨P2.mk p hp, q⟩) :
    (cf.u + cf.r) ^ 2 * p 0 ^ 2 +
    2 * (cf.r + 2 * cf.u - cf.u * (cf.u + cf.r) ^ 2) * p 0 * p 2 +
    (2 * cf.r * (cf.u + cf.r) + (cf.u + cf.r) ^ 3 * (cf.u - cf.r)) * p 2 ^ 2
    = 0 := by
  obtain hpq' := h.p1_equation cf hpq
  obtain hq := h.q_eq cf hpq
  simp only at hq
  rw [hq] at hpq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp _ |>.mp hpq
  have hpq' : ((cf.u + cf.r) ^ 2 - 1) * p 1 ^ 2 = (p 0 + (cf.u + cf.r) * p 2) ^ 2 := by
    rw [← cf.k_sq]
    linear_combination congr($hpq' ^ 2)
  linear_combination ((cf.u + cf.r) ^ 2 - 1) * ho - hpq'

def exSingularB (pq : P2 K × P2 K) : K := P2.lift₂
  (fun p q hp hq ↦ (cf.u + cf.r) ^ 2 * (p 0 + (cf.r - cf.u) * p 2) / (2 * cf.r * p 2)) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp_rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    field
  ) pq.1 pq.2

def eySingularB (pq : P2 K × P2 K) : K := P2.lift₂
  (fun p q hp hq ↦ (cf.u + cf.r) *
    ((cf.u * cf.r + cf.r ^ 2 - 1) * (cf.u + cf.r) * p 0 +
    (cf.r^4 + cf.r^3 * cf.u - cf.r^2 * cf.u^2 - cf.r * cf.u^3 - cf.u^2 - cf.r^2) * p 2)
    / (2 * cf.r ^ 2 * p 2)) (
  by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp_rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    field
  ) pq.1 pq.2

theorem equation_exSingularB_eySingularB [DecidableEq K] [NeZero (2 : K)] {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) (hz : ¬ ZeroZ pq) :
    (elliptic cf).Equation (exSingularB cf pq) (eySingularB cf pq) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hpeq := h.p_equation cf hpq
  have hp2 : p 2 ≠ 0 := by simpa [ZeroZ] using hz
  rw [equation_elliptic]
  simp only [eySingularB, P2.lift₂_mk, exSingularB]
  field_simp
  linear_combination - (cf.u + cf.r)^2 *
    (-cf.u^3*cf.r*p 2 - cf.u^2*cf.r^2*p 2 + cf.u*cf.r^3*p 2 + cf.r^4*p 2 +
    p 0*cf.u^2*cf.r + 2*p 0*cf.u*cf.r^2 + p 0*cf.r^3 - 2*cf.u^2*p 2) * hpeq

theorem nonsingular_exSingularB_eySingularB [DecidableEq K] [hchar : NeZero (2 : K)] (hk : cf.k ≠ 0)
    {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) (hz : ¬ ZeroZ pq)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp)) :
    (elliptic cf).Nonsingular (exSingularB cf pq) (eySingularB cf pq) := by
  obtain _ := cf.hr
  obtain hu0 := cf.hu
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hp1 := h.p1_equation cf hpq
  obtain hpeq := h.p_equation cf hpq
  have hp2 : p 2 ≠ 0 := by simpa [ZeroZ] using hz
  obtain hur0 := h.u_add_r_ne_zero
  by_contra! hs
  obtain ⟨hux, hy⟩ :=
    (singular_elliptic cf _ _).mp ⟨(equation_exSingularB_eySingularB cf hpq h hz), hs⟩
  have hy : (cf.u * cf.r + cf.r ^ 2 - 1) * (cf.u + cf.r) * p 0 +
      (cf.r ^ 4 + cf.r ^ 3 * cf.u - cf.r ^ 2 * cf.u ^ 2 - cf.r * cf.u ^ 3 - cf.u ^ 2 - cf.r ^ 2)
      * p 2 = 0 := by
    simpa [eySingularB, cf.hr, hp2, hchar.out, hur0] using hy
  obtain ⟨hu, hx⟩ | ⟨hu, hx⟩ := hux
  · have hx : (cf.u + cf.r) ^ 2 * (p 0 + (cf.r - cf.u) * p 2) = p 2 * 2 * (cf.r - 1) := by
      simp only [exSingularB,  P2.lift₂_mk] at hx
      field_simp at hx
      linear_combination hx
    obtain hu | hu := hu
    · have hr0 : cf.r - 1 ≠ 0 := by
        by_contra! h
        simp [hu, h] at hu0
      rw [hu] at hx
      rw [hu] at hy
      have hy : (cf.r - 1) * (4*p 0 *cf.r^2 + 4*cf.r^2*p 2 - 2*cf.r*p 2 - p 0 + p 2) = 0 := by
        linear_combination hy
      have hy : (4*p 0 *cf.r^2 + 4*cf.r^2*p 2 - 2*cf.r*p 2 - p 0 + p 2) = 0 := by
        simpa [hr0] using hy
      have heq : 2 * (2*cf.r - 1) * (p 0 + p 2) = 0 := by
        linear_combination hy - hx
      obtain hr | hp02 : (2*cf.r - 1) = 0 ∨ (p 0 + p 2) = 0 := by simpa [hchar.out] using heq
      · grind
      have hp02': p 0 = - p 2 := by linear_combination hp02
      rw [hp02'] at hy
      have : p 2 * 2 * (cf.r - 1) = 0 := by linear_combination -hy
      have hr : cf.r = 1 := by simpa [sub_eq_zero, hp2, hchar.out] using this
      contrapose! hleft
      simp only
      rw [P2.mk_eq_mk']
      use p 2
      ext i
      fin_cases i
      · simpa using hp02'
      · simpa [hu, hr, hp02, hk] using hp1
      · simp
    · rw [hu] at hy
      have heq : (cf.r - 1) * (p 0 + p 2) = 0 := by linear_combination hy
      obtain hr | hp02 := mul_eq_zero.mp heq
      · grind
      have hp02': p 0 = - p 2 := by linear_combination hp02
      contrapose! hleft
      simp only
      rw [P2.mk_eq_mk']
      use p 2
      ext i
      fin_cases i
      · simpa using hp02'
      · simpa [hu, hp02, hk] using hp1
      · simp
  · have hx : (cf.u + cf.r) ^ 2 * (p 0 + (cf.r - cf.u) * p 2) = p 2 * 2 * (cf.r + 1) := by
      simp only [exSingularB,  P2.lift₂_mk] at hx
      field_simp at hx
      linear_combination hx
    obtain hu | hu := hu
    · rw [hu] at hx
      rw [hu] at hy
      have : p 2 = -(2 * cf.r + 1) * p 0 := by linear_combination cf.r * hx - hy
      rw [this] at hx
      have : 4 * (2*cf.r + 1) * (cf.r + 1)^2 * p 0 = 0 := by linear_combination hx
      obtain hr | hr | hx : 2*cf.r + 1 = 0 ∨ cf.r + 1 = 0 ∨ p 0 = 0 := by
        simpa [h4, or_assoc] using this
      · grind
      · grind
      · grind
    · rw [hu] at hx
      rw [hu] at hy
      have : (cf.r + 1) * (p 0 - p 2) = 0 := by linear_combination hy
      obtain hr | hp02 := mul_eq_zero.mp this
      · grind
      contrapose! hright
      simp only
      rw [P2.mk_eq_mk']
      use p 2
      ext i
      fin_cases i
      · simpa [sub_eq_zero] using hp02
      · rw [hu, (show -cf.r - 1 + cf.r = -1 by ring)] at hp1
        simpa [hu, hp02, hk, ← sub_eq_add_neg] using hp1
      · simp

def eSingularB [DecidableEq K] [NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) (hz : ¬ ZeroZ pq)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp)) :=
  Point.some (nonsingular_exSingularB_eySingularB cf hk hpq h hz hleft hright)

theorem fPoint_eSingularB [DecidableEq K] [hchar : NeZero (2 : K)]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) (hz : ¬ ZeroZ pq)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp)) :
    fPoint cf (eSingularB cf hk hpq h hz hleft hright) = pq.1 := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hpeq := h.p_equation cf hpq
  have hp2 : p 2 ≠ 0 := by simpa [ZeroZ] using hz
  obtain hp1 := h.p1_equation cf hpq
  have hp1 : p 1 = -(p 0 + (cf.u + cf.r) * p 2) / cf.k := by
    field_simp
    linear_combination - hp1
  simp only [fPoint, fPointRaw, eSingularB, exSingularB, P2.lift₂_mk, eySingularB]
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ hp2 ?_ ?_
  · simp only [Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    linear_combination -(-cf.u^3*p 2 - cf.u^2*cf.r*p 2 + cf.u*cf.r^2*p 2 +
      cf.r^3*p 2 + cf.u^2*p 0 + 2*cf.u*cf.r*p 0 + cf.r^2*p 0 - 2*cf.r*p 2) * hpeq
  · rw [hp1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    rw [cf.k_sq]
    linear_combination (cf.u^3*p 2 + 5*cf.u^2*cf.r*p 2 + 7*cf.u*cf.r^2*p 2 + 3*cf.r^3*p 2 +
      cf.u^2*p 0 + 2*cf.u*cf.r*p 0 + cf.r^2*p 0 - 2*cf.r*p 2) * hpeq

theorem fChord_eSingularB [DecidableEq K] [hchar : NeZero (2 : K)]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) (hz : ¬ ZeroZ pq)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp)) :
    fChord cf (eSingularB cf hk hpq h hz hleft hright) = pq.2 := by
  have hk2 : (cf.u + cf.r)^2 - 1 ≠ 0 := by
    rw [← cf.k_sq]
    simpa using hk
  have hur0 := h.u_add_r_ne_zero
  obtain _ := cf.hr
  obtain _ := cf.hu
  rw [h.q_eq cf hpq]
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hpeq := h.p_equation cf hpq
  have hp2 : p 2 ≠ 0 := by simpa [ZeroZ] using hz
  by_cases hs : SingularAbc cf (exSingularB cf (P2.mk p hp, P2.mk q hq))
    (eySingularB cf (P2.mk p hp, P2.mk q hq))
  · obtain hc := hs.c_factor_eq_zero cf
      (nonsingular_exSingularB_eySingularB cf hk hpq h hz hleft hright)
    simp only [exSingularB, P2.lift₂_mk] at hc
    field_simp at hc
    have hc' : ((cf.u + cf.r) ^ 2 - 1) * (cf.u + cf.r)^2 * (p 0 + (cf.r-cf.u) *p 2) *
      ((cf.u + cf.r) ^ 2*p 0 +
      (-cf.u^3 - cf.u^2*cf.r+ cf.u*cf.r^2+ cf.r^3- 4*cf.u+ 2*cf.r)*p 2) = 0 := by
      linear_combination hc - (cf.u + cf.r) ^ 2 * hpeq
    have hc'' : 2 * p 2 * ((cf.u + cf.r)^2 - 1) * (cf.u + cf.r)^2 *
      ((-cf.u^3*cf.r - cf.u^2*cf.r^2 + cf.u*cf.r^3 + cf.r^4 + 2*cf.u^2 - 4*cf.u*cf.r)*p 2 +
      (cf.u^2*cf.r + 2*cf.u*cf.r^2 + cf.r^3 - 4*cf.u)*p 0) = 0 := by
      linear_combination hc - (cf.u + cf.r) ^ 4 * hpeq
    have hc'' :
      ((-cf.u^3*cf.r - cf.u^2*cf.r^2 + cf.u*cf.r^3 + cf.r^4 + 2*cf.u^2 - 4*cf.u*cf.r)*p 2 +
      (cf.u^2*cf.r + 2*cf.u*cf.r^2 + cf.r^3 - 4*cf.u)*p 0) = 0 := by
      simpa [hchar.out, hp2, hk2, hur0] using hc''
    have hc' : p 0 + (cf.r - cf.u) * p 2 = 0 ∨
      (cf.u + cf.r) ^ 2 * p 0 +
      (-cf.u ^ 3 - cf.u ^ 2 * cf.r + cf.u * cf.r ^ 2
       + cf.r ^ 3 - 4 * cf.u + 2 * cf.r) * p 2 = 0 := by
      simpa [hk2, hur0] using hc'
    obtain hc' | hc' := hc'
    · have hp0 : p 0 = (cf.u - cf.r) * p 2 := by linear_combination hc'
      rw [hp0] at hc''
      have h : 2 * p 2 * cf.u ^ 2 = 0 := by linear_combination -hc''
      simp [hchar.out, hp2, cf.hu] at h
    have hp0 : p 0 = -(-cf.u ^ 3 - cf.u ^ 2 * cf.r + cf.u * cf.r ^ 2
       + cf.r ^ 3 - 4 * cf.u + 2 * cf.r) * p 2 / (cf.u + cf.r) ^ 2 := by
       field_simp
       linear_combination hc'
    rw [hp0] at hc''
    field_simp at hc''
    have hc'' : 2 * p 2 * (cf.u^4 - 2*cf.u^2*cf.r^2 + cf.r^4 + 8*cf.u^2 - 4*cf.u*cf.r) = 0 := by
      linear_combination -hc''
    have hc'' : cf.u^4 - 2*cf.u^2*cf.r^2 + cf.r^4 + 8*cf.u^2 - 4*cf.u*cf.r = 0 := by
      simpa [hp2, hchar.out] using hc''
    simp only [fChord, fChordRaw, eSingularB, hs, ↓reduceIte]
    simp only [exSingularB, P2.lift₂_mk]
    conv_rhs => rw [← P2.mk'_eq]
    refine P2.mk'_eq_mk'_of_third _ (by simpa using hur0) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val]
      field_simp
      linear_combination 2 * (cf.u + cf.r) * hc''
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
      rw [hp0]
      field_simp
      rw [cf.k_sq]
      linear_combination -2 * (cf.u + cf.r) *
        (-cf.u^3 - cf.u^2*cf.r + cf.u*cf.r^2 + cf.r^3 + 2*cf.u) *hc''
  simp only [fChord, fChordRaw, eSingularB, hs, ↓reduceIte]
  simp only [fChordNormal, exSingularB, P2.lift₂_mk, eySingularB]
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ (by simpa using hur0) ?_ ?_
  · simp only [Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    linear_combination 2 *
      (-cf.u^5*p 2 - 3*cf.u^4*cf.r*p 2 - 2*cf.u^3*cf.r^2*p 2 + 2*cf.u^2*cf.r^3*p 2
      + 3*cf.u*cf.r^4*p 2 + cf.r^5*p 2 + cf.u^4*p 0 + 4*cf.u^3*cf.r*p 0
      + 6*cf.u^2*cf.r^2*p 0 + 4*cf.u*cf.r^3*p 0 + cf.r^4*p 0 - 2*cf.u^3*p 2
      - 4*cf.u^2*cf.r*p 2 - 2*cf.u*cf.r^2*p 2 + 4*cf.u*p 2) * hpeq
  · simp only [ Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    linear_combination 8 * p 2 * cf.u * hpeq

theorem f_eSingularB [DecidableEq K] [hchar : NeZero (2 : K)] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf) (h : SingularB cf pq) (hz : ¬ ZeroZ pq)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp)) :
    f cf (eSingularB cf hk hpq h hz hleft hright) = pq := by
  rw [f, fChord_eSingularB cf hk hpq h hz hleft hright,
    fPoint_eSingularB cf hk hpq h hz hleft hright]

------------- general case --------------

def eDeno (p q : Fin 3 → K) :=
  (cf.r * ((cf.u + cf.r) * q 0 - q 2) * ((cf.u + cf.r) * q 1 + cf.k * q 2)) * p 2

def eNume (p q : Fin 3 → K) :=
  (cf.k * p 0 + ((cf.u + cf.r) ^ 2 - 1) * p 1) * q 2 ^ 2
  + (2 * cf.u * cf.k * q 0 ^ 2 + cf.u *((cf.u + cf.r) ^ 2 - 2) * q 0 * q 1
  + (cf.r * (cf.u + cf.r) - 2) * cf.k * q 0 * q 2 +
  (2 - (cf.u + cf.r) * (cf.u + 2 * cf.r)) *  q 1 * q 2 - cf.u * cf.k * q 2 ^ 2) * p 2

def SingularE [DecidableEq K] (pq : P2 K × P2 K) : Prop := P2.lift₂ (fun p q hp hq ↦
  eDeno cf p q = 0)
  (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    simp_rw [eDeno, hl, hm]
    simp only [Pi.smul_apply, smul_eq_mul]
    grind
  ) pq.1 pq.2
deriving Decidable

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

theorem equation_exNormal_eyNormal [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
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
    + cf.u ^ 2 * eNume cf p q * eDeno cf p q ^ 3) by
    linear_combination this
  unfold eNume eDeno
  obtain hk := cf.k_sq
  exact inverse1 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) cf.u cf.r cf.k ho hi hpq cf.k_sq

theorem nonsingular_exNormal_eyNormal [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
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

def eNormal [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬SingularE cf pq) :=
  Point.some (nonsingular_exNormal_eyNormal cf hk hpq hleft hright hes)

theorem fPoint_eNormal [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
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
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
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
    exact inverse2 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) cf.u cf.r cf.k ho hi hpq cf.k_sq
  · simp only [Fin.isValue, Matrix.cons_val]
    field_simp

theorem fChord_eNormal_singularAbc [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0)
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0)
    (hmem : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf)
    (hleft : P2.mk p hp ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : P2.mk p hp ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬SingularE cf ⟨P2.mk p hp, P2.mk q hq⟩)
    (hs : SingularAbc cf (eNume cf p q / eDeno cf p q) (eyNormal cf (P2.mk p hp, P2.mk q hq))) :
    fChord cf (eNormal cf hk hmem hleft hright hes) = P2.mk q hq := by
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hmem
  obtain _ := cf.hr
  obtain _ := cf.hu
  have heDeno0 : eDeno cf p q ≠ 0 := by simpa [SingularE] using hes
  have hp2 : p 2 ≠ 0 := by
    contrapose! hes
    simp [SingularE, eDeno, hes]
  have hpoint := hs.fPoint_eq cf (nonsingular_exNormal_eyNormal cf hk hmem hleft hright hes)
  have hpe := fPoint_eNormal cf hk hmem hleft hright hes
  unfold eNormal at hpe
  rw [hpe] at hpoint
  simp only at hpoint
  obtain ⟨l, hl0, hl⟩ := (P2.mk_eq_mk _ _).mp hpoint
  have hp0 : p 0 = l * (2 * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2)) := by
    simpa using congr($hl 0)
  have hp1 : p 1 = l * (
      (cf.r * (cf.u + cf.r) ^ 2 * (eNume cf p q / eDeno cf p q) -
      cf.u * ((cf.u + cf.r) ^ 2 - 2)) * (cf.u ^ 2 - cf.r ^ 2)) := by
    simpa using congr($hl 1)
  have hp2 : p 2 = l * (4 * cf.u ^ 2 * cf.k) := by
    simpa using congr($hl 2)
  have hp1' : p 1 ^ 2 = -(2 * l * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2)) ^ 2 := by
    rw [hp0, hp2] at ho
    linear_combination ho
  have hpq : p 1 * q 1 = p 2 * q 2 - p 0 * q 0 := by
    linear_combination hpq
  have hpq' : p 1 ^ 2 * q 1 ^ 2 = (p 2 * q 2 - p 0 * q 0) ^ 2 := by
    rw [← mul_pow, hpq]
  have hi' : q 1 ^ 2 = q 2 ^ 2 - q 0 ^ 2 := by
    linear_combination hi
  simp only [fChord, fChordRaw, eNormal, exNormal_mk, hs, ↓reduceIte]
  by_cases hq2 : q 2 = 0
  · rw [hq2] at hi hpq
    have hq1 : q 1 ^ 2 = - q 0 ^ 2 := by simpa [hq2] using hi'
    have hq0ne0 : q 0 ≠ 0 := by
      by_contra! hq0
      suffices q = 0 from hq this
      ext i
      fin_cases i
      · simpa using hq0
      · simpa [hq0] using hq1
      · exact hq2
    have hq1ne0 : q 1 ≠ 0 := by
      contrapose! hq0ne0 with h
      simpa [h] using hq1
    have hDeno : eDeno cf p q = (cf.u + cf.r) ^ 2 * cf.r * q 0 * q 1 * p 2 := by
      simp_rw [eDeno, hq2]
      ring
    have hur0 : cf.u + cf.r ≠ 0 := by
      contrapose! heDeno0 with h
      simp [hDeno, h]
    have hNume : eNume cf p q =
        (2 * cf.u * cf.k * q 0 ^ 2 +
        cf.u * ((cf.u + cf.r) ^ 2 - 2) * q 0 * q 1) * p 2 := by
      simp_rw [eNume, hq2]
      ring
    obtain ha := hs.a_eq_zero cf
    simp only [eyNormal, exNormal_mk, P2.lift₂_mk] at ha
    field_simp at ha
    simp_rw [hDeno, hNume] at ha
    have : 4 * cf.u^2 * cf.r^3 * p 2^3 * q 0^3 * cf.k^2 * q 1 * (((cf.u+cf.r)^2-1)*q 1 + cf.k*q 0) *
        (cf.k * ((cf.u + cf.r) ^ 2 - 2) * q 1 + 2 * ((cf.u + cf.r) ^ 2 - 1) * q 0) *
        ((cf.u ^ 2 - cf.r ^ 2) * p 2 + 2 * cf.u * p 0)  = 0 := by
      apply inverse6 (p 0) (p 1) (p 2) (q 0) (q 1) cf.u cf.r cf.k
        (by linear_combination hi)
        (by linear_combination hpq)
        cf.k_sq
        (by linear_combination ha)
    obtain h | h | h : ((cf.u + cf.r) ^ 2 - 1) * q 1 + cf.k * q 0 = 0
        ∨ cf.k * ((cf.u + cf.r) ^ 2 - 2) * q 1 + 2 * ((cf.u + cf.r) ^ 2 - 1) * q 0 = 0
        ∨ (cf.u ^ 2 - cf.r ^ 2) * (l * (4 * cf.u ^ 2 * cf.k)) + 2 * cf.u * p 0 = 0 := by
        simpa [cf.hu, cf.hr, hp2, hl0, hk, hq0ne0, hq1ne0, or_assoc] using this
    · have : ((cf.u + cf.r) ^ 2 - 1) * q 1 = -cf.k * q 0 := by linear_combination h
      have : ((cf.u + cf.r) ^ 2 - 1) ^ 2 * q 1 ^ 2 = cf.k ^ 2 * q 0 ^ 2 := by
        linear_combination congr($this ^ 2)
      rw [hq1, cf.k_sq] at this
      have : -(cf.u + cf.r) ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * q 0 ^ 2 = 0 := by
        linear_combination this
      simp [hq0ne0, hur0, ← cf.k_sq, hk] at this
    · have : cf.k * ((cf.u + cf.r) ^ 2 - 2) * q 1 = -2 * ((cf.u + cf.r) ^ 2 - 1) * q 0 := by
        linear_combination h
      have : cf.k ^ 2 * ((cf.u + cf.r) ^ 2 - 2) ^ 2 * q 1 ^ 2 =
          4 * ((cf.u + cf.r) ^ 2 - 1) ^ 2 * q 0 ^ 2 := by
        linear_combination congr($this ^ 2)
      rw [hq1, cf.k_sq] at this
      have : ((cf.u + cf.r) ^ 2 - 1) * q 0 ^ 2 * (cf.u + cf.r) ^ 4 = 0 := by
        linear_combination -this
      simp [hq0ne0, ← cf.k_sq, hk, hur0] at this
    rw [hp0] at h
    have : 8 * cf.u ^ 2 * l * cf.k * (cf.u - cf.r) * (cf.u + cf.r) = 0 := by
      linear_combination h
    have hur : cf.u = cf.r := by
      simpa [hl0, hk, hur0, cf.hu, sub_eq_zero] using this
    refine P2.mk_eq_mk_of_third_zero _ _ (by simp [hur]) hq2 ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    simp_rw [hNume, hDeno, hur]
    linear_combination 32 * cf.k * q 0 * p 2 * cf.r ^ 6 * hq1
  rw [hp1', hp0, hp2, hi'] at hpq'
  have hq02 : 4 * l ^ 2 * cf.u ^ 2 * q 2 * cf.k ^ 2 *
      (((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2) * q 2 - 4 * cf.u * (cf.u ^ 2 - cf.r ^ 2) * q 0)
      = 0 := by
    linear_combination -hpq'
  have hq02 : ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2) * q 2 -
      4 * cf.u * (cf.u ^ 2 - cf.r ^ 2) * q 0 = 0 := by
    simpa [hl0, cf.hu, hq2, hk] using hq02
  have hq02' : 4 * cf.u * (cf.u ^ 2 - cf.r ^ 2) * q 0 =
      ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2) * q 2 := by
    linear_combination -hq02
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ (by simpa using hq2) ?_ ?_
  · simp only [Matrix.cons_val_zero, Matrix.cons_val]
    linear_combination 2 * cf.u * cf.k * hq02
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    have hur : cf.u ^ 2 - cf.r ^ 2 ≠ 0 := by
      contrapose! hq2 with hur
      simpa [hur, cf.hu] using hq02
    have hp1ne0 : p 1 ≠ 0 := by
      contrapose! hur with hp1ne0
      simpa [hp1ne0, hl0, cf.hu, hk] using hp1'
    rw [← mul_left_inj' (show l * p 1 * (cf.u ^ 2 - cf.r ^ 2) ≠ 0 by
      simp [hl0, hp1ne0, hur] )]
    suffices p 1 ^ 2 * q 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2) =
        8 * l * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2) ^ 2 * (p 1 * q 1) by
      rw [hp1] at ⊢ this
      linear_combination this
    rw [hp1', hpq]
    suffices -(2 * l * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2)) ^ 2 * q 2 *
        ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2) =
        8 * l * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2) ^ 2 * p 2 * q 2 -
        2 * l * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2) * p 0 *
        (4 * cf.u * (cf.u ^ 2 - cf.r ^ 2) * q 0) by
      linear_combination this
    rw [hq02', hp0, hp2]
    ring

theorem fChord_eNormal [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hmem : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬SingularE cf pq) :
    fChord cf (eNormal cf hk hmem hleft hright hes) = pq.2 := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hmem
  have hes : eDeno cf p q ≠ 0 := by simpa [SingularE] using hes
  have hp2 : p 2 ≠ 0 := by
    contrapose! hes
    simp [eDeno, hes]
  by_cases hs : SingularAbc cf (eNume cf p q / eDeno cf p q) (eyNormal cf (P2.mk p hp, P2.mk q hq))
  · exact fChord_eNormal_singularAbc cf hk hp hq hmem hleft hright hes hs
  simp only [fChord, fChordRaw, eNormal, exNormal_mk, hs, ↓reduceIte]
  simp only [fChordNormal, eyNormal, exNormal_mk, P2.lift₂_mk]
  by_cases hq2 : q 2 = 0
  · refine P2.mk_eq_mk_of_third_zero _ _ ?_ (by simpa using hq2) ?_
    · simp only [Matrix.cons_val, mul_eq_zero]
      right
      field_simp
      unfold eNume eDeno
      rw [hq2]
      linear_combination
        hi * (-8*p 2^2*q 0^2*cf.u*cf.r^3*cf.k^4 - 4*p 2^2*q 0^2*cf.r^4*cf.k^4
            + 4*p 2^2*q 0^2*cf.r^2*cf.k^6 - 8*p 2^2*q 0^2*cf.u*cf.r^3*cf.k^2
            - 4*p 2^2*q 0^2*cf.r^4*cf.k^2 + 8*p 2^2*q 0^2*cf.r^2*cf.k^4
            + 4*p 2^2*q 0^2*cf.r^2*cf.k^2) +
        cf.k_sq * (-4*p 2^2*q 0^2*q 1^2*cf.u^4*cf.r^2
          - 8*p 2^2*q 0^2*q 1^2*cf.u^3*cf.r^3 - 4*p 2^2*q 0^2*q 1^2*cf.u^2*cf.r^4
          - 4*p 2^2*q 0^4*cf.u^2*cf.r^2*cf.k^2 - 4*p 2^2*q 0^2*q 1^2*cf.u^2*cf.r^2*cf.k^2
          - 4*p 2^2*q 0^4*cf.r^2*cf.k^4 - 4*p 2^2*q 0^2*q 1^2*cf.r^2*cf.k^4
          - 4*p 2^2*q 0^4*cf.r^2*cf.k^2 - 4*p 2^2*q 0^2*q 1^2*cf.r^2*cf.k^2) +
        hq2 * (-8*p 2^2*q 0^2*q 2*cf.u*cf.r^3*cf.k^4 - 4*p 2^2*q 0^2*q 2*cf.r^4*cf.k^4
          + 4*p 2^2*q 0^2*q 2*cf.r^2*cf.k^6 - 8*p 2^2*q 0^2*q 2*cf.u*cf.r^3*cf.k^2
          - 4*p 2^2*q 0^2*q 2*cf.r^4*cf.k^2 + 8*p 2^2*q 0^2*q 2*cf.r^2*cf.k^4
          + 4*p 2^2*q 0^2*q 2*cf.r^2*cf.k^2)
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      unfold eNume eDeno
      simp only [hq2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, add_zero, sub_zero, zero_add] at ⊢ hi hpq
      exact inverse5 (p 0) (p 1) (p 2) (q 0) (q 1) cf.u cf.r cf.k ho hi hpq cf.k_sq
  conv_rhs => rw [← P2.mk'_eq]
  refine P2.mk'_eq_mk'_of_third _ (by simpa using hq2) ?_ ?_
  · simp only [Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    unfold eNume eDeno
    exact inverse3 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) cf.u cf.r cf.k ho hi hpq cf.k_sq
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    unfold eNume eDeno
    exact inverse4 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) cf.u cf.r cf.k ho hi hpq cf.k_sq

theorem f_eNormal [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hleft : pq.1 ≠ P2.mk ![-1, 0, 1] (by simp))
    (hright : pq.1 ≠ P2.mk ![1, 0, 1] (by simp))
    (hes : ¬SingularE cf pq) :
    f cf (eNormal cf hk hpq hleft hright hes) = pq := by
  rw [f, fChord_eNormal cf hk hpq hleft hright, fPoint_eNormal cf hk hpq hleft hright]

def e [DecidableEq K] [CharZero K] (pq : P2 K × P2 K) :=
  if hk : cf.k ≠ 0 then
    if hpq : pq ∈ dom₀ cf then
      if hes : SingularE cf pq then
        if hz : ZeroZ pq then
          eZeroZ cf hk ((mem_dom₀' cf).mp hpq).1 hz
        else if hsa : SingularA cf pq then
          eSingularA cf hk ((mem_dom₀' cf).mp hpq).1 hsa
        else if SingularAB cf pq then
          if cf.u + cf.r = 0 then
            eSingularABcasePos cf pq
          else
            eSingularAB cf pq
        else if hsb : SingularB cf pq then
          eSingularB cf hk ((mem_dom₀' cf).mp hpq).1 hsb hz
            ((mem_dom₀' cf).mp hpq).2.2 ((mem_dom₀' cf).mp hpq).2.1
        else
          .zero -- Unreachable
      else
        eNormal cf hk ((mem_dom₀' cf).mp hpq).1
          ((mem_dom₀' cf).mp hpq).2.2 ((mem_dom₀' cf).mp hpq).2.1 hes
    else
      .zero
  else
    .zero

theorem f_e [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) {pq : P2 K × P2 K}
    (hpq : pq ∈ dom₀ cf) :
    f cf (e cf pq) = pq := by
  have hpq' := hpq
  let ⟨hpq', hright, hleft⟩ := (mem_dom₀' cf).mp hpq'
  by_cases hes : SingularE cf pq
  · by_cases hz : ZeroZ pq
    · simpa [e, hes, hz, hk, hpq] using f_eZeroZ cf hk hpq' hz
    by_cases hsa : SingularA cf pq
    · simpa [e, hes, hz, hsa, hk, hpq] using f_eSingularA cf hk hpq' hsa
    by_cases hsab : SingularAB cf pq
    · by_cases hur : cf.u + cf.r = 0
      · simpa [e, hes, hz, hsa, hsab, hur, hk, hpq]
        using f_eSingularABcasePos cf hsab hk hur hpq' hz
      simpa [e, hes, hz, hsa, hsab, hur, hk, hpq] using f_eSingularAB cf hsab hk hur hpq'
    by_cases hsb : SingularB cf pq
    · simpa [e, hes, hz, hsa, hsab, hsb, hk, hpq] using f_eSingularB cf hk hpq' hsb hz hleft hright
    obtain ⟨p, q⟩ := pq
    induction p with | mk p hp
    induction q with | mk q hq
    simp only [ZeroZ, P2.lift₂_mk] at hz
    simp only [SingularA, P2.lift₂_mk] at hsa
    simp only [SingularB, P2.lift₂_mk] at hsb
    simp only [SingularAB, P2.lift₂_mk] at hsab
    obtain h | h : (cf.u + cf.r) * q 0 - q 2 = 0 ∨ (cf.u + cf.r) * q 1 + cf.k * q 2 = 0 := by
      simpa [SingularE, eDeno, cf.hr, hz] using hes
    · grind
    · grind
  simpa [e, hes, hk, hpq] using f_eNormal cf hk hpq' hleft hright hes

theorem rightInvOn_e_f [DecidableEq K] [CharZero K] (hk : cf.k ≠ 0) :
    Set.RightInvOn (e cf) (f cf) (dom₀ cf) := by
  intro p hp
  apply f_e cf hk hp
