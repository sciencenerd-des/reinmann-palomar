/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile041Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/16), (17907/1280)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((11/16), (17907/1280))
  have he : value ((11/16), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((427/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87449600/1487566249), (-45841920/1487566249)), 0, by norm_num⟩
  | 1 => ⟨((-2772975455436800/2212853345163930001), (4008857567232000/2212853345163930001)), 0, by norm_num⟩
  | 2 => ⟨((156913647/17592186044416), (-319115865/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((481790981/562949953421312), (1278000943/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-541654911/9007199254740992), (-482261265/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1494527861/576460752303423488), (373077647/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-397423535/4611686018427387904), (385989243/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((652467767/295147905179352825856), (-573442623/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-330960285/9444732965739290427392), (215271631/2361183241434822606848)), (13/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-28318779/75557863725914323419136), (-973117287/302231454903657293676544)), (5/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((586358325/9671406556917033397649408), (859454495/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-975293385/309485009821345068724781056), (-519282127/309485009821345068724781056)), (11/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((586697399/4951760157141521099596496896), (3773643/4951760157141521099596496896)), (1/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((427/32), (17907/2560)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((427/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((427/32), (17907/2560)))⁻¹=value ((87449600/1487566249), (-45841920/1487566249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((87449600/1487566249), (-45841920/1487566249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1456230715/536870912), (129607935/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((43724800/1487566249), (-22920960/1487566249)), 0, by norm_num⟩
  | 2 => ⟨((-693243863859200/2212853345163930001), (1002214391808000/2212853345163930001)), 0, by norm_num⟩
  | 3 => ⟨((52304549/35184372088832), (-106371955/8796093022208)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((481790981/4503599627370496), (1278000943/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-433323929/72057594037927936), (-96452253/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((996351907/4611686018427387904), (248718431/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-908396651/147573952589676412928), (110282641/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((652467767/4722366482869645213696), (-573442623/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-36773365/18889465931478580854784), (1530820487/302231454903657293676544)), (3/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-90620093/4835703278458516698824704), (-1556987659/9671406556917033397649408)), (33/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((213221209/77371252455336267181195264), (1250115629/309485009821345068724781056)), (45/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-325097795/2475880078570760549798248448), (-692376169/9903520314283042199192993792)), (59/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-13987/553472), (381/40960)), 0, by norm_num⟩
  | 45 => ⟨((364827007577/16322553446400), (-3036951/241172480)), 0, by norm_num⟩
  | 44 => ⟨((-1924314858654253/91928621010124800), (56245638026279/4741643894784000)), 0, by norm_num⟩
  | 43 => ⟨((740283529/34359738368), (-382104407/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-773938237/34359738368), (387074393/34359738368)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((797306043/34359738368), (-402612741/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-203835857/8589934592), (103852087/8589934592)), (3/34359738368), by norm_num⟩
  | 39 => ⟨((834769373/34359738368), (-212709125/17179869184)), (3/34359738368), by norm_num⟩
  | 38 => ⟨((-856802937/34359738368), (106341/8388608)), (3/34359738368), by norm_num⟩
  | 37 => ⟨((27514357/1073741824), (-223445615/17179869184)), (3/34359738368), by norm_num⟩
  | 36 => ⟨((-905234121/34359738368), (229556241/17179869184)), (3/34359738368), by norm_num⟩
  | 35 => ⟨((465636911/17179869184), (-117993117/8589934592)), (3/34359738368), by norm_num⟩
  | 34 => ⟨((-958848387/34359738368), (485491531/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((988139549/34359738368), (-499791027/34359738368)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-31852765/1073741824), (257485277/17179869184)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((1052460297/34359738368), (-132777091/8589934592)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-543929061/17179869184), (274144817/17179869184)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1125717313/34359738368), (-566617307/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-1166304939/34359738368), (586211367/34359738368)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((604963163/17179869184), (-151802123/8589934592)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-314233519/8589934592), (629764855/34359738368)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((1307737983/34359738368), (-654060535/34359738368)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1362816807/34359738368), (680304583/34359738368)), (3/34359738368), by norm_num⟩
  | 23 => ⟨((711366607/17179869184), (-708741009/34359738368)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-186019123/4294967296), (92457039/4294967296)), (1/17179869184), by norm_num⟩
  | 21 => ⟨((779934891/17179869184), (-386694561/17179869184)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-819418697/17179869184), (101292829/4294967296)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((215776523/4294967296), (-106375095/4294967296)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-113963113/2147483648), (111993673/4294967296)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((966091051/17179869184), (-472952335/17179869184)), (3/17179869184), by norm_num⟩
  | 16 => ⟨((-513680747/8589934592), (125218923/4294967296)), (3/17179869184), by norm_num⟩
  | 15 => ⟨((1096908527/17179869184), (-266148889/8589934592)), (3/17179869184), by norm_num⟩
  | 14 => ⟨((-294131533/4294967296), (567919089/17179869184)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((634282883/8589934592), (-76080027/2147483648)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1376170581/17179869184), (20488709/536870912)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((5873587/67108864), (-355242061/8589934592)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-828501529/8589934592), (193828995/4294967296)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((922504041/8589934592), (-213281875/4294967296)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-260101413/2147483648), (474118979/8589934592)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((298145133/2147483648), (-533558425/8589934592)), (3/8589934592), by norm_num⟩
  | 6 => ⟨((-1396380299/8589934592), (304977257/4294967296)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((420786589/2147483648), (-355867587/4294967296)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-528938499/2147483648), (53375093/536870912)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((710301287/2147483648), (-266687115/2147483648)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-1075071965/2147483648), (88701401/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1085423775/1073741824), (-264453025/1073741824)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-64583041/1073741824), (518431741/1073741824)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-85/512), (17907/40960)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-85/512), (17907/40960)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-85/512), (17907/40960))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((1456230715/536870912), (129607935/268435456)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((427/32), (17907/2560))) (z:=((-85/512), (17907/40960))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((1456230715/536870912), (129607935/268435456))) (r:=(1/268435456)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((411/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((263910445/8388608), (844720245/33554432)), (1/8388608), by norm_num⟩
  | 1 => ⟨((123582569/67108864), (66872043/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16607506112998400/2212853345163930001), (-9025218818573760/2212853345163930001)), 0, by norm_num⟩
  | 3 => ⟨((-465812179/8796093022208), (358576543/4398046511104)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((37248581/281474976710656), (-1861701399/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((246881883/18014398509481984), (69928313/2251799813685248)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-702309229/1152921504606846976), (-272750911/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((1365787055/73786976294838206464), (57277079/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1071513593/2361183241434822606848), (363925939/2361183241434822606848)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((653518081/75557863725914323419136), (-350539669/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-212694511/2417851639229258349412352), (1613903303/4835703278458516698824704)), (65/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-172516131/77371252455336267181195264), (-1444883569/154742504910672534362390528)), (711/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((223421921/1237940039285380274899124224), (503252233/2475880078570760549798248448)), (473/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-427/32), (-17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((151974957/8388608), (610009615/33554432)), (5/33554432), by norm_num⟩
  | 1 => ⟨((90028137/67108864), (66872043/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16607506112998400/2212853345163930001), (-9025218818573760/2212853345163930001)), 0, by norm_num⟩
  | 3 => ⟨((-465812179/8796093022208), (358576543/4398046511104)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((37248581/281474976710656), (-1861701399/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((246881883/18014398509481984), (69928313/2251799813685248)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-702309229/1152921504606846976), (-272750911/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((1365787055/73786976294838206464), (57277079/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1071513593/2361183241434822606848), (363925939/2361183241434822606848)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((653518081/75557863725914323419136), (-350539669/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-212694511/2417851639229258349412352), (1613903303/4835703278458516698824704)), (65/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-172516131/77371252455336267181195264), (-1444883569/154742504910672534362390528)), (711/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((223421921/1237940039285380274899124224), (503252233/2475880078570760549798248448)), (473/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((986702737/536870912), 0), (1/1073741824), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((986702737/1073741824), 0), (1/2147483648), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((638734289/33554432), (610009615/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((90028137/67108864), (66872043/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16607506112998400/2212853345163930001), (-9025218818573760/2212853345163930001)), 0, by norm_num⟩
  | 3 => ⟨((-465812179/8796093022208), (358576543/4398046511104)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((37248581/281474976710656), (-1861701399/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((246881883/18014398509481984), (69928313/2251799813685248)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-702309229/1152921504606846976), (-272750911/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((1365787055/73786976294838206464), (57277079/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1071513593/2361183241434822606848), (363925939/2361183241434822606848)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((653518081/75557863725914323419136), (-350539669/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-212694511/2417851639229258349412352), (1613903303/4835703278458516698824704)), (65/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-172516131/77371252455336267181195264), (-1444883569/154742504910672534362390528)), (711/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((223421921/1237940039285380274899124224), (503252233/2475880078570760549798248448)), (473/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5545950910873600/2212853345163930001), (-8017715134464000/2212853345163930001)), 0, by norm_num⟩
  | 1 => ⟨((-156913647/4398046511104), (319115865/1099511627776)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-90335809/17592186044416), (-239625177/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((541654911/1125899906842624), (482261265/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-934079913/36028797018963968), (-233173529/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((1192270605/1152921504606846976), (-72372983/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1141818593/36893488147419103232), (501762295/18446744073709551616)), (9/36893488147419103232), by norm_num⟩
  | 7 => ⟨((330960285/590295810358705651712), (-215271631/147573952589676412928)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((63717253/9444732965739290427392), (273689237/4722366482869645213696)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-732947907/604462909807314587353088), (-537159059/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1341028405/19342813113834066795298816), (178503231/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1760092197/618970019642690137449562112), (-353779/19342813113834066795298816)), (25/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((449884347/4951760157141521099596496896), (-232157265/4951760157141521099596496896)), (19/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((156913647/4398046511104), (-319115865/1099511627776)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((90335809/8796093022208), (239625177/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-812482367/562949953421312), (-361695949/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((467039957/4503599627370496), (116586765/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-93146141/18014398509481984), (361864915/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 5 => ⟨((856363945/4611686018427387904), (-752643443/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-144795125/36893488147419103232), (753450709/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-63717253/1180591620717411303424), (-273689237/590295810358705651712)), (5/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((824566395/75557863725914323419136), (1208607883/75557863725914323419136)), (17/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-838142753/1208925819614629174706176), (-446258077/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1210063385/38685626227668133590597632), (3891569/19342813113834066795298816)), (23/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-1349653041/1237940039285380274899124224), (696471795/1237940039285380274899124224)), (9/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((270102525/9903520314283042199192993792), (-770330345/19807040628566084398385987584)), (29/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-481790981/70368744177664), (-1278000943/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((1083309823/562949953421312), (964522531/562949953421312)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-467039957/2251799813685248), (-116586765/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((496779419/36028797018963968), (-241243277/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((-713636621/1152921504606846976), (627202869/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((144795125/9223372036854775808), (-753450709/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((74336795/295147905179352825856), (159652055/73786976294838206464)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-274855465/4722366482869645213696), (-805738589/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((628607065/151115727451828646838272), (669387117/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-2016772309/9671406556917033397649408), (-1621487/1208925819614629174706176)), (31/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((618590977/77371252455336267181195264), (-638432479/154742504910672534362390528)), (13/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-270102525/1237940039285380274899124224), (770330345/2475880078570760549798248448)), (11/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((160359829/79228162514264337593543950336), (-1238655653/79228162514264337593543950336)), (35/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-541654911/562949953421312), (-482261265/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((467039957/2251799813685248), (116586765/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((-745169129/36028797018963968), (361864915/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 3 => ⟨((713636621/576460752303423488), (-627202869/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((-361987813/9223372036854775808), (941813387/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-223010385/295147905179352825856), (-478956165/73786976294838206464)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((60124633/295147905179352825856), (352510633/1180591620717411303424)), (5/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-628607065/37778931862957161709568), (-669387117/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((141804303/151115727451828646838272), (1824173/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-386619361/9671406556917033397649408), (399020299/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((742781943/618970019642690137449562112), (-1059204225/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-7516867/618970019642690137449562112), (232247935/2475880078570760549798248448)), (45/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-114976931/79228162514264337593543950336), (-622069203/158456325028528675187087900672)), (19/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1494527861/18014398509481984), (-373077647/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((596135303/36028797018963968), (-72372983/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 2 => ⟨((-428181973/288230376151711744), (752643443/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 3 => ⟨((579180501/9223372036854775808), (-1506901419/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((13938149/9223372036854775808), (1915824661/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-577196477/1180591620717411303424), (-846025519/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((220012473/4722366482869645213696), (234285491/9444732965739290427392)), (15/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-1815095079/604462909807314587353088), (-11674707/604462909807314587353088)), (29/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((1391829699/9671406556917033397649408), (-718236539/9671406556917033397649408)), (7/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-92847743/19342813113834066795298816), (1059204225/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((132296859/2475880078570760549798248448), (-510945457/1237940039285380274899124224)), (25/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((137972317/19807040628566084398385987584), (186620761/9903520314283042199192993792)), (43/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-222281391/316912650057057350374175801344), (-801942367/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-397423535/72057594037927936), (385989243/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 1 => ⟨((570909297/576460752303423488), (-1003524591/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 2 => ⟨((-579180501/9223372036854775808), (1506901419/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-148673589/73786976294838206464), (-1277216441/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 4 => ⟨((60124633/73786976294838206464), (352510633/295147905179352825856)), (13/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-220012473/2361183241434822606848), (-234285491/4722366482869645213696)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((2117610927/302231454903657293676544), (13620491/302231454903657293676544)), (39/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-463943233/1208925819614629174706176), (59853045/302231454903657293676544)), (11/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((278543229/19342813113834066795298816), (-794403169/38685626227668133590597632)), (11/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-220494765/1237940039285380274899124224), (1703151525/1237940039285380274899124224)), (43/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-988083/38685626227668133590597632), (-1368552247/19807040628566084398385987584)), (41/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((222281391/79228162514264337593543950336), (25060699/9903520314283042199192993792)), (19/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-923787451/5070602400912917605986812821504), (-236926453/5070602400912917605986812821504)), (17/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-652467767/2305843009213693952), (573442623/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((165480143/4611686018427387904), (-861086525/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 2 => ⟨((127434505/73786976294838206464), (1094756949/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-274855465/295147905179352825856), (-402869295/295147905179352825856)), (17/590295810358705651712), by norm_num⟩
  | 4 => ⟨((1257214131/9444732965739290427392), (334693559/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-1815095081/151115727451828646838272), (-11674707/151115727451828646838272)), (5/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((927886467/1208925819614629174706176), (-59853045/151115727451828646838272)), (25/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-318335119/9671406556917033397649408), (113486167/2417851639229258349412352)), (15/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((141746635/309485009821345068724781056), (-1094883123/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((361356069/4951760157141521099596496896), (122192165/618970019642690137449562112)), (33/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-349299329/39614081257132168796771975168), (-630097575/79228162514264337593543950336)), (33/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((1583635631/2535301200456458802993406410752), (203079817/1267650600228229401496703205376)), (31/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-1337774081/40564819207303340847894502572032), (315723577/40564819207303340847894502572032)), (29/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-330960285/36893488147419103232), (215271631/9223372036854775808)), (13/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-63717253/73786976294838206464), (-1094756949/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 2 => ⟨((824566395/1180591620717411303424), (1208607885/1180591620717411303424)), (7/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-1257214131/9444732965739290427392), (-334693559/4722366482869645213696)), (33/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((1134434425/75557863725914323419136), (1824173/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-1391829701/1208925819614629174706176), (179559135/302231454903657293676544)), (45/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((278543229/4835703278458516698824704), (-794403169/9671406556917033397649408)), (31/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-141746635/154742504910672534362390528), (273720781/38685626227668133590597632)), (19/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-406525577/2475880078570760549798248448), (-1099729485/2475880078570760549798248448)), (11/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((873248323/39614081257132168796771975168), (787621969/39614081257132168796771975168)), (47/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-1088749497/633825300114114700748351602688), (-279234749/633825300114114700748351602688)), (49/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((1003330561/10141204801825835211973625643008), (-236792683/10141204801825835211973625643008)), (49/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-689141969/162259276829213363391578010288128), (298931335/81129638414606681695789005144064)), (47/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28318779/147573952589676412928), (973117287/590295810358705651712)), (5/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-183236977/590295810358705651712), (-1074318119/2361183241434822606848)), (7/590295810358705651712), by norm_num⟩
  | 2 => ⟨((419071377/4722366482869645213696), (446258079/9444732965739290427392)), (25/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-252096539/18889465931478580854784), (-12971897/151115727451828646838272)), (61/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((386619361/302231454903657293676544), (-99755075/151115727451828646838272)), (31/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-742781945/9671406556917033397649408), (529602113/4835703278458516698824704)), (49/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((220494765/154742504910672534362390528), (-1703151525/154742504910672534362390528)), (71/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((361356069/1237940039285380274899124224), (977537321/1237940039285380274899124224)), (47/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-873248323/19807040628566084398385987584), (-787621969/19807040628566084398385987584)), (7/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((1209721663/316912650057057350374175801344), (9695651/9903520314283042199192993792)), (1/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-1226292909/5070602400912917605986812821504), (289413279/5070602400912917605986812821504)), (69/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((918855959/81129638414606681695789005144064), (-797150227/81129638414606681695789005144064)), (9/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-206158767/649037107316853453566312041152512), (1052495147/1298074214633706907132624082305024)), (9/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((586358325/9444732965739290427392), (859454495/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-1341028407/37778931862957161709568), (-178503231/9444732965739290427392)), (45/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((1210063387/151115727451828646838272), (7783139/151115727451828646838272)), (43/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-309295489/302231454903657293676544), (19951015/37778931862957161709568)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((92847743/1208925819614629174706176), (-529602113/4835703278458516698824704)), (15/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-132296859/77371252455336267181195264), (255472729/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-505898497/1237940039285380274899124224), (-171069031/154742504910672534362390528)), (79/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((698598659/9903520314283042199192993792), (630097575/9903520314283042199192993792)), (55/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-1088749497/158456325028528675187087900672), (-279234749/158456325028528675187087900672)), (35/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((1226292909/2535301200456458802993406410752), (-289413279/2535301200456458802993406410752)), (83/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-1010741555/40564819207303340847894502572032), (438432625/20282409603651670423947251286016)), (93/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((494781041/649037107316853453566312041152512), (-1262994177/649037107316853453566312041152512)), (101/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((144241341/10384593717069655257060992658440192), (164074545/1298074214633706907132624082305024)), (105/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21862400/4462698747), (-3820160/1487566249)), 0, by norm_num⟩
  | 1 => ⟨((-693243863859200/6638560035491790003), (334071463936000/2212853345163930001)), 0, by norm_num⟩
  | 2 => ⟨((52304549/70368744177664), (-106371955/17592186044416)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((321193987/4503599627370496), (852000629/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-180551637/36028797018963968), (-160753755/36028797018963968)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((996351907/4611686018427387904), (248718431/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-1059796093/147573952589676412928), (128663081/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((869957023/4722366482869645213696), (-191147541/1180591620717411303424)), (11/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-110320095/37778931862957161709568), (1148115365/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-9439593/302231454903657293676544), (-324372429/1208925819614629174706176)), (27/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((195452775/38685626227668133590597632), (1145939327/154742504910672534362390528)), (41/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-325097795/1237940039285380274899124224), (-692376169/4951760157141521099596496896)), (59/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1564526397/158456325028528675187087900672), (1257881/19807040628566084398385987584)), (43/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((638898669/33554432), (609923445/33554432)), (7/33554432), by norm_num⟩
  | 1 => ⟨((1440338065/1073741824), (267650273/1073741824)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1031584097/137438953472), (-561381793/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-465184847/8796093022208), (359408575/4398046511104)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((143352085/1125899906842624), (-933362477/562949953421312)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((501547765/36028797018963968), (1120796121/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-355294443/576460752303423488), (-543491461/1152921504606846976)), (43/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1379380133/73786976294838206464), (217161595/73786976294838206464)), (101/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1078408599/2361183241434822606848), (190932621/1180591620717411303424)), (129/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((651158183/75557863725914323419136), (-721352615/75557863725914323419136)), (185/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-400957425/4835703278458516698824704), (1649713907/4835703278458516698824704)), (261/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-192834743/77371252455336267181195264), (-366630081/38685626227668133590597632)), (357/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((471289567/2475880078570760549798248448), (125852367/618970019642690137449562112)), (475/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55791519/562949953421312), (1815414699/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((-128477595/4503599627370496), (-1363201007/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((577765239/144115188075855872), (32150751/9007199254740992)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-1328469211/4611686018427387904), (-2590817/36028797018963968)), (3/2305843009213693952), by norm_num⟩
  | 4 => ⟨((1059796093/73786976294838206464), (-128663081/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-152242479/295147905179352825856), (535213115/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((411861689/37778931862957161709568), (-535787171/18889465931478580854784)), (9/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((90620093/604462909807314587353088), (1556987659/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-586358325/19342813113834066795298816), (-859454495/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((1192025249/618970019642690137449562112), (317339077/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-430244759/4951760157141521099596496896), (-1383669/2475880078570760549798248448)), (17/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((479876637/158456325028528675187087900672), (-15477151/9903520314283042199192993792)), (13/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-768291627/10141204801825835211973625643008), (1095580935/10141204801825835211973625643008)), (21/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((319449333/16777216), (38120217/2097152)), (1/4194304), by norm_num⟩
  | 1 => ⟨((720169017/536870912), (16728137/67108864)), (3/536870912), by norm_num⟩
  | 2 => ⟨((128948081/17179869184), (-280690651/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-465187381/8796093022208), (718816517/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((2240129/17592186044416), (-116670555/70368744177664)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((501529181/36028797018963968), (560406227/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-710576317/1152921504606846976), (-543524163/1152921504606846976)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((1379391195/73786976294838206464), (108628313/36893488147419103232)), (51/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-67405011/147573952589676412928), (47720041/295147905179352825856)), (65/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((325651847/37778931862957161709568), (-180318785/18889465931478580854784)), (93/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-200688793/2417851639229258349412352), (1649711205/4835703278458516698824704)), (523/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-48150107/19342813113834066795298816), (-733381077/77371252455336267181195264)), (715/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((117775499/618970019642690137449562112), (31479809/154742504910672534362390528)), (951/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-880404173/1152921504606846976), (-783865929/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((1518250527/9223372036854775808), (378999515/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-1211195537/73786976294838206464), (147043521/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((579971349/590295810358705651712), (-63715847/73786976294838206464)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-294186921/9444732965739290427392), (1530820489/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-90620093/151115727451828646838272), (-389246915/75557863725914323419136)), (15/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((781811101/4835703278458516698824704), (8952651/37778931862957161709568)), (17/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-127716991/9671406556917033397649408), (-544009847/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((1843906111/2475880078570760549798248448), (2965005/618970019642690137449562112)), (29/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-314204941/9903520314283042199192993792), (648566327/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((301828853/316912650057057350374175801344), (-107601699/79228162514264337593543950336)), (23/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-48871567/5070602400912917605986812821504), (1509980225/20282409603651670423947251286016)), (37/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-373766277/324518553658426726783156020576256), (-252777327/81129638414606681695789005144064)), (1/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((319449333/16777216), (38120217/2097152)), (9/33554432), by norm_num⟩
  | 1 => ⟨((720169017/536870912), (16728137/67108864)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((515792323/68719476736), (-561381301/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-116296843/2199023255552), (718816509/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((143368221/1125899906842624), (-1866728789/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((501529159/36028797018963968), (280203067/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-710576131/1152921504606846976), (-271761945/576460752303423488)), (45/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1379390221/73786976294838206464), (217256107/73786976294838206464)), (103/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-539239209/1180591620717411303424), (381760339/2361183241434822606848)), (131/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((651301297/75557863725914323419136), (-721273903/75557863725914323419136)), (187/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-100343245/1208925819614629174706176), (824852319/2417851639229258349412352)), (131/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-385202347/154742504910672534362390528), (-733375317/77371252455336267181195264)), (179/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((942198289/4951760157141521099596496896), (251834615/1237940039285380274899124224)), (119/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((242239107/73786976294838206464), (-117634817/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-695965619/1180591620717411303424), (152918033/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 2 => ⟨((353024305/9444732965739290427392), (-918492293/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((181240185/151115727451828646838272), (1556987661/151115727451828646838272)), (11/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-293179163/604462909807314587353088), (-26857953/37778931862957161709568)), (17/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((1072822725/19342813113834066795298816), (142802585/4835703278458516698824704)), (11/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-1290734279/309485009821345068724781056), (-4151007/154742504910672534362390528)), (25/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((1131137787/4951760157141521099596496896), (-570029/4835703278458516698824704)), (27/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-84889365/9903520314283042199192993792), (242103823/19807040628566084398385987584)), (7/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((134396809/1267650600228229401496703205376), (-519055703/633825300114114700748351602688)), (27/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((308357179/20282409603651670423947251286016), (834165179/20282409603651670423947251286016)), (13/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-541943201/324518553658426726783156020576256), (-488802967/324518553658426726783156020576256)), (47/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((1126140893/10384593717069655257060992658440192), (72206157/2596148429267413814265248164610048)), (43/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((319449333/16777216), (38120217/2097152)), (5/16777216), by norm_num⟩
  | 1 => ⟨((720169017/536870912), (16728137/67108864)), (1/134217728), by norm_num⟩
  | 2 => ⟨((515792323/68719476736), (-561381301/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-116296843/2199023255552), (718816509/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((35842055/281474976710656), (-933364395/562949953421312)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((501529161/36028797018963968), (1120812269/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-88822017/144115188075855872), (-271761945/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((689695119/36893488147419103232), (108628049/36893488147419103232)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-539239219/1180591620717411303424), (23860023/147573952589676412928)), (33/590295810358705651712), by norm_num⟩
  | 9 => ⟨((651301305/75557863725914323419136), (-721273965/75557863725914323419136)), (47/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-200686453/2417851639229258349412352), (1649704837/4835703278458516698824704)), (525/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-385202605/154742504910672534362390528), (-1466750867/154742504910672534362390528)), (717/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((471099413/2475880078570760549798248448), (503669299/2475880078570760549798248448)), (953/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-285272165/37778931862957161709568), (371107997/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-109842537/151115727451828646838272), (-1887257771/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((177684341/302231454903657293676544), (1041763025/1208925819614629174706176)), (25/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-541829659/4835703278458516698824704), (-288490071/4835703278458516698824704)), (29/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((1955657999/154742504910672534362390528), (12578809/154742504910672534362390528)), (53/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-599845797/618970019642690137449562112), (619086041/1237940039285380274899124224)), (5/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((480182267/9903520314283042199192993792), (-684738085/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-244357835/316912650057057350374175801344), (471868821/79228162514264337593543950336)), (67/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-350405885/2535301200456458802993406410752), (-947914977/2535301200456458802993406410752)), (39/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((752698891/40564819207303340847894502572032), (339446505/20282409603651670423947251286016)), (21/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((-938450745/649037107316853453566312041152512), (-240687191/649037107316853453566312041152512)), (43/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((1729647297/20769187434139310514121985316880384), (-204104131/10384593717069655257060992658440192)), (85/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-148501973/41538374868278621028243970633760768), (515329439/166153499473114484112975882535043072)), (21/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((319449333/16777216), (38120217/2097152)), (11/33554432), by norm_num⟩
  | 1 => ⟨((720169017/536870912), (16728137/67108864)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((515792323/68719476736), (-561381301/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-116296843/2199023255552), (718816509/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((35842055/281474976710656), (-933364395/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((501529161/36028797018963968), (1120812269/36028797018963968)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-88822017/144115188075855872), (-271761945/576460752303423488)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((689695119/36893488147419103232), (108628049/36893488147419103232)), (105/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-539239219/1180591620717411303424), (381760367/2361183241434822606848)), (133/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((325650653/37778931862957161709568), (-180318491/18889465931478580854784)), (189/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-401372913/4835703278458516698824704), (1649704835/4835703278458516698824704)), (263/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-12037581/4835703278458516698824704), (-733375435/77371252455336267181195264)), (359/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((117774851/618970019642690137449562112), (1007338613/4951760157141521099596496896)), (477/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-287835615/2417851639229258349412352), (-421894945/2417851639229258349412352)), (15/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((1316586531/19342813113834066795298816), (700999169/19342813113834066795298816)), (45/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((-297002127/19342813113834066795298816), (-3820641/38685626227668133590597632)), (43/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((151829101/77371252455336267181195264), (-313398135/309485009821345068724781056)), (7/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((-364621919/2475880078570760549798248448), (1039898939/4951760157141521099596496896)), (15/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((32471397/9903520314283042199192993792), (-1003265709/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((496677881/633825300114114700748351602688), (335902179/158456325028528675187087900672)), (79/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-685865847/5070602400912917605986812821504), (-618613279/5070602400912917605986812821504)), (55/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((1068905711/81129638414606681695789005144064), (68536339/20282409603651670423947251286016)), (35/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-1203942227/1298074214633706907132624082305024), (284138369/1298074214633706907132624082305024)), (83/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((992319559/20769187434139310514121985316880384), (-860883313/20769187434139310514121985316880384)), (23/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((-242881527/166153499473114484112975882535043072), (619987285/166153499473114484112975882535043072)), (25/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((-141612367/5316911983139663491615228241121378304), (-322168173/1329227995784915872903807060280344576)), (13/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((319449333/16777216), (38120217/2097152)), (3/8388608), by norm_num⟩
  | 1 => ⟨((720169017/536870912), (16728137/67108864)), (5/536870912), by norm_num⟩
  | 2 => ⟨((515792323/68719476736), (-561381301/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-116296843/2199023255552), (718816509/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((35842055/281474976710656), (-933364395/562949953421312)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((501529161/36028797018963968), (1120812269/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-88822017/144115188075855872), (-271761945/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((689695119/36893488147419103232), (108628049/36893488147419103232)), (53/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-539239219/1180591620717411303424), (381760367/2361183241434822606848)), (67/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((325650653/37778931862957161709568), (-180318491/18889465931478580854784)), (95/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-401372913/4835703278458516698824704), (1649704835/4835703278458516698824704)), (527/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-12037581/4835703278458516698824704), (-1466750869/154742504910672534362390528)), (719/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((117774851/618970019642690137449562112), (251834653/1237940039285380274899124224)), (955/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1219909913355881/8388608), (-485646542122645/4194304)), (480285909/4194304), by norm_num⟩
  | 1 => ⟨((447874943/2), (-238138675/2)), (739/4), by norm_num⟩
  | 2 => ⟨((1325245871/8), (-106827457/2)), 150, by norm_num⟩
  | 3 => ⟨((634459819/8), (-180907725/16)), (327/4), by norm_num⟩
  | 4 => ⟨((1779941847/64), (20155801/32)), (2153/64), by norm_num⟩
  | 5 => ⟨((122349839/16), (44847513/32)), (357/32), by norm_num⟩
  | 6 => ⟨((220179177/128), (306218481/512)), (199/64), by norm_num⟩
  | 7 => ⟨((667067591/2048), (349867989/2048)), (767/1024), by norm_num⟩
  | 8 => ⟨((108419835/2048), (628237057/16384)), (163/1024), by norm_num⟩
  | 9 => ⟨((490326263/65536), (943964435/131072)), (3975/131072), by norm_num⟩
  | 10 => ⟨((60689351/65536), (76753817/65536)), (687/131072), by norm_num⟩
  | 11 => ⟨((421310685/4194304), (706915987/4194304)), (3483/4194304), by norm_num⟩
  | 12 => ⟨((158713649/16777216), (365681653/16777216)), (8159/67108864), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((201097294736121/1267650600228229401496703205376), (-875902096347/10141204801825835211973625643008)), (465851/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((452971607158701/158456325028528675187087900672), (-1072707484585/633825300114114700748351602688)), (571135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1927036267921881/39614081257132168796771975168), (-151217491917/4951760157141521099596496896)), (644165/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1929177319931785/2475880078570760549798248448), (-643951140109/1237940039285380274899124224)), (342917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((28295046141367/2417851639229258349412352), (-645380802751/77371252455336267181195264)), (171853/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1586806850203917/9671406556917033397649408), (-1213135578131/9671406556917033397649408)), (646129/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1291427449847623/604462909807314587353088), (-532275162569/302231454903657293676544)), (567049/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((970454513246545/37778931862957161709568), (-1735647190267/75557863725914323419136)), (924629/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((668723251341371/2361183241434822606848), (-10209303881/36893488147419103232)), (348131/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1676433318393037/590295810358705651712), (-1805093580487/590295810358705651712)), (961917/590295810358705651712), by norm_num⟩
  | 8 => ⟨((946188150919559/36893488147419103232), (-2268823113419/73786976294838206464)), (1209273/73786976294838206464), by norm_num⟩
  | 7 => ⟨((237550794071117/1152921504606846976), (-2569670953713/9223372036854775808)), (1369955/9223372036854775808), by norm_num⟩
  | 6 => ⟨((835975159299027/576460752303423488), (-1295702575661/576460752303423488)), (1381961/1152921504606846976), by norm_num⟩
  | 5 => ⟨((315783579531707/36028797018963968), (-1146088740121/72057594037927936)), (1222863/144115188075855872), by norm_num⟩
  | 4 => ⟨((797571373157035/18014398509481984), (-3488286447771/36028797018963968)), (1861947/36028797018963968), by norm_num⟩
  | 3 => ⟨((1619833592581365/9007199254740992), (-4449316950433/9007199254740992)), (37135/140737488355328), by norm_num⟩
  | 2 => ⟨((1246367545086821/2251799813685248), (-4585650064475/2251799813685248)), (1226055/1125899906842624), by norm_num⟩
  | 1 => ⟨((1311279455164729/1125899906842624), (-7229658268701/1125899906842624)), (3872769/1125899906842624), by norm_num⟩
  | 0 => ⟨((1515943190777019/1125899906842624), (-7963968713765/562949953421312)), (8560623/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1515943190777019/1125899906842624), (-7963968713765/562949953421312)), (32656185154441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((510220767518391/281474976710656), (-10722910686661/281474976710656)), (11647369/562949953421312), by norm_num⟩
  | 2 => ⟨((924452517358041/281474976710656), (-77748321140509/562949953421312)), (43113057/562949953421312), by norm_num⟩
  | 3 => ⟨((47356632864569/4398046511104), (-63837496354595/70368744177664)), (73775579/140737488355328), by norm_num⟩
  | 4 => ⟨((1012600398525245/8796093022208), (-42961245268569/2199023255552)), (3364523/274877906944), by norm_num⟩
  | 5 => ⟨((884473711669169/68719476736), (-154552189997381/34359738368)), (226526363/68719476736), by norm_num⟩
  | 6 => ⟨((1219909913355881/8388608), (-485646542122645/4194304)), (480285909/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((319449333/16777216), (38120217/2097152)), (3/8388608), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8806400/332494249), (-45841920/332494249)), 0, by norm_num⟩
  | 1 => ⟨((1011964474163200/110552425618074001), (403702284288000/110552425618074001)), 0, by norm_num⟩
  | 2 => ⟨((-820138449/2199023255552), (320323301/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-309866853/8796093022208), (-588043875/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((779915641/281474976710656), (-558956637/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((451265461/4503599627370496), (978668985/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1175072101/72057594037927936), (290370727/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-71291379/1152921504606846976), (-169701227/144115188075855872)), (13/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1512525673/18446744073709551616), (104513343/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-275518639/147573952589676412928), (202999927/36893488147419103232)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-837242711/2361183241434822606848), (-14873263/73786976294838206464)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((702359217/37778931862957161709568), (-205654423/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((189628051/151115727451828646838272), (118623993/75557863725914323419136)), (33/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((43/32), (17907/2560)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((43/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((43/32), (17907/2560)))⁻¹=value ((8806400/332494249), (-45841920/332494249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((8806400/332494249), (-45841920/332494249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5120000/118886883), (-15280640/118886883)), 0, by norm_num⟩
  | 1 => ⟨((11515753267200/1570454549939521), (78236876800000/14134090949455689)), 0, by norm_num⟩
  | 2 => ⟨((-1129478349/2199023255552), (774166027/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-12715497/1099511627776), (-1428105881/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((804316785/281474976710656), (36817259/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-314967849/4503599627370496), (814351967/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-364419811/36028797018963968), (-604432863/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((872612993/1152921504606846976), (-270591319/576460752303423488)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((127914483/9223372036854775808), (1083715189/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-1202467793/295147905179352825856), (-110316051/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 10 => ⟨((32982339/295147905179352825856), (-1198427199/4722366482869645213696)), (27/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1050465517/75557863725914323419136), (955517169/75557863725914323419136)), (19/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-672211999/604462909807314587353088), (750934819/1208925819614629174706176)), (53/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((75/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((75/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((75/32), (17907/2560)))⁻¹=value ((5120000/118886883), (-15280640/118886883)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((5120000/118886883), (-15280640/118886883))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-655405108428800/39529204879035867), (-369278058496000/39529204879035867)), 0, by norm_num⟩
  | 1 => ⟨((1001080575/549755813888), (-1035547275/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((77334975/549755813888), (1014254355/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-416285755/17592186044416), (252018131/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-48802287/562949953421312), (-74471737/35184372088832)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((383116655/2251799813685248), (328634039/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-446232481/72057594037927936), (447401795/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-943904371/1152921504606846976), (-204106795/288230376151711744)), (13/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1256696709/18446744073709551616), (-874688501/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 9 => ⟨((325715257/147573952589676412928), (867157735/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-68818839/147573952589676412928), (61634591/1180591620717411303424)), (23/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((44281615/9444732965739290427392), (-650188139/18889465931478580854784)), (31/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1430724205/604462909807314587353088), (573524537/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((107/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21913600/393934249), (-45841920/393934249)), 0, by norm_num⟩
  | 1 => ⟨((810637882163200/155184192535194001), (1004561498112000/155184192535194001)), 0, by norm_num⟩
  | 2 => ⟨((-573880587/1099511627776), (272441665/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((257146065/35184372088832), (-297439249/8796093022208)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((496587937/281474976710656), (768857815/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-578878099/4503599627370496), (145611337/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-27005661/144115188075855872), (-668509951/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((1256724457/2305843009213693952), (284930067/1152921504606846976)), (13/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1089782671/36893488147419103232), (229088865/9223372036854775808)), (19/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-184055407/295147905179352825856), (-711168193/295147905179352825856)), (27/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1487949101/9444732965739290427392), (145136953/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-233099989/37778931862957161709568), (628018483/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-377188899/1208925819614629174706176), (-356746315/604462909807314587353088)), (19/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((107/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((107/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((107/32), (17907/2560)))⁻¹=value ((21913600/393934249), (-45841920/393934249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((21913600/393934249), (-45841920/393934249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-276174329/137438953472), (775029559/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-316750017/2199023255552), (-519866407/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((291057075/4398046511104), (21611265/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-337059083/140737488355328), (61295877/8796093022208)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-332129991/562949953421312), (-31020281/70368744177664)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((125580765/2251799813685248), (-358812273/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((134552155/72057594037927936), (830726501/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((-1188155135/2305843009213693952), (9685525/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((56997051/4611686018427387904), (-1500225959/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 9 => ⟨((834921449/295147905179352825856), (35420729/18446744073709551616)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-496486431/2361183241434822606848), (795051257/4722366482869645213696)), (29/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-581206287/75557863725914323419136), (-1464125621/75557863725914323419136)), (43/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((957170877/604462909807314587353088), (-158689187/1208925819614629174706176)), (63/1208925819614629174706176), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((139/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28467200/444315049), (-45841920/444315049)), 0, by norm_num⟩
  | 1 => ⟨((645550076723200/197415862767872401), (1304991105024000/197415862767872401)), 0, by norm_num⟩
  | 2 => ⟨((-980246233/2199023255552), (-47358671/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((290306533/17592186044416), (-380270999/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((82537277/140737488355328), (869057557/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1773072969/18014398509481984), (-172939743/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((149286419/36028797018963968), (-321550435/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((224739869/2305843009213693952), (411254001/1152921504606846976)), (25/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-794086285/36893488147419103232), (-118042301/18446744073709551616)), (17/36893488147419103232), by norm_num⟩
  | 9 => ⟨((75234869/73786976294838206464), (-66803437/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 10 => ⟨((66307671/4722366482869645213696), (1541426653/18889465931478580854784)), (65/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1408231973/302231454903657293676544), (-571151791/302231454903657293676544)), (11/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1193227483/4835703278458516698824704), (-217399637/1208925819614629174706176)), (119/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((139/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((139/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((139/32), (17907/2560)))⁻¹=value ((28467200/444315049), (-45841920/444315049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((28467200/444315049), (-45841920/444315049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73483059/4398046511104), (1309059733/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-325020509/4398046511104), (-106014947/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((561382983/70368744177664), (-344433435/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((458787801/562949953421312), (798669073/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-205563637/1125899906842624), (263197489/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 5 => ⟨((34267651/9007199254740992), (-336166013/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((896487243/576460752303423488), (559586529/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-610942403/4611686018427387904), (472982863/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-328394723/73786976294838206464), (-258257231/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 9 => ⟨((734420133/590295810358705651712), (29552247/590295810358705651712)), (33/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-364007239/9444732965739290427392), (224453913/2361183241434822606848)), (27/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-931073351/151115727451828646838272), (-828314499/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1373474279/2417851639229258349412352), (-759299605/2417851639229258349412352)), (1/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((171/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3891200/56422561), (-15280640/169267683)), 0, by norm_num⟩
  | 1 => ⟨((48612510924800/28651548508188489), (59460026368000/9550516169396163)), 0, by norm_num⟩
  | 2 => ⟨((-93327945/274877906944), (-303684621/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1262500193/70368744177664), (-743323749/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-79860717/562949953421312), (1321886119/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-866544231/18014398509481984), (-844665217/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((1088109221/288230376151711744), (-159797381/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-484928741/4611686018427387904), (109249537/576460752303423488)), (11/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-363653993/73786976294838206464), (-208104753/18446744073709551616)), (15/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1603618241/2361183241434822606848), (196633439/1180591620717411303424)), (39/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-1168769705/37778931862957161709568), (941158877/37778931862957161709568)), (51/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-34868319/604462909807314587353088), (-1363344065/604462909807314587353088)), (33/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1003844717/9671406556917033397649408), (727005783/9671406556917033397649408)), (85/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((171/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((171/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((171/32), (17907/2560)))⁻¹=value ((3891200/56422561), (-15280640/169267683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((3891200/56422561), (-15280640/169267683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((246486299/8796093022208), (669168327/35184372088832)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((-1280350965/140737488355328), (197667369/35184372088832)), (7/140737488355328), by norm_num⟩
  | 2 => ⟨((-19240967/70368744177664), (-1125719097/562949953421312)), (7/562949953421312), by norm_num⟩
  | 3 => ⟨((1278882249/4503599627370496), (11383319/140737488355328)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((-421473199/18014398509481984), (1027755663/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-34282471/18014398509481984), (-264459769/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((982673805/2305843009213693952), (-151213689/4611686018427387904)), (7/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-483042535/36893488147419103232), (1453578939/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-855252751/295147905179352825856), (-741802157/295147905179352825856)), (13/147573952589676412928), by norm_num⟩
  | 9 => ⟨((717065273/2361183241434822606848), (-361244061/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((89055095/37778931862957161709568), (548143313/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1396823355/604462909807314587353088), (-432819793/604462909807314587353088)), (61/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((74246669/604462909807314587353088), (-737706149/4835703278458516698824704)), (3/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((203/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((41574400/584398249), (-45841920/584398249)), 0, by norm_num⟩
  | 1 => ⟨((186525446963200/341521313434266001), (1905850318848000/341521313434266001)), 0, by norm_num⟩
  | 2 => ⟨((-65503797/274877906944), (-778795801/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1085205055/70368744177664), (-6702257/2199023255552)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-483025821/1125899906842624), (401537393/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-114531359/9007199254740992), (-1520338119/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((1214808685/576460752303423488), (577767583/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-526975689/4611686018427387904), (108380961/2305843009213693952)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((163887081/73786976294838206464), (-908129325/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 9 => ⟨((191673249/1180591620717411303424), (722530963/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-335795717/18889465931478580854784), (-85321623/18889465931478580854784)), (49/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((978610049/1208925819614629174706176), (-324335677/604462909807314587353088)), (59/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-149881151/19342813113834066795298816), (983295019/19342813113834066795298816)), (9/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((203/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((203/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((203/32), (17907/2560)))⁻¹=value ((41574400/584398249), (-45841920/584398249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((41574400/584398249), (-45841920/584398249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((245264393/70368744177664), (-237883657/281474976710656)), (5/281474976710656), by norm_num⟩
  | 1 => ⟨((-167382263/562949953421312), (1441225589/1125899906842624)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-60782443/281474976710656), (-801656577/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 3 => ⟨((185589385/4503599627370496), (-84033695/4503599627370496)), (9/18014398509481984), by norm_num⟩
  | 4 => ⟨((-11583551/72057594037927936), (885535187/144115188075855872)), (21/288230376151711744), by norm_num⟩
  | 5 => ⟨((-189817851/288230376151711744), (-388169915/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1187530159/18446744073709551616), (-457629645/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((133946449/73786976294838206464), (1198260181/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-928341515/1180591620717411303424), (-24957103/147573952589676412928)), (27/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((835037831/18889465931478580854784), (-1124527651/18889465931478580854784)), (25/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((242275215/75557863725914323419136), (433013967/75557863725914323419136)), (43/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-1352529285/2417851639229258349412352), (126318667/2417851639229258349412352)), (71/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((282794295/19342813113834066795298816), (-107078291/2417851639229258349412352)), (29/9671406556917033397649408), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((235/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1024000/14342567), (-975360/14342567)), 0, by norm_num⟩
  | 1 => ⟨((-48624435200/205709228149489), (998768640000/205709228149489)), 0, by norm_num⟩
  | 2 => ⟨((-344479879/2199023255552), (-797627415/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1654898923/140737488355328), (161518293/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-1033095389/2251799813685248), (202017879/562949953421312)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((75224761/18014398509481984), (-255896333/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((470935993/576460752303423488), (333244063/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-78947117/1152921504606846976), (-248939215/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((856903743/295147905179352825856), (-17031749/9223372036854775808)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-192926501/4722366482869645213696), (777482015/4722366482869645213696)), (25/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-312785359/75557863725914323419136), (-1098062153/151115727451828646838272)), (57/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((477345601/1208925819614629174706176), (143421743/1208925819614629174706176)), (65/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-1402682745/77371252455336267181195264), (711102699/77371252455336267181195264)), (73/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((235/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((235/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((235/32), (17907/2560)))⁻¹=value ((1024000/14342567), (-975360/14342567)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1024000/14342567), (-975360/14342567))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((430930251/2251799813685248), (-334801205/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 1 => ⟨((622411663/9007199254740992), (1159528657/9007199254740992)), (13/9007199254740992), by norm_num⟩
  | 2 => ⟨((-1238182905/36028797018963968), (-2427821/9007199254740992)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((419263595/144115188075855872), (-762876155/144115188075855872)), (13/144115188075855872), by norm_num⟩
  | 4 => ⟨((556312671/1152921504606846976), (850304333/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-1035021321/9223372036854775808), (49927941/4611686018427387904)), (21/9223372036854775808), by norm_num⟩
  | 6 => ⟨((179297051/36893488147419103232), (-894474677/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((543359313/590295810358705651712), (311161429/295147905179352825856)), (25/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-160971725/1180591620717411303424), (331171359/9444732965739290427392)), (3/590295810358705651712), by norm_num⟩
  | 9 => ⟨((52565801/18889465931478580854784), (-496583539/37778931862957161709568)), (23/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1168133747/1208925819614629174706176), (912688449/1208925819614629174706176)), (81/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-933766619/9671406556917033397649408), (461092143/9671406556917033397649408)), (69/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-22027583/154742504910672534362390528), (-1414490763/154742504910672534362390528)), (115/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((267/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18227200/258970083), (-15280640/258970083)), 0, by norm_num⟩
  | 1 => ⟨((-16455476838400/22355167963008963), (278523281408000/67065503889026889)), 0, by norm_num⟩
  | 2 => ⟨((-6639711/68719476736), (-369145705/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((587776281/70368744177664), (430233915/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-216251089/562949953421312), (156330581/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((84866519/9007199254740992), (-2282691/140737488355328)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((42352609/288230376151711744), (122320443/144115188075855872)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1114627909/36893488147419103232), (-942056217/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1072302015/590295810358705651712), (4288349/590295810358705651712)), (23/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-151450637/2361183241434822606848), (251879233/4722366482869645213696)), (25/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((103311777/151115727451828646838272), (-1139230091/302231454903657293676544)), (53/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((210711537/2417851639229258349412352), (369499281/2417851639229258349412352)), (7/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-1172257949/154742504910672534362390528), (-434351967/154742504910672534362390528)), (117/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((267/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((267/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((267/32), (17907/2560)))⁻¹=value ((18227200/258970083), (-15280640/258970083)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((18227200/258970083), (-15280640/258970083))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73438645/18014398509481984), (-290224521/9007199254740992)), (15/36028797018963968), by norm_num⟩
  | 1 => ⟨((488322279/36028797018963968), (216064417/36028797018963968)), (15/72057594037927936), by norm_num⟩
  | 2 => ⟨((-890239581/288230376151711744), (316716607/144115188075855872)), (19/288230376151711744), by norm_num⟩
  | 3 => ⟨((-146945591/2305843009213693952), (-1643371195/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 4 => ⟨((929242759/9223372036854775808), (430165879/9223372036854775808)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-898792023/73786976294838206464), (643015853/73786976294838206464)), (31/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-930029/4611686018427387904), (-1066086515/590295810358705651712)), (9/147573952589676412928), by norm_num⟩
  | 7 => ⟨((442422831/2361183241434822606848), (22872679/295147905179352825856)), (39/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-619877099/37778931862957161709568), (502990365/37778931862957161709568)), (39/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-238826349/604462909807314587353088), (-154287459/75557863725914323419136)), (37/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((902842443/4835703278458516698824704), (272376345/4835703278458516698824704)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-945052561/77371252455336267181195264), (973218903/77371252455336267181195264)), (119/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-75922171/154742504910672534362390528), (-222518653/154742504910672534362390528)), (101/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((299/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((61235200/892827049), (-45841920/892827049)), 0, by norm_num⟩
  | 1 => ⟨((-824134044876800/797140139426048401), (2807139139584000/797140139426048401)), 0, by norm_num⟩
  | 2 => ⟨((-241678511/4398046511104), (-323925943/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((398715575/70368744177664), (512391875/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1296015991/4503599627370496), (92817189/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((336490165/36028797018963968), (-291637851/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-259339939/2305843009213693952), (149116707/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-86927555/9223372036854775808), (-761071671/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((503399547/590295810358705651712), (274764721/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-1556279527/37778931862957161709568), (56015589/9444732965739290427392)), (47/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((761873329/604462909807314587353088), (-762193259/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-209905169/19342813113834066795298816), (1462299655/19342813113834066795298816)), (89/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-485478471/309485009821345068724781056), (-888563293/309485009821345068724781056)), (87/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((299/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((299/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((299/32), (17907/2560)))⁻¹=value ((61235200/892827049), (-45841920/892827049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((61235200/892827049), (-45841920/892827049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-278718515/144115188075855872), (-144159363/72057594037927936)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((195302679/144115188075855872), (-306266713/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-319709139/2305843009213693952), (101806995/288230376151711744)), (21/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-835215909/18446744073709551616), (-1130437283/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | 4 => ⟨((917207903/73786976294838206464), (-76371481/73786976294838206464)), (15/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-58121923/73786976294838206464), (465663103/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-566932453/4722366482869645213696), (-887047355/4722366482869645213696)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((973538869/37778931862957161709568), (-71477939/75557863725914323419136)), (53/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-393254271/302231454903657293676544), (370175877/151115727451828646838272)), (55/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-726370359/4835703278458516698824704), (-1146895785/4835703278458516698824704)), (107/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((260520023/9671406556917033397649408), (-27969227/19342813113834066795298816)), (101/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-333788795/309485009821345068724781056), (1380913653/618970019642690137449562112)), (179/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-316349777/2475880078570760549798248448), (-879579137/4951760157141521099596496896)), (155/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((331/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67788800/1021851049), (-45841920/1021851049)), 0, by norm_num⟩
  | 1 => ⟨((-1246919888076800/1044179566342400401), (3107568746496000/1044179566342400401)), 0, by norm_num⟩
  | 2 => ⟨((-119390131/4398046511104), (-275981093/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1045829765/281474976710656), (125042809/35184372088832)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-914052313/4503599627370496), (-155554345/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1081855041/144115188075855872), (-490984601/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-795888649/4611686018427387904), (1297685321/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-10835337/18446744073709551616), (-1948676877/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((186342629/590295810358705651712), (1003079781/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-1511153721/75557863725914323419136), (-529679689/75557863725914323419136)), (5/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((248022119/302231454903657293676544), (-261234453/1208925819614629174706176)), (37/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-432759733/19342813113834066795298816), (989388983/38685626227668133590597632)), (33/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((208516267/1237940039285380274899124224), (-417855679/309485009821345068724781056)), (119/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((331/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((331/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((331/32), (17907/2560)))⁻¹=value ((67788800/1021851049), (-45841920/1021851049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((67788800/1021851049), (-45841920/1021851049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-502790737/2305843009213693952), (-52984541/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 1 => ⟨((795498887/9223372036854775808), (-23572955/288230376151711744)), (31/9223372036854775808), by norm_num⟩
  | 2 => ⟨((207393119/36893488147419103232), (1265427511/36893488147419103232)), (43/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-247505425/36893488147419103232), (-449472275/147573952589676412928)), (21/73786976294838206464), by norm_num⟩
  | 4 => ⟨((631048305/590295810358705651712), (-99725943/147573952589676412928)), (67/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-16786605/9444732965739290427392), (1760470861/9444732965739290427392)), (23/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-774962103/37778931862957161709568), (-251191357/18889465931478580854784)), (57/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((799636373/302231454903657293676544), (-374117207/302231454903657293676544)), (33/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-88053215/2417851639229258349412352), (776817713/2417851639229258349412352)), (69/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-1029171315/38685626227668133590597632), (-791853539/38685626227668133590597632)), (69/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((474081699/154742504910672534362390528), (-378240229/309485009821345068724781056)), (33/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-113073823/2475880078570760549798248448), (1513485551/4951760157141521099596496896)), (15/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-431518637/19807040628566084398385987584), (-340964205/19807040628566084398385987584)), (53/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((363/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((24780800/387994083), (-15280640/387994083)), 0, by norm_num⟩
  | 1 => ⟨((-63431681638400/50179802814336963), (378666483712000/150539408443010889)), 0, by norm_num⟩
  | 2 => ⟨((-161228891/17592186044416), (-462763389/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((665590849/281474976710656), (895001429/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1244145503/9007199254740992), (-15474717/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((791718371/144115188075855872), (-277946993/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((-360743865/2305843009213693952), (640910303/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((333428735/147573952589676412928), (-1109586583/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((358461645/4722366482869645213696), (1343997719/4722366482869645213696)), (11/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-606609491/75557863725914323419136), (-286889069/37778931862957161709568)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((981456849/2417851639229258349412352), (204097959/2417851639229258349412352)), (1/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-565782511/38685626227668133590597632), (409885759/77371252455336267181195264)), (27/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((898066057/2475880078570760549798248448), (-1131907355/2475880078570760549798248448)), (45/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((363/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((363/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((363/32), (17907/2560)))⁻¹=value ((24780800/387994083), (-15280640/387994083)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((24780800/387994083), (-15280640/387994083))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-580579249/36893488147419103232), (208537845/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 1 => ⟨((395324061/147573952589676412928), (-168062695/18446744073709551616)), (55/147573952589676412928), by norm_num⟩
  | 2 => ⟨((266184053/147573952589676412928), (42666933/18446744073709551616)), (5/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-769244573/1180591620717411303424), (73994161/2361183241434822606848)), (41/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((292100663/4722366482869645213696), (-935924303/9444732965739290427392)), (17/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((544284775/75557863725914323419136), (308985887/18889465931478580854784)), (3/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-1442263867/604462909807314587353088), (-31882915/75557863725914323419136)), (123/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((990051159/4835703278458516698824704), (-1048238241/4835703278458516698824704)), (145/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((311720859/38685626227668133590597632), (1273086353/38685626227668133590597632)), (157/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1055538791/309485009821345068724781056), (-178237459/154742504910672534362390528)), (5/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((345558105/1237940039285380274899124224), (-141803329/618970019642690137449562112)), (39/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((23360867/4951760157141521099596496896), (1352139409/39614081257132168796771975168)), (9/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-229144929/79228162514264337593543950336), (-24532129/19807040628566084398385987584)), (259/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((395/32), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80896000/1319220649), (-45841920/1319220649)), 0, by norm_num⟩
  | 1 => ⟨((-2221340593356800/1740343120747981201), (3708427960320000/1740343120747981201)), 0, by norm_num⟩
  | 2 => ⟨((580437/274877906944), (-1539490999/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((409745565/281474976710656), (382776295/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-827654453/9007199254740992), (-523298285/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1102989803/288230376151711744), (13315343/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-555898313/4611686018427387904), (560992291/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((97364965/36893488147419103232), (-1168555685/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-57262011/4722366482869645213696), (1579582991/9444732965739290427392)), (1/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-382932647/151115727451828646838272), (-403365265/75557863725914323419136)), (13/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((206060437/1208925819614629174706176), (578607137/4835703278458516698824704)), (41/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1130392525/154742504910672534362390528), (-27356087/38685626227668133590597632)), (1/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((584954191/2475880078570760549798248448), (-521124307/4951760157141521099596496896)), (99/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((395/32), (17907/2560)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((395/32), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((395/32), (17907/2560)))⁻¹=value ((80896000/1319220649), (-45841920/1319220649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((80896000/1319220649), (-45841920/1319220649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-907366361/1180591620717411303424), (131849801/147573952589676412928)), (37/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-85168095/590295810358705651712), (-1635147073/2361183241434822606848)), (45/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((244898315/1180591620717411303424), (57779277/590295810358705651712)), (69/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-886428233/18889465931478580854784), (475380747/18889465931478580854784)), (73/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((102084615/75557863725914323419136), (-1482892933/151115727451828646838272)), (63/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((172153207/151115727451828646838272), (651061575/604462909807314587353088)), (23/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-64864789/302231454903657293676544), (6619831/151115727451828646838272)), (15/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((104851131/9671406556917033397649408), (-246419163/9671406556917033397649408)), (145/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((540963481/309485009821345068724781056), (837946341/309485009821345068724781056)), (161/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-1732147371/4951760157141521099596496896), (-23569327/4951760157141521099596496896)), (335/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((197715079/9903520314283042199192993792), (-587874101/19807040628566084398385987584)), (83/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((437007299/316912650057057350374175801344), (252420783/79228162514264337593543950336)), (313/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-806295499/2535301200456458802993406410752), (-249336063/5070602400912917605986812821504)), (569/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73174195/8796093022208), (1925639831/8796093022208)), (1819/8796093022208), by norm_num⟩
  | 1 => ⟨((-734011713/4398046511104), (912978663/4398046511104)), (1911/4398046511104), by norm_num⟩
  | 2 => ⟨((-672295261/4398046511104), (363921131/8796093022208)), (4131/8796093022208), by norm_num⟩
  | 3 => ⟨((-506167363/8796093022208), (-372098787/17592186044416)), (3045/8796093022208), by norm_num⟩
  | 4 => ⟨((-708684483/70368744177664), (-497906413/35184372088832)), (13701/70368744177664), by norm_num⟩
  | 5 => ⟨((-42994021/281474976710656), (-1079897423/281474976710656)), (25033/281474976710656), by norm_num⟩
  | 6 => ⟨((190338119/562949953421312), (-677933981/1125899906842624)), (77191/2251799813685248), by norm_num⟩
  | 7 => ⟨((201196669/2251799813685248), (-484305599/9007199254740992)), (103181/9007199254740992), by norm_num⟩
  | 8 => ⟨((1954295187/144115188075855872), (-126374783/144115188075855872)), (487913/144115188075855872), by norm_num⟩
  | 9 => ⟨((843297943/576460752303423488), (326281917/576460752303423488)), (129525/144115188075855872), by norm_num⟩
  | 10 => ⟨((1095598167/9223372036854775808), (261584055/2305843009213693952)), (2001185/9223372036854775808), by norm_num⟩
  | 11 => ⟨((506396331/73786976294838206464), (528168947/36893488147419103232)), (887547/18446744073709551616), by norm_num⟩
  | 12 => ⟨((182719963/1180591620717411303424), (838077841/590295810358705651712)), (5833645/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73174195/8796093022208), (1925639831/8796093022208)), (455/2199023255552), by norm_num⟩
  | 1 => ⟨((-734011713/4398046511104), (912978663/4398046511104)), (239/549755813888), by norm_num⟩
  | 2 => ⟨((-672295261/4398046511104), (363921131/8796093022208)), (1033/2199023255552), by norm_num⟩
  | 3 => ⟨((-506167363/8796093022208), (-372098787/17592186044416)), (6091/17592186044416), by norm_num⟩
  | 4 => ⟨((-708684483/70368744177664), (-497906413/35184372088832)), (1713/8796093022208), by norm_num⟩
  | 5 => ⟨((-42994021/281474976710656), (-1079897423/281474976710656)), (25045/281474976710656), by norm_num⟩
  | 6 => ⟨((190338119/562949953421312), (-677933981/1125899906842624)), (38641/1125899906842624), by norm_num⟩
  | 7 => ⟨((201196669/2251799813685248), (-484305599/9007199254740992)), (51771/4503599627370496), by norm_num⟩
  | 8 => ⟨((1954295187/144115188075855872), (-126374783/144115188075855872)), (246839/72057594037927936), by norm_num⟩
  | 9 => ⟨((843297943/576460752303423488), (326281917/576460752303423488)), (541159/576460752303423488), by norm_num⟩
  | 10 => ⟨((1095598167/9223372036854775808), (261584055/2305843009213693952)), (296265/1152921504606846976), by norm_num⟩
  | 11 => ⟨((506396331/73786976294838206464), (528168947/36893488147419103232)), (1625417/18446744073709551616), by norm_num⟩
  | 12 => ⟨((182719963/1180591620717411303424), (838077841/590295810358705651712)), (58890955/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile041Gamma
