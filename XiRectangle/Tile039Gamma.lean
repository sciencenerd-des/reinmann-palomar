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
namespace Reinmann.XiRectangle.Tile039Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((17/32), (7191/512))
  have he : value ((17/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((81/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((849/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((4636672/78745179), (-818176/26248393)), 0, by norm_num⟩
  | 1 => ⟨((-7737009766400/6200803215742041), (3793613750272/2066934405247347)), 0, by norm_num⟩
  | 2 => ⟨((279341/34359738368), (-1292706483/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((509966033/562949953421312), (644601637/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1123407087/18014398509481984), (-960238963/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((192159157/72057594037927936), (344377443/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((-405008461/4611686018427387904), (221119823/9223372036854775808)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((163211921/73786976294838206464), (-612297915/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-309685133/9444732965739290427392), (112805827/1180591620717411303424)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-158317675/302231454903657293676544), (-502327111/151115727451828646838272)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((650202405/9671406556917033397649408), (867538963/9671406556917033397649408)), (31/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1045229491/309485009821345068724781056), (-246522125/154742504910672534362390528)), (23/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1230618013/9903520314283042199192993792), (-56782769/9903520314283042199192993792)), (67/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((849/64), (7191/1024)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((849/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((849/64), (7191/1024)))⁻¹=value ((4636672/78745179), (-818176/26248393)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((4636672/78745179), (-818176/26248393))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((363555311/134217728), (65346423/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((2318336/78745179), (-409088/26248393)), 0, by norm_num⟩
  | 2 => ⟨((-1934252441600/6200803215742041), (948403437568/2066934405247347)), 0, by norm_num⟩
  | 3 => ⟨((190696789/140737488355328), (-430902161/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((509966033/4503599627370496), (644601637/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-449362835/72057594037927936), (-384095585/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((1024848837/4611686018427387904), (114792481/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-925733625/147573952589676412928), (252708369/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((163211921/1180591620717411303424), (-612297915/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-137637837/75557863725914323419136), (401087385/75557863725914323419136)), (13/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-31663535/1208925819614629174706176), (-1607446755/9671406556917033397649408)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((118218619/38685626227668133590597632), (157734357/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-1393639321/9903520314283042199192993792), (-657392333/9903520314283042199192993792)), (31/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-28089/1106944), (153/16384)), 0, by norm_num⟩
  | 45 => ⟨((293285804101/13058042757120), (-2456721/192937984)), 0, by norm_num⟩
  | 44 => ⟨((-617084415446863/29417158723239936), (6086469677717/505775348776960)), 0, by norm_num⟩
  | 43 => ⟨((370381019/17179869184), (-387010111/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-12106623/536870912), (391262703/34359738368)), (1/34359738368), by norm_num⟩
  | 41 => ⟨((399365949/17179869184), (-406939333/34359738368)), (1/34359738368), by norm_num⟩
  | 40 => ⟨((-816888269/34359738368), (52513971/4294967296)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((418117603/17179869184), (-430331817/34359738368)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-429120329/17179869184), (110142463/8589934592)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((881945779/34359738368), (-451977793/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-453392779/17179869184), (116082915/8589934592)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((932878111/34359738368), (-238672595/17179869184)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-480249665/17179869184), (491021303/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((247460227/8589934592), (-126370397/8589934592)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-510523147/17179869184), (260415479/17179869184)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((527139591/17179869184), (-16785947/1073741824)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1089741963/34359738368), (34657831/2147483648)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1127670499/34359738368), (-573059405/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-292083171/8589934592), (296436917/17179869184)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((1212034549/34359738368), (-614106877/34359738368)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-629564681/17179869184), (636916485/34359738368)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((163753463/4294967296), (-661484705/34359738368)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1365209297/34359738368), (688022851/34359738368)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((712618977/17179869184), (-358388795/17179869184)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-745390407/17179869184), (93504817/4294967296)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((781316583/17179869184), (-391073997/17179869184)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-51304711/1073741824), (409756759/17179869184)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((432323079/8589934592), (-430312119/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-456669113/8589934592), (453036161/17179869184)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((967829319/17179869184), (-239145399/8589934592)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-514609345/8589934592), (126630781/4294967296)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((549450775/8589934592), (-538292013/17179869184)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-147334457/2147483648), (143576335/4294967296)), (3/17179869184), by norm_num⟩
  | 13 => ⟨((635448713/8589934592), (-19233535/536870912)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((-1378716653/17179869184), (662985115/17179869184)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((188305015/2147483648), (-359213555/8589934592)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-830057393/8589934592), (97995047/2147483648)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((924251091/8589934592), (-431304153/8589934592)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-4071851/33554432), (239683265/4294967296)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((1194881199/8589934592), (-67429203/1073741824)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-1399099623/8589934592), (616626273/8589934592)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((843225619/4294967296), (-179862655/2147483648)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-264990739/1073741824), (431571429/4294967296)), (1/4294967296), by norm_num⟩
  | 3 => ⟨((711691717/2147483648), (-538976661/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-269272343/536870912), (89604835/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1087122463/1073741824), (-133497983/536870912)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-535953/8388608), (522771383/1073741824)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-175/1024), (7191/16384)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-175/1024), (7191/16384)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-175/1024), (7191/16384))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((363555311/134217728), (65346423/134217728)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((849/64), (7191/1024))) (z:=((-175/1024), (7191/16384))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((363555311/134217728), (65346423/134217728))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((817/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((261382379/8388608), (846810225/33554432)), (3/33554432), by norm_num⟩
  | 1 => ⟨((987643073/536870912), (67438241/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((46606572046336/6200803215742041), (-8527628665472/2066934405247347)), 0, by norm_num⟩
  | 3 => ⟨((-231630989/4398046511104), (726537307/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((126951033/1125899906842624), (-1884759053/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((520313533/36028797018963968), (1127386517/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-727256553/1152921504606846976), (-270412783/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((701344609/36893488147419103232), (99602861/36893488147419103232)), (55/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1088945547/2361183241434822606848), (202891423/1180591620717411303424)), (73/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((649127965/75557863725914323419136), (-744808505/75557863725914323419136)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-377114017/4835703278458516698824704), (105333833/302231454903657293676544)), (545/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-420661449/154742504910672534362390528), (-371130225/38685626227668133590597632)), (187/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((978909127/4951760157141521099596496896), (1005598001/4951760157141521099596496896)), (499/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-849/64), (-7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((150102251/8388608), (611175537/33554432)), (3/33554432), by norm_num⟩
  | 1 => ⟨((719207617/536870912), (67438241/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((46606572046336/6200803215742041), (-8527628665472/2066934405247347)), 0, by norm_num⟩
  | 3 => ⟨((-231630989/4398046511104), (726537307/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((126951033/1125899906842624), (-1884759053/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((520313533/36028797018963968), (1127386517/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-727256553/1152921504606846976), (-270412783/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((701344609/36893488147419103232), (99602861/36893488147419103232)), (55/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1088945547/2361183241434822606848), (202891423/1180591620717411303424)), (73/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((649127965/75557863725914323419136), (-744808505/75557863725914323419136)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-377114017/4835703278458516698824704), (105333833/302231454903657293676544)), (545/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-420661449/154742504910672534362390528), (-371130225/38685626227668133590597632)), (187/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((978909127/4951760157141521099596496896), (1005598001/4951760157141521099596496896)), (499/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((631243465/33554432), (611175537/33554432)), (1/8388608), by norm_num⟩
  | 1 => ⟨((719207617/536870912), (67438241/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((46606572046336/6200803215742041), (-8527628665472/2066934405247347)), 0, by norm_num⟩
  | 3 => ⟨((-231630989/4398046511104), (726537307/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((126951033/1125899906842624), (-1884759053/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((520313533/36028797018963968), (1127386517/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-727256553/1152921504606846976), (-270412783/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((701344609/36893488147419103232), (99602861/36893488147419103232)), (55/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1088945547/2361183241434822606848), (202891423/1180591620717411303424)), (73/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((649127965/75557863725914323419136), (-744808505/75557863725914323419136)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-377114017/4835703278458516698824704), (105333833/302231454903657293676544)), (545/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-420661449/154742504910672534362390528), (-371130225/38685626227668133590597632)), (187/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((978909127/4951760157141521099596496896), (1005598001/4951760157141521099596496896)), (499/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15474019532800/6200803215742041), (-7587227500544/2066934405247347)), 0, by norm_num⟩
  | 1 => ⟨((-279341/8589934592), (1292706483/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-382474525/70368744177664), (-120862807/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1123407087/2251799813685248), (960238963/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-960795785/36028797018963968), (-107617951/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((1215025383/1152921504606846976), (-165839867/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-142810431/4611686018427387904), (535760675/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((309685133/590295810358705651712), (-112805827/73786976294838206464)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((22263423/2361183241434822606848), (35319875/590295810358705651712)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-406376503/302231454903657293676544), (-135552963/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((718595275/9671406556917033397649408), (677935845/19342813113834066795298816)), (35/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-461481755/154742504910672534362390528), (85174153/618970019642690137449562112)), (53/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((918986589/9903520314283042199192993792), (-33883267/618970019642690137449562112)), (5/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((279341/8589934592), (-1292706483/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((382474525/35184372088832), (120862807/4398046511104)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-210638829/140737488355328), (-720179223/562949953421312)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((960795785/9007199254740992), (107617951/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-1518781729/288230376151711744), (414599667/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 5 => ⟨((428431293/2305843009213693952), (-803641013/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-541948983/147573952589676412928), (1579281577/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-22263423/295147905179352825856), (-35319875/73786976294838206464)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((228586783/18889465931478580854784), (1219976667/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-449122047/604462909807314587353088), (-423709903/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((634537413/19342813113834066795298816), (-29278615/19342813113834066795298816)), (25/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-344619971/309485009821345068724781056), (101649801/154742504910672534362390528)), (5/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((32561555/1237940039285380274899124224), (-423969763/9903520314283042199192993792)), (31/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-509966033/70368744177664), (-644601637/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((70212943/35184372088832), (240059741/140737488355328)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-480397893/2251799813685248), (-107617951/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((1012521153/72057594037927936), (-138199889/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((-714052155/1152921504606846976), (167425211/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((541948983/36893488147419103232), (-1579281577/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 6 => ⟨((51947987/147573952589676412928), (659304333/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-304782377/4722366482869645213696), (-406658889/4722366482869645213696)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1347366141/302231454903657293676544), (635564855/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-1057562355/4835703278458516698824704), (12199423/1208925819614629174706176)), (17/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((39487705/4835703278458516698824704), (-745431873/154742504910672534362390528)), (29/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-32561555/154742504910672534362390528), (423969763/1237940039285380274899124224)), (3/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((42459069/39614081257132168796771975168), (-1323354521/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1123407087/1125899906842624), (-960238963/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((480397893/2251799813685248), (107617951/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 2 => ⟨((-759390865/36028797018963968), (103649917/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 3 => ⟨((714052155/576460752303423488), (-167425211/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((-338718115/9223372036854775808), (493525493/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-155843961/147573952589676412928), (-247239125/36893488147419103232)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((66671145/295147905179352825856), (11119579/36893488147419103232)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1347366141/75557863725914323419136), (-635564855/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((594878825/604462909807314587353088), (-54897403/1208925819614629174706176)), (9/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-197438525/4835703278458516698824704), (465894921/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((358177105/309485009821345068724781056), (-72869803/38685626227668133590597632)), (29/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-127377207/19807040628566084398385987584), (992515891/9903520314283042199192993792)), (25/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-579991961/316912650057057350374175801344), (-1289098813/316912650057057350374175801344)), (21/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-192159157/2251799813685248), (-344377443/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((151878173/9007199254740992), (-331679735/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 2 => ⟨((-428431293/288230376151711744), (401820507/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 3 => ⟨((541948983/9223372036854775808), (-789640789/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((155843961/73786976294838206464), (247239125/18446744073709551616)), (11/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-40002687/73786976294838206464), (-213495917/295147905179352825856)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((943156299/18889465931478580854784), (444895399/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-118975765/37778931862957161709568), (87835845/604462909807314587353088)), (29/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((355389345/2417851639229258349412352), (-419305429/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-358177105/77371252455336267181195264), (72869803/9671406556917033397649408)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((8757183/309485009821345068724781056), (-136470935/309485009821345068724781056)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((347995177/39614081257132168796771975168), (96682411/4951760157141521099596496896)), (3/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-252732037/316912650057057350374175801344), (-786434143/1267650600228229401496703205376)), (41/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-405008461/72057594037927936), (221119823/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 1 => ⟨((142810431/144115188075855872), (-133940169/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 2 => ⟨((-541948983/9223372036854775808), (1579281579/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-51947987/18446744073709551616), (-1318608667/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 4 => ⟨((66671145/73786976294838206464), (11119579/9223372036854775808)), (13/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-943156299/9444732965739290427392), (-444895399/9444732965739290427392)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((555220237/75557863725914323419136), (-6404697/18889465931478580854784)), (5/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-947704921/2417851639229258349412352), (559073905/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((268632829/19342813113834066795298816), (-218609409/9671406556917033397649408)), (23/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-116762439/1237940039285380274899124224), (1819612467/1237940039285380274899124224)), (45/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-637991157/19807040628566084398385987584), (-1418008695/19807040628566084398385987584)), (43/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((1010928149/316912650057057350374175801344), (786434143/316912650057057350374175801344)), (41/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-1008468117/5070602400912917605986812821504), (-88773871/2535301200456458802993406410752)), (19/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-163211921/576460752303423488), (612297915/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 1 => ⟨((309685133/9223372036854775808), (-112805827/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 2 => ⟨((22263423/9223372036854775808), (1130236001/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-609564755/590295810358705651712), (-813317779/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 4 => ⟨((1347366141/9444732965739290427392), (635564855/9444732965739290427392)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-118975765/9444732965739290427392), (21958961/37778931862957161709568)), (41/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((947704921/1208925819614629174706176), (-559073905/1208925819614629174706176)), (13/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-614017895/19342813113834066795298816), (999357299/19342813113834066795298816)), (29/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((75061569/309485009821345068724781056), (-146218859/38685626227668133590597632)), (33/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((455707969/4951760157141521099596496896), (506431677/2475880078570760549798248448)), (17/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-49643793/4951760157141521099596496896), (-617912541/79228162514264337593543950336)), (17/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((864401243/1267650600228229401496703205376), (304367557/2535301200456458802993406410752)), (33/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-1409579683/40564819207303340847894502572032), (227784061/20282409603651670423947251286016)), (63/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-309685133/36893488147419103232), (112805827/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-22263423/18446744073709551616), (-35319875/4611686018427387904)), (23/147573952589676412928), by norm_num⟩
  | 2 => ⟨((914347133/1180591620717411303424), (1219976669/1180591620717411303424)), (33/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-673683071/4722366482869645213696), (-635564855/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((594878825/37778931862957161709568), (-54897403/75557863725914323419136)), (15/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-710778691/604462909807314587353088), (419305429/604462909807314587353088)), (3/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((268632829/4835703278458516698824704), (-218609409/2417851639229258349412352)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-75061569/154742504910672534362390528), (146218859/19342813113834066795298816)), (19/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-512671465/2475880078570760549798248448), (-569735637/1237940039285380274899124224)), (45/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((248218965/9903520314283042199192993792), (772390677/39614081257132168796771975168)), (3/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-1188551709/633825300114114700748351602688), (-26156587/79228162514264337593543950336)), (51/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((528592381/5070602400912917605986812821504), (-85419023/2535301200456458802993406410752)), (51/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-687985475/162259276829213363391578010288128), (707620813/162259276829213363391578010288128)), (25/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((158317675/590295810358705651712), (502327111/295147905179352825856)), (21/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-406376503/1180591620717411303424), (-1084423705/2361183241434822606848)), (37/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((898244095/9444732965739290427392), (26481869/590295810358705651712)), (15/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-264390589/18889465931478580854784), (12199423/18889465931478580854784)), (17/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((789754101/604462909807314587353088), (-465894921/604462909807314587353088)), (1/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-716354211/9671406556917033397649408), (1165916849/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((14595305/19342813113834066795298816), (-454903117/38685626227668133590597632)), (37/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((455707969/1237940039285380274899124224), (506431677/618970019642690137449562112)), (47/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-248218965/4951760157141521099596496896), (-772390677/19807040628566084398385987584)), (29/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((1320613011/316912650057057350374175801344), (58125749/79228162514264337593543950336)), (33/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-646057355/2535301200456458802993406410752), (417604111/5070602400912917605986812821504)), (9/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((458656983/40564819207303340847894502572032), (-943494417/81129638414606681695789005144064)), (75/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-344456735/1298074214633706907132624082305024), (294517895/324518553658426726783156020576256)), (19/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((650202405/9444732965739290427392), (867538963/9444732965739290427392)), (31/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-1437190551/37778931862957161709568), (-338967923/18889465931478580854784)), (29/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((317268707/37778931862957161709568), (-29278615/75557863725914323419136)), (13/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-1263606561/1208925819614629174706176), (372715937/604462909807314587353088)), (1/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((716354211/9671406556917033397649408), (-1165916849/9671406556917033397649408)), (63/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-8757183/9671406556917033397649408), (1091767481/77371252455336267181195264)), (55/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-637991157/1237940039285380274899124224), (-177251087/154742504910672534362390528)), (83/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((49643793/618970019642690137449562112), (308956271/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-1188551709/158456325028528675187087900672), (-26156587/19807040628566084398385987584)), (9/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((646057355/1267650600228229401496703205376), (-26100257/158456325028528675187087900672)), (43/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-252261341/10141204801825835211973625643008), (518921929/20282409603651670423947251286016)), (97/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((206674041/324518553658426726783156020576256), (-176710737/81129638414606681695789005144064)), (53/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((289322999/10384593717069655257060992658440192), (1409831829/10384593717069655257060992658440192)), (111/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1159168/236235537), (-204544/78745179)), 0, by norm_num⟩
  | 1 => ⟨((-1934252441600/18602409647226123), (948403437568/6200803215742041)), 0, by norm_num⟩
  | 2 => ⟨((190696789/281474976710656), (-430902161/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((339977355/4503599627370496), (859468849/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-374469029/72057594037927936), (-640159309/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((1024848837/4611686018427387904), (114792481/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-1080022563/147573952589676412928), (294826431/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((870463579/4722366482869645213696), (-204099305/1180591620717411303424)), (13/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-412913511/151115727451828646838272), (1203262155/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-211090233/4835703278458516698824704), (-1339538963/4835703278458516698824704)), (29/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((216734135/38685626227668133590597632), (1156718617/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-1393639321/4951760157141521099596496896), (-657392333/4951760157141521099596496896)), (31/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1640824017/158456325028528675187087900672), (-75710359/158456325028528675187087900672)), (45/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((631408111/33554432), (305544189/16777216)), (5/33554432), by norm_num⟩
  | 1 => ⟨((359575897/268435456), (269917191/1073741824)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((129139235/17179869184), (-283939321/68719476736)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-57824745/1099511627776), (728215957/8796093022208)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((60549977/562949953421312), (-944880149/562949953421312)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((528320165/36028797018963968), (564590075/18014398509481984)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-735694229/1152921504606846976), (-538522235/1152921504606846976)), (43/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1416290211/73786976294838206464), (186449515/73786976294838206464)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-1095397321/2361183241434822606848), (424583817/2361183241434822606848)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((40364355/4722366482869645213696), (-765738801/75557863725914323419136)), (203/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-175011125/2417851639229258349412352), (1721488785/4835703278458516698824704)), (547/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-232106339/77371252455336267181195264), (-752532205/77371252455336267181195264)), (751/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((515092439/2475880078570760549798248448), (250808013/1237940039285380274899124224)), (501/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-203409909/2251799813685248), (1838515887/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-543963769/18014398509481984), (-85946885/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((599150447/144115188075855872), (512127447/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-341616279/1152921504606846976), (-306113283/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1080022563/73786976294838206464), (-147413215/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-304662253/590295810358705651712), (285739027/590295810358705651712)), (5/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((385385943/37778931862957161709568), (-1123044677/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((253308279/1208925819614629174706176), (401861689/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-650202405/19342813113834066795298816), (-867538963/19342813113834066795298816)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1277502711/618970019642690137449562112), (75326205/77371252455336267181195264)), (3/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-1804906419/19807040628566084398385987584), (41640697/9903520314283042199192993792)), (9/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((490126181/158456325028528675187087900672), (-578274423/316912650057057350374175801344)), (29/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-370478137/5070602400912917605986812821504), (1205958437/10141204801825835211973625643008)), (45/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((157852027/8388608), (611088405/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((359575889/268435456), (269917109/1073741824)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1033114451/137438953472), (-283939077/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-231300283/4398046511104), (728215373/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((60558217/562949953421312), (-1889764797/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((264150785/18014398509481984), (564598795/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-183920617/288230376151711744), (-134639127/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((177038209/9223372036854775808), (93273813/36893488147419103232)), (113/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1095476691/2361183241434822606848), (106119479/590295810358705651712)), (37/590295810358705651712), by norm_num⟩
  | 9 => ⟨((645985625/75557863725914323419136), (-95708155/9444732965739290427392)), (51/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-350462901/4835703278458516698824704), (1721509117/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-463734039/154742504910672534362390528), (-1505346771/154742504910672534362390528)), (47/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1029823083/4951760157141521099596496896), (1003820899/4951760157141521099596496896)), (1003/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-228247789/288230376151711744), (-780384681/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((390418605/2305843009213693952), (43730469/1152921504606846976)), (9/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-1234311501/73786976294838206464), (84236123/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((580309053/590295810358705651712), (-544264813/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-137637837/4722366482869645213696), (401087385/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-253308279/302231454903657293676544), (-401861689/75557863725914323419136)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((866936539/4835703278458516698824704), (578359309/2417851639229258349412352)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-273750581/19342813113834066795298816), (-516522549/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((1933828307/2475880078570760549798248448), (-89230065/2475880078570760549798248448)), (15/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1283663807/39614081257132168796771975168), (378632063/19807040628566084398385987584)), (27/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((582179929/633825300114114700748351602688), (-236884693/158456325028528675187087900672)), (25/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-51759627/10141204801825835211973625643008), (806616089/10141204801825835211973625643008)), (21/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-235679273/162259276829213363391578010288128), (-1047648559/324518553658426726783156020576256)), (35/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((157852027/8388608), (611088405/33554432)), (7/33554432), by norm_num⟩
  | 1 => ⟨((359575889/268435456), (269917109/1073741824)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1033114449/137438953472), (-567878153/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-462600557/8796093022208), (728215365/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((121116401/1125899906842624), (-1889764701/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((132075385/9007199254740992), (564598699/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-735682261/1152921504606846976), (-67319529/144115188075855872)), (45/1152921504606846976), by norm_num⟩
  | 7 => ⟨((354076157/18446744073709551616), (186547133/73786976294838206464)), (57/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1095474847/2361183241434822606848), (424477831/2361183241434822606848)), (149/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((645983177/75557863725914323419136), (-191415949/18889465931478580854784)), (205/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-350458459/4835703278458516698824704), (26898467/75557863725914323419136)), (549/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-463734829/154742504910672534362390528), (-1505334463/154742504910672534362390528)), (753/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1029815891/4951760157141521099596496896), (1003804913/4951760157141521099596496896)), (251/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((61715575/18446744073709551616), (-134777797/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-43523179/73786976294838206464), (40819861/73786976294838206464)), (11/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((330330809/9444732965739290427392), (-240652431/2361183241434822606848)), (13/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((253308279/151115727451828646838272), (401861689/37778931862957161709568)), (11/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-650202405/1208925819614629174706176), (-216884741/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((1149752441/19342813113834066795298816), (542348677/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-169209977/38685626227668133590597632), (62461045/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((288824357/1237940039285380274899124224), (-681537713/4951760157141521099596496896)), (27/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-654952421/79228162514264337593543950336), (532990559/39614081257132168796771975168)), (29/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((71169487/1267650600228229401496703205376), (-1109097123/1267650600228229401496703205376)), (29/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((24304425/1267650600228229401496703205376), (432155031/10141204801825835211973625643008)), (27/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-616184777/324518553658426726783156020576256), (-479350335/324518553658426726783156020576256)), (13/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((1229370657/10384593717069655257060992658440192), (13527447/649037107316853453566312041152512)), (47/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((157852027/8388608), (611088405/33554432)), (1/4194304), by norm_num⟩
  | 1 => ⟨((359575889/268435456), (269917109/1073741824)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1033114449/137438953472), (-567878153/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-462600557/8796093022208), (728215365/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((7569775/70368744177664), (-944882351/562949953421312)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((264150771/18014398509481984), (1129197399/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-367841133/576460752303423488), (-67319529/144115188075855872)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1416304645/73786976294838206464), (186547123/73786976294838206464)), (115/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1095474867/2361183241434822606848), (424477863/2361183241434822606848)), (75/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((645983181/75557863725914323419136), (-382831931/37778931862957161709568)), (103/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-175229183/2417851639229258349412352), (860751047/2417851639229258349412352)), (275/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-463735123/154742504910672534362390528), (-376333673/38685626227668133590597632)), (377/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1029816477/4951760157141521099596496896), (125475627/618970019642690137449562112)), (1005/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-533867973/75557863725914323419136), (1555732887/75557863725914323419136)), (25/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-153520169/151115727451828646838272), (-974210155/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((24628879/37778931862957161709568), (1051562381/1208925819614629174706176)), (29/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-580683051/4835703278458516698824704), (-273913473/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((2051030023/154742504910672534362390528), (-94637947/154742504910672534362390528)), (53/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-612657727/618970019642690137449562112), (722843029/1237940039285380274899124224)), (21/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((57887209/1237940039285380274899124224), (-753724023/9903520314283042199192993792)), (29/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-32349767/79228162514264337593543950336), (31508441/4951760157141521099596496896)), (67/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-110474659/633825300114114700748351602688), (-491085263/1267650600228229401496703205376)), (5/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((855812189/40564819207303340847894502572032), (665764355/40564819207303340847894502572032)), (21/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((-1024475547/649037107316853453566312041152512), (-22545745/81129638414606681695789005144064)), (45/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((911243431/10384593717069655257060992658440192), (-294508685/10384593717069655257060992658440192)), (45/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-593011049/166153499473114484112975882535043072), (609935785/166153499473114484112975882535043072)), (11/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((157852027/8388608), (611088405/33554432)), (9/33554432), by norm_num⟩
  | 1 => ⟨((359575889/268435456), (269917109/1073741824)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1033114449/137438953472), (-567878153/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-462600557/8796093022208), (728215365/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((7569775/70368744177664), (-944882351/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((264150771/18014398509481984), (1129197399/36028797018963968)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-367841133/576460752303423488), (-67319529/144115188075855872)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1416304645/73786976294838206464), (186547123/73786976294838206464)), (29/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1095474867/2361183241434822606848), (212238931/1180591620717411303424)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((645983183/75557863725914323419136), (-765663861/75557863725914323419136)), (207/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-175229187/2417851639229258349412352), (1721502093/4835703278458516698824704)), (551/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-463735109/154742504910672534362390528), (-188166837/19342813113834066795298816)), (755/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1029816459/4951760157141521099596496896), (501902517/2475880078570760549798248448)), (503/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-319175837/2417851639229258349412352), (-851727009/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((705498001/9671406556917033397649408), (665579639/19342813113834066795298816)), (29/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-1245944393/77371252455336267181195264), (57489953/77371252455336267181195264)), (13/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((77535987/38685626227668133590597632), (-365922735/309485009821345068724781056)), (63/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-703297783/4951760157141521099596496896), (572333297/2475880078570760549798248448)), (63/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((68780581/39614081257132168796771975168), (-1071868689/39614081257132168796771975168)), (55/39614081257132168796771975168), by norm_num⟩
  | 6 => ⟨((626362991/633825300114114700748351602688), (87010235/39614081257132168796771975168)), (41/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((-389911795/2535301200456458802993406410752), (-606650333/5070602400912917605986812821504)), (7/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((583444453/40564819207303340847894502572032), (205438811/81129638414606681695789005144064)), (9/10141204801825835211973625643008), by norm_num⟩
  | 9 => ⟨((-1268564345/1298074214633706907132624082305024), (6406137/20282409603651670423947251286016)), (43/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((990654283/20769187434139310514121985316880384), (-1018927889/20769187434139310514121985316880384)), (3/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((-202907155/166153499473114484112975882535043072), (346979937/83076749736557242056487941267521536)), (105/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-284049735/5316911983139663491615228241121378304), (-692067963/2658455991569831745807614120560689152)), (55/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((157852027/8388608), (611088405/33554432)), (5/16777216), by norm_num⟩
  | 1 => ⟨((359575889/268435456), (269917109/1073741824)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1033114449/137438953472), (-567878153/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-462600557/8796093022208), (728215365/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((7569775/70368744177664), (-944882351/562949953421312)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((264150771/18014398509481984), (1129197399/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-367841133/576460752303423488), (-67319529/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((1416304645/73786976294838206464), (186547123/73786976294838206464)), (117/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1095474867/2361183241434822606848), (212238931/1180591620717411303424)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((645983183/75557863725914323419136), (-765663861/75557863725914323419136)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-175229187/2417851639229258349412352), (1721502093/4835703278458516698824704)), (69/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-463735109/154742504910672534362390528), (-1505334695/154742504910672534362390528)), (189/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1029816459/4951760157141521099596496896), (1003805033/4951760157141521099596496896)), (1007/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((501109296142595/4194304), (-92827796957097/1048576)), (626035235/8388608), by norm_num⟩
  | 1 => ⟨((729168303/4), (-354205757/4)), 121, by norm_num⟩
  | 2 => ⟨((1070037377/8), (-150220933/4)), (197/2), by norm_num⟩
  | 3 => ⟨((254160287/4), (-103877095/16)), (861/16), by norm_num⟩
  | 4 => ⟨((1415019347/64), (90633193/64)), (1419/64), by norm_num⟩
  | 5 => ⟨((771834739/128), (351749221/256)), (1885/256), by norm_num⟩
  | 6 => ⟨((344208697/256), (547983339/1024)), (2105/1024), by norm_num⟩
  | 7 => ⟨((1032613793/4096), (602997429/4096)), (2031/4096), by norm_num⟩
  | 8 => ⟨((663671967/16384), (529714455/16384)), (1729/16384), by norm_num⟩
  | 9 => ⟨((739940493/131072), (784016087/131072)), (1319/65536), by norm_num⟩
  | 10 => ⟨((179896601/262144), (504074609/524288)), (3651/1048576), by norm_num⟩
  | 11 => ⟨((608964337/8388608), (574704917/4194304)), (4631/8388608), by norm_num⟩
  | 12 => ⟨((441298409/67108864), (294746501/16777216)), (5429/67108864), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804243784021391/5070602400912917605986812821504), (-830678404349/10141204801825835211973625643008)), (388209/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1811530422821181/633825300114114700748351602688), (-1016960353327/633825300114114700748351602688)), (237875/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((963317399271145/19807040628566084398385987584), (-35838428895/1237940039285380274899124224)), (33535/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1928749921085061/2475880078570760549798248448), (-305224552507/618970019642690137449562112)), (571253/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1810454616152387/154742504910672534362390528), (-76473532953/9671406556917033397649408)), (286275/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((396601071229355/2417851639229258349412352), (-1149956619779/9671406556917033397649408)), (269073/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1291074202494755/604462909807314587353088), (-1009075036029/604462909807314587353088)), (59033/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1940333112428951/75557863725914323419136), (-822567523793/37778931862957161709568)), (770037/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1337012908875421/4722366482869645213696), (-619292987031/2361183241434822606848)), (579821/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1675834418984625/590295810358705651712), (-855393717947/295147905179352825856)), (400499/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1891623592371007/73786976294838206464), (-537537123899/18446744073709551616)), (1006897/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1899553899109843/9223372036854775808), (-1217532148635/4611686018427387904)), (1140583/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1671090738347313/1152921504606846976), (-1227706520879/576460752303423488)), (287611/288230376151711744), by norm_num⟩
  | 5 => ⟨((157796760971559/18014398509481984), (-1085803625549/72057594037927936)), (127231/18014398509481984), by norm_num⟩
  | 4 => ⟨((1593986003359663/36028797018963968), (-3304230009181/36028797018963968)), (1549479/36028797018963968), by norm_num⟩
  | 3 => ⟨((809179253763857/4503599627370496), (-2106768750633/4503599627370496)), (1977247/9007199254740992), by norm_num⟩
  | 2 => ⟨((77802986780093/140737488355328), (-4341089178801/2251799813685248)), (509797/562949953421312), by norm_num⟩
  | 1 => ⟨((327221197998461/281474976710656), (-6840081183539/1125899906842624)), (1609219/562949953421312), by norm_num⟩
  | 0 => ⟨((377668271198765/281474976710656), (-15052992749917/1125899906842624)), (222037/35184372088832), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((377668271198765/281474976710656), (-15052992749917/1125899906842624)), (847003936901795853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2026740177048841/1125899906842624), (-40394622745259/1125899906842624)), (2407089/140737488355328), by norm_num⟩
  | 2 => ⟨((911724922162901/281474976710656), (-36357319312751/281474976710656)), (17677513/281474976710656), by norm_num⟩
  | 3 => ⟨((92139682442187/8796093022208), (-58882452905475/70368744177664)), (29771273/70368744177664), by norm_num⟩
  | 4 => ⟨((959010659142561/8796093022208), (-154199441116347/8796093022208)), (84191965/8796093022208), by norm_num⟩
  | 5 => ⟨((49733771362773/4294967296), (-525371418065399/137438953472)), (166486113/68719476736), by norm_num⟩
  | 6 => ⟨((501109296142595/4194304), (-92827796957097/1048576)), (626035235/8388608), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((157852027/8388608), (611088405/33554432)), (5/16777216), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((16384/659137), (-818176/5932233)), 0, by norm_num⟩
  | 1 => ⟨((323834347520/35191388366289), (13404995584/3910154262921)), 0, by norm_num⟩
  | 2 => ⟨((-48210835/137438953472), (1301756805/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-20045625/549755813888), (-277491131/8796093022208)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((369951951/140737488355328), (-597402985/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((512019693/4503599627370496), (58448671/281474976710656)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1133659009/72057594037927936), (378979731/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-24089967/144115188075855872), (-663099665/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((1501602711/18446744073709551616), (51080105/18446744073709551616)), (1/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-354959551/295147905179352825856), (411663949/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-436568603/1180591620717411303424), (-359546675/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((570337383/37778931862957161709568), (-222972561/9444732965739290427392)), (21/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((870665091/604462909807314587353088), (806645223/604462909807314587353088)), (7/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((81/64), (7191/1024)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((81/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((81/64), (7191/1024)))⁻¹=value ((16384/659137), (-818176/5932233)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((16384/659137), (-818176/5932233))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((145/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((2375680/57092881), (-7363584/57092881)), 0, by norm_num⟩
  | 1 => ⟨((24289256931328/3259597060880161), (17493519237120/3259597060880161)), 0, by norm_num⟩
  | 2 => ⟨((-550992731/1099511627776), (101396963/274877906944)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-470138561/35184372088832), (-703531245/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1608315631/562949953421312), (-4174761/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-129539039/2251799813685248), (832512819/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-193186659/18014398509481984), (-544449981/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((819002551/1152921504606846976), (-19252601/36028797018963968)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((181521241/9223372036854775808), (131266991/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-1204386499/295147905179352825856), (3126605/36893488147419103232)), (23/295147905179352825856), by norm_num⟩
  | 10 => ⟨((375115457/4722366482869645213696), (-625508715/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((36435443/2361183241434822606848), (803492297/75557863725914323419136)), (45/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-608585125/604462909807314587353088), (233886031/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((145/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((145/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((145/64), (7191/1024)))⁻¹=value ((2375680/57092881), (-7363584/57092881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((2375680/57092881), (-7363584/57092881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-630488825856/37632030303697), (-3029529001984/338688272733273)), 0, by norm_num⟩
  | 1 => ⟨((481167553/274877906944), (-1065713285/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((661224203/4398046511104), (981162201/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-812781439/35184372088832), (148548983/17592186044416)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((-128507827/562949953421312), (-589053463/281474976710656)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((1542195541/9007199254740992), (25666479/1125899906842624)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-360912373/72057594037927936), (57714357/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-1011722287/1152921504606846976), (-710116097/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((1138560229/18446744073709551616), (-499527911/9223372036854775808)), (19/18446744073709551616), by norm_num⟩
  | 9 => ⟨((424713473/147573952589676412928), (405410739/73786976294838206464)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-530347467/1180591620717411303424), (265962039/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-1578713/4722366482869645213696), (-161704549/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((184906277/75557863725914323419136), (169436581/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((209/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((3424256/62892817), (-7363584/62892817)), 0, by norm_num⟩
  | 1 => ⟨((21248420085760/3955506430195489), (25214796693504/3955506430195489)), 0, by norm_num⟩
  | 2 => ⟨((-571099535/1099511627776), (154961833/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((207213879/35184372088832), (-1204835429/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((519127869/281474976710656), (718874049/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1125564833/9007199254740992), (164841545/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-127337419/144115188075855872), (-1341460637/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((163993195/288230376151711744), (465025423/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((-503503681/18446744073709551616), (1026286387/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-261326823/295147905179352825856), (-1390231971/590295810358705651712)), (33/590295810358705651712), by norm_num⟩
  | 10 => ⟨((382453525/2361183241434822606848), (57997475/4722366482869645213696)), (23/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-387491861/75557863725914323419136), (691189789/75557863725914323419136)), (33/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-119656359/302231454903657293676544), (-664004559/1208925819614629174706176)), (23/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((209/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((209/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((209/64), (7191/1024)))⁻¹=value ((3424256/62892817), (-7363584/62892817)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((3424256/62892817), (-7363584/62892817))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1077230035/549755813888), (405328401/274877906944)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-362044623/2199023255552), (-511651295/1099511627776)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((290398493/4398046511104), (-42683753/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-270857997/140737488355328), (499325027/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-87320965/140737488355328), (-55316729/140737488355328)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((467393431/9007199254740992), (-800327627/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((348165555/144115188075855872), (797149373/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((-1174752057/2305843009213693952), (138479849/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((272014063/36893488147419103232), (-1536048557/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 9 => ⟨((56015207/18446744073709551616), (56344633/36893488147419103232)), (19/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-865799137/4722366482869645213696), (230117373/1180591620717411303424)), (29/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-197335681/18889465931478580854784), (-674893823/37778931862957161709568)), (45/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((924261311/604462909807314587353088), (-115225295/302231454903657293676544)), (33/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((273/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((1490944/23596635), (-818176/7865545)), 0, by norm_num⟩
  | 1 => ⟨((1900896845824/556801183323225), (1219854598144/185600394441075)), 0, by norm_num⟩
  | 2 => ⟨((-988879407/2199023255552), (-132289877/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((138724731/8796093022208), (-789473175/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((94120267/140737488355328), (215206553/140737488355328)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1813298705/18014398509481984), (-243668881/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((139919057/36028797018963968), (-173223673/36028797018963968)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((293697303/2305843009213693952), (407991759/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-413743845/18446744073709551616), (-336114011/73786976294838206464)), (31/73786976294838206464), by norm_num⟩
  | 9 => ⟨((279063253/295147905179352825856), (-301827463/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 10 => ⟨((110109353/4722366482869645213696), (1539170531/18889465931478580854784)), (15/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-375867549/75557863725914323419136), (-411499727/302231454903657293676544)), (81/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((551201893/2417851639229258349412352), (-521563629/2417851639229258349412352)), (109/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((273/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((273/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((273/64), (7191/1024)))⁻¹=value ((1490944/23596635), (-818176/7865545)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((1490944/23596635), (-818176/7865545))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((130083009/4398046511104), (1306198169/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-41335605/549755813888), (-353976633/17592186044416)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((258307257/35184372088832), (-724556657/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((517969059/562949953421312), (381586445/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1618274511/9007199254740992), (402898933/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 5 => ⟨((72308467/36028797018963968), (-10674859/562949953421312)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((951648879/576460752303423488), (115528687/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-552438465/4611686018427387904), (270532249/2305843009213693952)), (11/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-228097313/36893488147419103232), (-983913063/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((731718741/590295810358705651712), (-8829301/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-229002993/9444732965739290427392), (941052911/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-1047911933/151115727451828646838272), (-672604359/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((153390153/302231454903657293676544), (-487428965/1208925819614629174706176)), (33/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((337/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((5521408/80784145), (-7363584/80784145)), 0, by norm_num⟩
  | 1 => ⟨((11868211511296/6526078083381025), (40657351606272/6526078083381025)), 0, by norm_num⟩
  | 2 => ⟨((-190261469/549755813888), (-285915377/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((624618277/35184372088832), (-398629685/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-101689099/1125899906842624), (673441679/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-926560205/18014398509481984), (-405301747/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((548863337/144115188075855872), (-116217423/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((-53840309/576460752303423488), (927565199/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-440879557/73786976294838206464), (-821262837/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 9 => ⟨((1679876921/2361183241434822606848), (15944633/147573952589676412928)), (21/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-552278677/18889465931478580854784), (542746383/18889465931478580854784)), (7/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-187601699/604462909807314587353088), (-1398982367/604462909807314587353088)), (73/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1122730179/9671406556917033397649408), (314068141/4835703278458516698824704)), (47/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((337/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((337/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((337/64), (7191/1024)))⁻¹=value ((5521408/80784145), (-7363584/80784145)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((5521408/80784145), (-7363584/80784145))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1023620791/35184372088832), (38709179/2199023255552)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1234205601/140737488355328), (436477515/70368744177664)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((-59077819/140737488355328), (-558611429/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((1311680539/4503599627370496), (258858009/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-187126073/9007199254740992), (17307139/562949953421312)), (11/36028797018963968), by norm_num⟩
  | 5 => ⟨((-164469231/72057594037927936), (-250503995/72057594037927936)), (13/288230376151711744), by norm_num⟩
  | 6 => ⟨((486929663/1152921504606846976), (-23320265/288230376151711744)), (7/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-75989493/9223372036854775808), (755422759/18446744073709551616)), (27/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-951222547/295147905179352825856), (-156634357/73786976294838206464)), (25/295147905179352825856), by norm_num⟩
  | 9 => ⟨((331392851/1180591620717411303424), (-230815395/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((254732997/37778931862957161709568), (269123107/9444732965739290427392)), (37/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-363999427/151115727451828646838272), (-102330667/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((462699341/4835703278458516698824704), (-831878185/4835703278458516698824704)), (49/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((401/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((6569984/92875537), (-7363584/92875537)), 0, by norm_num⟩
  | 1 => ⟨((5528839782400/8625865373038369), (48378629062656/8625865373038369)), 0, by norm_num⟩
  | 2 => ⟨((-16836695/68719476736), (-760705897/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((273075095/17592186044416), (-252965917/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-14303175/35184372088832), (835977089/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-271218487/18014398509481984), (-381701385/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((1275389715/576460752303423488), (16249725/18014398509481984)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1051582735/9223372036854775808), (257338181/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((134331137/73786976294838206464), (-119782169/18446744073709551616)), (5/36893488147419103232), by norm_num⟩
  | 9 => ⟨((455758477/2361183241434822606848), (712700283/2361183241434822606848)), (25/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-354984943/18889465931478580854784), (-114253003/37778931862957161709568)), (61/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((237126053/302231454903657293676544), (-771317423/1208925819614629174706176)), (37/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-23773617/9671406556917033397649408), (1038114789/19342813113834066795298816)), (45/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((401/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((401/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((401/64), (7191/1024)))⁻¹=value ((6569984/92875537), (-7363584/92875537)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((6569984/92875537), (-7363584/92875537))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((486060603/140737488355328), (-298758429/281474976710656)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-234925617/1125899906842624), (1473262933/1125899906842624)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-521368081/2251799813685248), (-728057419/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 3 => ⟨((716217825/18014398509481984), (-202538839/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 4 => ⟨((65289409/144115188075855872), (1785119911/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 5 => ⟨((-100683457/144115188075855872), (-76685829/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((1083179881/18446744073709551616), (-530285393/9223372036854775808)), (27/18446744073709551616), by norm_num⟩
  | 7 => ⟨((422990457/147573952589676412928), (583759103/73786976294838206464)), (27/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1915616321/2361183241434822606848), (-71828771/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((669880237/18889465931478580854784), (-1248498585/18889465931478580854784)), (3/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((38742053/9444732965739290427392), (789535153/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-664236241/1208925819614629174706176), (350199629/2417851639229258349412352)), (71/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((263892175/38685626227668133590597632), (-1805054565/38685626227668133590597632)), (117/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((465/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((2539520/35688027), (-818176/11896009)), 0, by norm_num⟩
  | 1 => ⟨((-212227063808/1273635271152729), (2077774315520/424545090384243)), 0, by norm_num⟩
  | 2 => ⟨((-714126851/4398046511104), (-791033699/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1683546713/140737488355328), (14346635/17592186044416)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-1021544685/2251799813685248), (860982091/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((107807251/36028797018963968), (-1052205273/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((517571595/576460752303423488), (658307561/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-164212931/2305843009213693952), (-179955589/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((423434135/147573952589676412928), (-620380853/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-35188089/1180591620717411303424), (819127707/4722366482869645213696)), (25/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-370573239/75557863725914323419136), (-543750271/75557863725914323419136)), (57/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1020276483/2417851639229258349412352), (211289819/2417851639229258349412352)), (65/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-348534741/19342813113834066795298816), (220547073/19342813113834066795298816)), (73/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((465/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((465/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((465/64), (7191/1024)))⁻¹=value ((2539520/35688027), (-818176/11896009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((2539520/35688027), (-818176/11896009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((194508967/1125899906842624), (-176238475/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((179621551/2251799813685248), (1121785113/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 2 => ⟨((-1250750549/36028797018963968), (98452273/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 3 => ⟨((349302141/144115188075855872), (-810733641/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 4 => ⟨((651887309/1152921504606846976), (799044961/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 5 => ⟨((-1032680417/9223372036854775808), (220467133/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 6 => ⟨((249823405/73786976294838206464), (-946721965/73786976294838206464)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((78867107/73786976294838206464), (277073979/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-312212673/2361183241434822606848), (517806985/9444732965739290427392)), (47/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((60211689/75557863725914323419136), (-1030614229/75557863725914323419136)), (11/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((660039663/604462909807314587353088), (364111109/604462909807314587353088)), (79/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-857869483/9671406556917033397649408), (310521433/4835703278458516698824704)), (69/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-274823633/154742504910672534362390528), (-1411939505/154742504910672534362390528)), (29/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((529/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((8667136/123349777), (-7363584/123349777)), 0, by norm_num⟩
  | 1 => ⟨((-10448438558720/15215167485949729), (63821183975424/15215167485949729)), 0, by norm_num⟩
  | 2 => ⟨((-3472929/34359738368), (-738267489/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1204916871/140737488355328), (202694785/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-870908655/2251799813685248), (347560583/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((323567165/36028797018963968), (-1222586905/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((220110337/1152921504606846976), (996292355/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1199062879/36893488147419103232), (-909829015/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((554262645/295147905179352825856), (-61210547/590295810358705651712)), (23/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-74236133/1180591620717411303424), (70476327/1180591620717411303424)), (25/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((64574123/151115727451828646838272), (-600554003/151115727451828646838272)), (53/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((250510847/2417851639229258349412352), (736841893/4835703278458516698824704)), (7/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-1267059651/154742504910672534362390528), (-87458401/38685626227668133590597632)), (59/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((529/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((529/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((529/64), (7191/1024)))⁻¹=value ((8667136/123349777), (-7363584/123349777)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((8667136/123349777), (-7363584/123349777))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-235987899/36028797018963968), (-4547281/140737488355328)), (9/18014398509481984), by norm_num⟩
  | 1 => ⟨((1025684293/72057594037927936), (355152449/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 2 => ⟨((-842592431/288230376151711744), (5665771/2251799813685248)), (15/288230376151711744), by norm_num⟩
  | 3 => ⟨((-318027975/2305843009213693952), (-1650120103/2305843009213693952)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((494873309/4611686018427387904), (165876321/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-416296881/36893488147419103232), (5939115/576460752303423488)), (27/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-259219577/590295810358705651712), (-531976907/295147905179352825856)), (33/590295810358705651712), by norm_num⟩
  | 7 => ⟨((473110961/2361183241434822606848), (247312507/4722366482869645213696)), (37/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-552353947/37778931862957161709568), (300089947/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-434491249/604462909807314587353088), (-302310931/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((477889717/2417851639229258349412352), (125573085/4835703278458516698824704)), (33/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-782860497/77371252455336267181195264), (572332129/38685626227668133590597632)), (117/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-233847881/309485009821345068724781056), (-419934357/309485009821345068724781056)), (51/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((593/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((9715712/141732625), (-7363584/141732625)), 0, by norm_num⟩
  | 1 => ⟨((-20086345170944/20088136989390625), (71542461431808/20088136989390625)), 0, by norm_num⟩
  | 2 => ⟨((-128078993/2199023255552), (-40693453/274877906944)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((411092465/70368744177664), (501181779/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-329595423/1125899906842624), (66880295/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((166850215/18014398509481984), (-310658007/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-215522645/2305843009213693952), (618121043/1152921504606846976)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-197815189/18446744073709551616), (-95941151/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1071944767/1180591620717411303424), (512947273/1180591620717411303424)), (7/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-801048423/18889465931478580854784), (328472839/37778931862957161709568)), (55/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((371030289/302231454903657293676544), (-423008385/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-55311545/9671406556917033397649408), (386188591/4835703278458516698824704)), (105/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-290692321/154742504910672534362390528), (-893116651/309485009821345068724781056)), (51/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((593/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((593/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((593/64), (7191/1024)))⁻¹=value ((9715712/141732625), (-7363584/141732625)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((9715712/141732625), (-7363584/141732625))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-153313573/72057594037927936), (-270153237/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 1 => ⟨((1560408253/1152921504606846976), (-113183241/288230376151711744)), (15/576460752303423488), by norm_num⟩
  | 2 => ⟨((-244094493/2305843009213693952), (860020399/2305843009213693952)), (9/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-972044737/18446744073709551616), (-1059280537/18446744073709551616)), (33/18446744073709551616), by norm_num⟩
  | 4 => ⟨((923995221/73786976294838206464), (-185215583/73786976294838206464)), (25/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-355492217/590295810358705651712), (125719343/73786976294838206464)), (35/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-695905593/4722366482869645213696), (-12896593/73786976294838206464)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((984039909/37778931862957161709568), (-175957257/37778931862957161709568)), (25/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-286710161/302231454903657293676544), (811459463/302231454903657293676544)), (53/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-920912381/4835703278458516698824704), (-523362119/2417851639229258349412352)), (13/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1046377365/38685626227668133590597632), (-58189883/9671406556917033397649408)), (49/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-215322971/309485009821345068724781056), (1515665119/618970019642690137449562112)), (177/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-802456817/4951760157141521099596496896), (-771279707/4951760157141521099596496896)), (39/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((657/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((1196032/18023625), (-818176/18023625)), 0, by norm_num⟩
  | 1 => ⟨((-42282254336/36094562015625), (978564677632/324851058140625)), 0, by norm_num⟩
  | 2 => ⟨((-259526167/8796093022208), (-1113028921/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1083959659/281474976710656), (496628231/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-1872306187/9007199254740992), (-267290723/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((272756337/36028797018963968), (-538043919/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-767602839/4611686018427387904), (1363693263/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-43867655/36893488147419103232), (-501354195/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 8 => ⟨((410717013/1180591620717411303424), (1000898229/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-1599120967/75557863725914323419136), (-116520113/18889465931478580854784)), (41/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1018190597/1208925819614629174706176), (-2603927/9444732965739290427392)), (19/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-838977333/38685626227668133590597632), (1093409125/38685626227668133590597632)), (69/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((96622191/1237940039285380274899124224), (-442570997/309485009821345068724781056)), (125/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((657/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((657/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((657/64), (7191/1024)))⁻¹=value ((1196032/18023625), (-818176/18023625)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((1196032/18023625), (-818176/18023625))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1043552601/4611686018427387904), (-128252903/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 1 => ⟨((739036649/9223372036854775808), (-845878045/9223372036854775808)), (15/4611686018427387904), by norm_num⟩
  | 2 => ⟨((344191741/36893488147419103232), (1269772607/36893488147419103232)), (19/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-265419967/36893488147419103232), (-173305771/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 4 => ⟨((595634671/590295810358705651712), (-242134443/295147905179352825856)), (29/590295810358705651712), by norm_num⟩
  | 5 => ⟨((212710909/9444732965739290427392), (449862355/2361183241434822606848)), (81/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-430391091/18889465931478580854784), (-101239457/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((760514767/302231454903657293676544), (-499581077/302231454903657293676544)), (61/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((31325443/2417851639229258349412352), (805603001/2417851639229258349412352)), (133/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-147275401/4835703278458516698824704), (-159384643/9671406556917033397649408)), (67/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((449733347/154742504910672534362390528), (-274137799/154742504910672534362390528)), (129/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((43413901/4951760157141521099596496896), (394682577/1237940039285380274899124224)), (119/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-251071403/9903520314283042199192993792), (-264601639/19807040628566084398385987584)), (213/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((721/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((11812864/184789777), (-7363584/184789777)), 0, by norm_num⟩
  | 1 => ⟨((-42660693278720/34147261683709729), (86985016344576/34147261683709729)), 0, by norm_num⟩
  | 2 => ⟨((-47596169/4398046511104), (-935134795/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((693582763/281474976710656), (895777985/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-40016649/281474976710656), (-474004453/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((805980995/144115188075855872), (-331616653/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-89831813/576460752303423488), (341732323/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((299290893/147573952589676412928), (-1157254297/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((431717095/4722366482869645213696), (1374477875/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-658949813/75557863725914323419136), (-141323133/18889465931478580854784)), (9/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((258600097/604462909807314587353088), (39514989/604462909807314587353088)), (31/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1158775693/77371252455336267181195264), (248920843/38685626227668133590597632)), (13/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((433901085/1237940039285380274899124224), (-156000819/309485009821345068724781056)), (87/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((721/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((721/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((721/64), (7191/1024)))⁻¹=value ((11812864/184789777), (-7363584/184789777)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((11812864/184789777), (-7363584/184789777))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1149132485/73786976294838206464), (133541005/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 1 => ⟨((16797571/9223372036854775808), (-1416306447/147573952589676412928)), (55/147573952589676412928), by norm_num⟩
  | 2 => ⟨((620066729/295147905179352825856), (20027997/9223372036854775808)), (9/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-195950199/295147905179352825856), (128668079/1180591620717411303424)), (71/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((480378543/9444732965739290427392), (-1032913313/9444732965739290427392)), (59/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((724229275/75557863725914323419136), (1193131923/75557863725914323419136)), (85/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-378494555/151115727451828646838272), (-55034677/604462909807314587353088)), (111/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((855248013/4835703278458516698824704), (-611555253/2417851639229258349412352)), (135/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((65242307/4835703278458516698824704), (1253086057/38685626227668133590597632)), (75/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-1138977263/309485009821345068724781056), (-93835427/154742504910672534362390528)), (155/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((303182597/1237940039285380274899124224), (-700688799/2475880078570760549798248448)), (153/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((438752713/39614081257132168796771975168), (672587143/19807040628566084398385987584)), (143/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-63056619/19807040628566084398385987584), (-112258355/158456325028528675187087900672)), (65/79228162514264337593543950336), by norm_num⟩
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
  | 0 => ⟨((785/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((12861440/209464081), (-7363584/209464081)), 0, by norm_num⟩
  | 1 => ⟨((-55597134774272/43875201229174561), (94706293800960/43875201229174561)), 0, by norm_num⟩
  | 2 => ⟨((16923077/17592186044416), (-1557649417/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((429753001/281474976710656), (192474327/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-855245129/9007199254740992), (-257322045/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1129687445/288230376151711744), (24549869/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-17556927/144115188075855872), (305648651/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((190015055/73786976294838206464), (-1232570703/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-53418687/9444732965739290427392), (1638421351/9444732965739290427392)), (1/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-434541787/151115727451828646838272), (-409918699/75557863725914323419136)), (25/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((888039581/4835703278458516698824704), (280506501/2417851639229258349412352)), (39/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-37124585/4835703278458516698824704), (-12914501/38685626227668133590597632)), (31/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1196165597/4951760157141521099596496896), (-617457171/4951760157141521099596496896)), (97/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((785/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((785/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((785/64), (7191/1024)))⁻¹=value ((12861440/209464081), (-7363584/209464081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((12861440/209464081), (-7363584/209464081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-828486627/1180591620717411303424), (292782457/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-261446167/1180591620717411303424), (-821810629/1180591620717411303424)), (23/590295810358705651712), by norm_num⟩
  | 2 => ⟨((1059541857/4722366482869645213696), (363402959/4722366482869645213696)), (63/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-426660129/9444732965739290427392), (597139691/18889465931478580854784)), (65/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((16566133/151115727451828646838272), (-1551613293/151115727451828646838272)), (55/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((798359357/604462909807314587353088), (287055677/302231454903657293676544)), (41/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-129497031/604462909807314587353088), (370008043/4835703278458516698824704)), (109/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((278540341/38685626227668133590597632), (-67367923/2417851639229258349412352)), (135/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((345976731/154742504910672534362390528), (772648713/309485009821345068724781056)), (77/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-1781713297/4951760157141521099596496896), (271334617/4951760157141521099596496896)), (81/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((300519289/19807040628566084398385987584), (-673309725/19807040628566084398385987584)), (325/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((635570829/316912650057057350374175801344), (952629871/316912650057057350374175801344)), (155/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-212196701/633825300114114700748351602688), (57709087/5070602400912917605986812821504)), (571/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((34978699/8796093022208), (1588934135/8796093022208)), (1249/8796093022208), by norm_num⟩
  | 1 => ⟨((-70459257/549755813888), (197265047/1099511627776)), (83/274877906944), by norm_num⟩
  | 2 => ⟨((-1099514441/8796093022208), (90346857/2199023255552)), (359/1099511627776), by norm_num⟩
  | 3 => ⟨((-858427363/17592186044416), (-134290641/8796093022208)), (2111/8796093022208), by norm_num⟩
  | 4 => ⟨((-629255023/70368744177664), (-403233553/35184372088832)), (2367/17592186044416), by norm_num⟩
  | 5 => ⟨((-70820219/281474976710656), (-1809232067/562949953421312)), (17237/281474976710656), by norm_num⟩
  | 6 => ⟨((151068441/562949953421312), (-290246523/562949953421312)), (52961/2251799813685248), by norm_num⟩
  | 7 => ⟨((334070281/4503599627370496), (-424658463/9007199254740992)), (70535/9007199254740992), by norm_num⟩
  | 8 => ⟨((822444271/72057594037927936), (-33570469/36028797018963968)), (166245/72057594037927936), by norm_num⟩
  | 9 => ⟨((712041189/576460752303423488), (133717305/288230376151711744)), (704481/1152921504606846976), by norm_num⟩
  | 10 => ⟨((922702005/9223372036854775808), (218410485/2305843009213693952)), (1358745/9223372036854775808), by norm_num⟩
  | 11 => ⟨((423748259/73786976294838206464), (441707583/36893488147419103232)), (1204925/36893488147419103232), by norm_num⟩
  | 12 => ⟨((18495635/147573952589676412928), (1399511065/1180591620717411303424)), (990671/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((34978699/8796093022208), (1588934135/8796093022208)), (625/4398046511104), by norm_num⟩
  | 1 => ⟨((-70459257/549755813888), (197265047/1099511627776)), (1329/4398046511104), by norm_num⟩
  | 2 => ⟨((-1099514441/8796093022208), (90346857/2199023255552)), (2873/8796093022208), by norm_num⟩
  | 3 => ⟨((-858427363/17592186044416), (-134290641/8796093022208)), (4223/17592186044416), by norm_num⟩
  | 4 => ⟨((-629255023/70368744177664), (-403233553/35184372088832)), (9471/70368744177664), by norm_num⟩
  | 5 => ⟨((-70820219/281474976710656), (-1809232067/562949953421312)), (34497/562949953421312), by norm_num⟩
  | 6 => ⟨((151068441/562949953421312), (-290246523/562949953421312)), (13263/562949953421312), by norm_num⟩
  | 7 => ⟨((334070281/4503599627370496), (-424658463/9007199254740992)), (4431/562949953421312), by norm_num⟩
  | 8 => ⟨((822444271/72057594037927936), (-33570469/36028797018963968)), (338255/144115188075855872), by norm_num⟩
  | 9 => ⟨((712041189/576460752303423488), (133717305/288230376151711744)), (375299/576460752303423488), by norm_num⟩
  | 10 => ⟨((922702005/9223372036854775808), (218410485/2305843009213693952)), (26995/144115188075855872), by norm_num⟩
  | 11 => ⟨((423748259/73786976294838206464), (441707583/36893488147419103232)), (2680665/36893488147419103232), by norm_num⟩
  | 12 => ⟨((18495635/147573952589676412928), (1399511065/1180591620717411303424)), (55149033/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile039Gamma
