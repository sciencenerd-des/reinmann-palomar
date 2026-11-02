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
namespace Reinmann.XiRectangle.Tile037Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (3525/256))
  have he : value ((5/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((21/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((213/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((1163264/19627827), (-601600/19627827)), 0, by norm_num⟩
  | 1 => ⟨((-55070031872/42805732526881), (699819622400/385251592741929)), 0, by norm_num⟩
  | 2 => ⟨((45232225/4398046511104), (-1293820601/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((462930021/562949953421312), (1315602999/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-67759747/1125899906842624), (-1020506167/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((191065073/72057594037927936), (436025743/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1663259865/18446744073709551616), (336130889/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((706178623/295147905179352825856), (-567205365/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-391478015/9444732965739290427392), (884170533/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-62380587/302231454903657293676544), (-1030403967/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((282234449/4835703278458516698824704), (946495955/9671406556917033397649408)), (31/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-499714335/154742504910672534362390528), (-310351291/154742504910672534362390528)), (23/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1252111355/9903520314283042199192993792), (98459951/9903520314283042199192993792)), (67/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (3525/512)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (3525/512)))⁻¹=value ((1163264/19627827), (-601600/19627827)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((1163264/19627827), (-601600/19627827))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((363355703/134217728), (64060177/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((581632/19627827), (-300800/19627827)), 0, by norm_num⟩
  | 2 => ⟨((-13767507968/42805732526881), (174954905600/385251592741929)), 0, by norm_num⟩
  | 3 => ⟨((241238533/140737488355328), (-1725094135/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((462930021/4503599627370496), (1315602999/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-433662381/72057594037927936), (-408202467/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((1019013723/4611686018427387904), (290683829/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-950434209/147573952589676412928), (96037397/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((706178623/4722366482869645213696), (-567205365/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-173990229/75557863725914323419136), (785929363/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-99808939/9671406556917033397649408), (-1648646347/9671406556917033397649408)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((410522835/154742504910672534362390528), (688360695/154742504910672534362390528)), (3/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-166571445/1237940039285380274899124224), (-413801721/4951760157141521099596496896)), (31/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (75/8192)), 0, by norm_num⟩
  | 45 => ⟨((73564147309/3264510689280), (-299775/24117248)), 0, by norm_num⟩
  | 44 => ⟨((-194555954897327/9192862101012480), (447018893345/37933151158272)), 0, by norm_num⟩
  | 43 => ⟨((93372057/4294967296), (-380917181/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-389824933/17179869184), (385404547/34359738368)), (1/34359738368), by norm_num⟩
  | 41 => ⟨((50197529/2147483648), (-200108791/17179869184)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-821686553/34359738368), (412822269/34359738368)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((210350015/8589934592), (-422911199/34359738368)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-863554777/34359738368), (54136063/4294967296)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((887334741/34359738368), (-111082775/8589934592)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-456143483/17179869184), (114112993/8589934592)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((938532209/34359738368), (-469224789/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-241579551/8589934592), (241331747/17179869184)), (3/34359738368), by norm_num⟩
  | 33 => ⟨((995826389/34359738368), (-496877031/34359738368)), (3/34359738368), by norm_num⟩
  | 32 => ⟨((-1027204419/34359738368), (255980885/17179869184)), (3/34359738368), by norm_num⟩
  | 31 => ⟨((530310425/17179869184), (-527997433/34359738368)), (3/34359738368), by norm_num⟩
  | 30 => ⟨((-548139805/17179869184), (272534971/17179869184)), (3/34359738368), by norm_num⟩
  | 29 => ⟨((1134416855/34359738368), (-281640739/17179869184)), (3/34359738368), by norm_num⟩
  | 28 => ⟨((-293825321/8589934592), (582750821/34359738368)), (3/34359738368), by norm_num⟩
  | 27 => ⟨((304810091/8589934592), (-75451693/4294967296)), (3/34359738368), by norm_num⟩
  | 26 => ⟨((-316647267/8589934592), (313012361/17179869184)), (3/34359738368), by norm_num⟩
  | 25 => ⟨((82359989/2147483648), (-650163145/34359738368)), (3/34359738368), by norm_num⟩
  | 24 => ⟨((-1373234431/34359738368), (84529539/4294967296)), (3/34359738368), by norm_num⟩
  | 23 => ⟨((1433579107/34359738368), (-704486393/34359738368)), (3/34359738368), by norm_num⟩
  | 22 => ⟨((-749731899/17179869184), (183799427/8589934592)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((392921771/8589934592), (-384353145/17179869184)), (3/17179869184), by norm_num⟩
  | 20 => ⟨((-206401071/4294967296), (402706105/17179869184)), (3/17179869184), by norm_num⟩
  | 19 => ⟨((869595789/17179869184), (-422897791/17179869184)), (3/17179869184), by norm_num⟩
  | 18 => ⟨((-229632521/4294967296), (445218813/17179869184)), (3/17179869184), by norm_num⟩
  | 17 => ⟨((3801907/67108864), (-470024369/17179869184)), (3/17179869184), by norm_num⟩
  | 16 => ⟨((-1034973349/17179869184), (62219153/2147483648)), (3/17179869184), by norm_num⟩
  | 15 => ⟨((1104985649/17179869184), (-528953795/17179869184)), (3/17179869184), by norm_num⟩
  | 14 => ⟨((-592564445/8589934592), (564320659/17179869184)), (3/17179869184), by norm_num⟩
  | 13 => ⟨((638883525/8589934592), (-604746651/17179869184)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((-1386059515/17179869184), (651398955/17179869184)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((757162701/8589934592), (-176458275/4294967296)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-417156949/4294967296), (385084435/8589934592)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((464437417/4294967296), (-423685629/8589934592)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-1047452753/8589934592), (470858791/8589934592)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((1200463317/8589934592), (-66225779/1073741824)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-1405321605/8589934592), (605547677/8589934592)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((26460487/134217728), (-353209977/4294967296)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-1063981447/4294967296), (423676741/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((89254013/268435456), (-528993383/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-539932273/1073741824), (351673659/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((1088771363/1073741824), (-130933395/536870912)), (1/1073741824), by norm_num⟩
  | 0 => ⟨((-140397695/2147483648), (1024962831/2147483648)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (3525/8192)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (3525/8192)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (3525/8192))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((363355703/134217728), (64060177/134217728)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (3525/512))) (z:=((-43/256), (3525/8192))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((363355703/134217728), (64060177/134217728))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((205/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((526806955/16777216), (207649367/8388608)), (3/33554432), by norm_num⟩
  | 1 => ⟨((493596153/268435456), (2066159/8388608)), (1/268435456), by norm_num⟩
  | 2 => ⟨((971998951424/128417197580643), (-1563490043200/385251592741929)), 0, by norm_num⟩
  | 3 => ⟨((-479049853/8796093022208), (359836547/4398046511104)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((22921535/140737488355328), (-944772255/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((119689903/9007199254740992), (1154533015/36028797018963968)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-705593225/1152921504606846976), (-580605433/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1402195663/73786976294838206464), (71047849/18446744073709551616)), (59/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1126978869/2361183241434822606848), (333876137/2361183241434822606848)), (73/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((178677361/18889465931478580854784), (-350332443/37778931862957161709568)), (201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-265908247/2417851639229258349412352), (417412143/1208925819614629174706176)), (273/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-277849739/154742504910672534362390528), (-1543195869/154742504910672534362390528)), (373/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((220126667/1237940039285380274899124224), (1124715135/4951760157141521099596496896)), (995/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((303460267/16777216), (149895767/8388608)), (3/33554432), by norm_num⟩
  | 1 => ⟨((359378425/268435456), (2066159/8388608)), (1/268435456), by norm_num⟩
  | 2 => ⟨((971998951424/128417197580643), (-1563490043200/385251592741929)), 0, by norm_num⟩
  | 3 => ⟨((-479049853/8796093022208), (359836547/4398046511104)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((22921535/140737488355328), (-944772255/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((119689903/9007199254740992), (1154533015/36028797018963968)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-705593225/1152921504606846976), (-580605433/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1402195663/73786976294838206464), (71047849/18446744073709551616)), (59/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1126978869/2361183241434822606848), (333876137/2361183241434822606848)), (73/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((178677361/18889465931478580854784), (-350332443/37778931862957161709568)), (201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-265908247/2417851639229258349412352), (417412143/1208925819614629174706176)), (273/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-277849739/154742504910672534362390528), (-1543195869/154742504910672534362390528)), (373/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((220126667/1237940039285380274899124224), (1124715135/4951760157141521099596496896)), (995/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((637754995/33554432), (149895767/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((359378425/268435456), (2066159/8388608)), (1/268435456), by norm_num⟩
  | 2 => ⟨((971998951424/128417197580643), (-1563490043200/385251592741929)), 0, by norm_num⟩
  | 3 => ⟨((-479049853/8796093022208), (359836547/4398046511104)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((22921535/140737488355328), (-944772255/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((119689903/9007199254740992), (1154533015/36028797018963968)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-705593225/1152921504606846976), (-580605433/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1402195663/73786976294838206464), (71047849/18446744073709551616)), (59/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1126978869/2361183241434822606848), (333876137/2361183241434822606848)), (73/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((178677361/18889465931478580854784), (-350332443/37778931862957161709568)), (201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-265908247/2417851639229258349412352), (417412143/1208925819614629174706176)), (273/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-277849739/154742504910672534362390528), (-1543195869/154742504910672534362390528)), (373/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((220126667/1237940039285380274899124224), (1124715135/4951760157141521099596496896)), (995/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((110140063744/42805732526881), (-1399639244800/385251592741929)), 0, by norm_num⟩
  | 1 => ⟨((-45232225/1099511627776), (1293820601/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-86799379/17592186044416), (-986702249/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((67759747/140737488355328), (1020506167/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-955325365/36028797018963968), (-272516089/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((1247444899/1152921504606846976), (-252098167/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-617906295/18446744073709551616), (496304695/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((391478015/590295810358705651712), (-884170533/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((70178161/18889465931478580854784), (1159204463/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-705586123/604462909807314587353088), (-147889993/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((687107211/9671406556917033397649408), (426733025/9671406556917033397649408)), (9/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1878167033/618970019642690137449562112), (-147689927/618970019642690137449562112)), (27/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((125491505/1237940039285380274899124224), (-105762581/2475880078570760549798248448)), (41/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((45232225/1099511627776), (-1293820601/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((86799379/8796093022208), (986702249/35184372088832)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-203279241/140737488355328), (-765379625/562949953421312)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((955325365/9007199254740992), (272516089/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-389826531/72057594037927936), (315122709/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((926859443/4611686018427387904), (-372228521/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-342543263/73786976294838206464), (773649217/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-70178161/2361183241434822606848), (-1159204463/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((793784389/75557863725914323419136), (1331009937/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-429442007/604462909807314587353088), (-533416281/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1291239835/38685626227668133590597632), (12692103/4835703278458516698824704)), (13/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-1505898061/1237940039285380274899124224), (317287743/618970019642690137449562112)), (5/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((325727167/9903520314283042199192993792), (-781807695/19807040628566084398385987584)), (31/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-462930021/70368744177664), (-1315602999/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((67759747/35184372088832), (1020506167/562949953421312)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-955325365/4503599627370496), (-272516089/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((129942177/9007199254740992), (-105040903/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((-772382869/1152921504606846976), (155095217/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((342543263/18446744073709551616), (-773649217/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((81874521/590295810358705651712), (1352405207/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-529189593/9444732965739290427392), (-443669979/4722366482869645213696)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1288326021/302231454903657293676544), (400062211/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-269008299/1208925819614629174706176), (-21153505/1208925819614629174706176)), (17/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((345101639/38685626227668133590597632), (-145423549/38685626227668133590597632)), (29/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-325727167/1237940039285380274899124224), (781807695/2475880078570760549798248448)), (25/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((73232219/19807040628566084398385987584), (-1326039479/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-67759747/70368744177664), (-1020506167/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((955325365/4503599627370496), (272516089/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1559306123/72057594037927936), (315122709/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 3 => ⟨((772382869/576460752303423488), (-155095217/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((-428179079/9223372036854775808), (967061521/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-61405891/147573952589676412928), (-1014303905/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((231520447/1180591620717411303424), (776422463/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-1288326021/75557863725914323419136), (-400062211/37778931862957161709568)), (19/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((605268673/604462909807314587353088), (95190773/1208925819614629174706176)), (19/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-862754097/19342813113834066795298816), (363558873/19342813113834066795298816)), (17/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((895749709/618970019642690137449562112), (-1074985581/618970019642690137449562112)), (15/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-219696657/9903520314283042199192993792), (994529609/9903520314283042199192993792)), (13/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-186262793/158456325028528675187087900672), (-1401080211/316912650057057350374175801344)), (43/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-191065073/2251799813685248), (-436025743/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((1247444899/72057594037927936), (-252098167/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 2 => ⟨((-463429721/288230376151711744), (372228521/288230376151711744)), (9/576460752303423488), by norm_num⟩
  | 3 => ⟨((342543263/4611686018427387904), (-773649217/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((61405891/73786976294838206464), (1014303905/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-34728067/73786976294838206464), (-232926739/295147905179352825856)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((901828215/18889465931478580854784), (560087095/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-1936859753/604462909807314587353088), (-38076309/151115727451828646838272)), (29/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((24264959/151115727451828646838272), (-327202985/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-895749709/154742504910672534362390528), (537492791/77371252455336267181195264)), (29/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((120833161/1237940039285380274899124224), (-546991285/1237940039285380274899124224)), (27/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((447030703/79228162514264337593543950336), (840648127/39614081257132168796771975168)), (49/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-221073915/316912650057057350374175801344), (-974011081/1267650600228229401496703205376)), (43/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1663259865/288230376151711744), (336130889/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 1 => ⟨((617906295/576460752303423488), (-496304695/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 2 => ⟨((-342543263/4611686018427387904), (773649217/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-81874521/73786976294838206464), (-1352405207/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 4 => ⟨((231520447/295147905179352825856), (776422463/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-901828215/9444732965739290427392), (-70010887/1180591620717411303424)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((141229357/18889465931478580854784), (88844721/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-1035304917/2417851639229258349412352), (436270647/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((335906141/19342813113834066795298816), (-403119593/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-100694301/309485009821345068724781056), (455826071/309485009821345068724781056)), (23/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-409778145/19807040628566084398385987584), (-1541188233/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((221073915/79228162514264337593543950336), (974011081/316912650057057350374175801344)), (43/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-246787539/1267650600228229401496703205376), (-183730911/2535301200456458802993406410752)), (39/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-706178623/2305843009213693952), (567205365/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 1 => ⟨((391478015/9223372036854775808), (-442085267/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((70178161/73786976294838206464), (1159204463/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-529189593/590295810358705651712), (-443669979/295147905179352825856)), (17/590295810358705651712), by norm_num⟩
  | 4 => ⟨((644163011/4722366482869645213696), (400062211/4722366482869645213696)), (29/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-968429877/75557863725914323419136), (-38076309/37778931862957161709568)), (41/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((1035304917/1208925819614629174706176), (-436270647/1208925819614629174706176)), (13/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-767785465/19342813113834066795298816), (921416213/19342813113834066795298816)), (15/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((258928203/309485009821345068724781056), (-1172124183/309485009821345068724781056)), (17/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((292698675/4951760157141521099596496896), (550424369/2475880078570760549798248448)), (35/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-694803733/79228162514264337593543950336), (-765294421/79228162514264337593543950336)), (9/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((846128705/1267650600228229401496703205376), (78741819/316912650057057350374175801344)), (35/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-1514947945/40564819207303340847894502572032), (184104453/40564819207303340847894502572032)), (33/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-391478015/36893488147419103232), (884170533/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-70178161/147573952589676412928), (-1159204463/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 2 => ⟨((793784389/1180591620717411303424), (1331009937/1180591620717411303424)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-644163011/4722366482869645213696), (-400062211/4722366482869645213696)), (33/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((605268673/37778931862957161709568), (23797693/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-24264959/18889465931478580854784), (163601493/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((335906141/4835703278458516698824704), (-403119593/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-129464101/77371252455336267181195264), (1172124183/154742504910672534362390528)), (39/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-329286009/2475880078570760549798248448), (-619227415/1237940039285380274899124224)), (23/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((868504667/39614081257132168796771975168), (478309013/19807040628566084398385987584)), (25/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-581713485/316912650057057350374175801344), (-433080005/633825300114114700748351602688)), (53/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((1136210959/10141204801825835211973625643008), (-34519585/2535301200456458802993406410752)), (27/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-420710649/81129638414606681695789005144064), (573448485/162259276829213363391578010288128)), (53/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62380587/590295810358705651712), (1030403967/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-176396531/590295810358705651712), (-147889993/295147905179352825856)), (33/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((429442007/4722366482869645213696), (266708141/4722366482869645213696)), (27/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-269008299/18889465931478580854784), (-21153505/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((862754097/604462909807314587353088), (-363558873/604462909807314587353088)), (31/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-895749709/9671406556917033397649408), (537492791/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((100694301/38685626227668133590597632), (-455826071/38685626227668133590597632)), (37/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((292698675/1237940039285380274899124224), (550424369/618970019642690137449562112)), (49/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-868504667/19807040628566084398385987584), (-478309013/9903520314283042199192993792)), (59/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1292696633/316912650057057350374175801344), (481200005/316912650057057350374175801344)), (17/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-1388702283/5070602400912917605986812821504), (10547651/316912650057057350374175801344)), (75/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((140236883/10141204801825835211973625643008), (-764597981/81129638414606681695789005144064)), (79/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-301385679/649037107316853453566312041152512), (139477101/162259276829213363391578010288128)), (81/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((282234449/4722366482869645213696), (946495955/9444732965739290427392)), (31/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-687107211/18889465931478580854784), (-426733025/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((322809959/37778931862957161709568), (101536825/151115727451828646838272)), (47/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-345101639/302231454903657293676544), (145423549/302231454903657293676544)), (59/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((895749709/9671406556917033397649408), (-537492791/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-120833161/38685626227668133590597632), (546991285/38685626227668133590597632)), (27/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-409778145/1237940039285380274899124224), (-1541188233/1237940039285380274899124224)), (83/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((694803733/9903520314283042199192993792), (765294421/9903520314283042199192993792)), (29/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-581713485/79228162514264337593543950336), (-433080005/158456325028528675187087900672)), (73/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((1388702283/2535301200456458802993406410752), (-10547651/158456325028528675187087900672)), (11/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-617042285/20282409603651670423947251286016), (841057779/40564819207303340847894502572032)), (101/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((723325629/649037107316853453566312041152512), (-1338980169/649037107316853453566312041152512)), (111/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-13408519/5192296858534827628530496329220096), (1489052007/10384593717069655257060992658440192)), (117/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((290816/58883481), (-150400/58883481)), 0, by norm_num⟩
  | 1 => ⟨((-13767507968/128417197580643), (174954905600/1155754778225787)), 0, by norm_num⟩
  | 2 => ⟨((241238533/281474976710656), (-1725094135/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((154310007/2251799813685248), (438534333/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-722770635/144115188075855872), (-680337445/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((1019013723/4611686018427387904), (290683829/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-554419955/73786976294838206464), (224087259/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((941571497/4722366482869645213696), (-189068455/1180591620717411303424)), (13/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-521970687/151115727451828646838272), (294723511/37778931862957161709568)), (19/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-20793529/1208925819614629174706176), (-343467989/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((752625197/154742504910672534362390528), (1261994607/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-166571445/618970019642690137449562112), (-413801721/2475880078570760549798248448)), (31/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1669481807/158456325028528675187087900672), (131279935/158456325028528675187087900672)), (45/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((637920715/33554432), (599497363/33554432)), (5/33554432), by norm_num⟩
  | 1 => ⟨((1437398585/1073741824), (66157723/268435456)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1040403059/137438953472), (-558619221/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-59805885/1099511627776), (721386119/8796093022208)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((88862817/562949953421312), (-947429823/562949953421312)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((486720657/36028797018963968), (578401991/18014398509481984)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-714256037/1152921504606846976), (-578854751/1152921504606846976)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((708453859/36893488147419103232), (136187309/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1135134661/2361183241434822606848), (88074089/590295810358705651712)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((89176231/9444732965739290427392), (-722131635/75557863725914323419136)), (203/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-127074239/1208925819614629174706176), (106817869/302231454903657293676544)), (275/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-39936575/19342813113834066795298816), (-1569058477/154742504910672534362390528)), (749/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((466338987/2475880078570760549798248448), (1128817633/4951760157141521099596496896)), (999/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-128660551/1125899906842624), (920050205/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-493792023/18014398509481984), (-1403309865/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((144554127/36028797018963968), (136067489/36028797018963968)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-339671241/1152921504606846976), (-193789219/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 4 => ⟨((554419955/36893488147419103232), (-56021815/18446744073709551616)), (5/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-41193753/73786976294838206464), (264695837/590295810358705651712)), (5/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((487172641/37778931862957161709568), (-1100301109/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((24952235/302231454903657293676544), (1648646347/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-564468899/19342813113834066795298816), (-946495955/19342813113834066795298816)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1221523931/618970019642690137449562112), (758636489/618970019642690137449562112)), (3/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-459107497/4951760157141521099596496896), (-144407927/19807040628566084398385987584)), (19/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((1070860843/316912650057057350374175801344), (-451253679/316912650057057350374175801344)), (29/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-926512831/10141204801825835211973625643008), (1111904277/10141204801825835211973625643008)), (45/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((637920711/33554432), (299748695/16777216)), (3/16777216), by norm_num⟩
  | 1 => ⟨((359349639/268435456), (33078851/134217728)), (3/536870912), by norm_num⟩
  | 2 => ⟨((520201805/68719476736), (-279309351/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-478449671/8796093022208), (180346345/2199023255552)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((88871277/562949953421312), (-1894863065/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((486700543/36028797018963968), (578410069/18014398509481984)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-357120585/576460752303423488), (-289444165/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((708456905/36893488147419103232), (272475243/73786976294838206464)), (15/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-567601783/1180591620717411303424), (352180817/2361183241434822606848)), (37/590295810358705651712), by norm_num⟩
  | 9 => ⟨((44597435/4722366482869645213696), (-180509757/18889465931478580854784)), (51/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-63593163/604462909807314587353088), (213631331/604462909807314587353088)), (69/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-318969719/154742504910672534362390528), (-49039963/4835703278458516698824704)), (375/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((932225575/4951760157141521099596496896), (1129360555/4951760157141521099596496896)), (125/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-881091821/1152921504606846976), (-414681871/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((1552782815/9223372036854775808), (221473393/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-1267245611/73786976294838206464), (256099725/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((156928583/147573952589676412928), (-504182547/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-173990229/4722366482869645213696), (785929363/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-24952235/75557863725914323419136), (-1648646347/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((752625199/4835703278458516698824704), (1261994607/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-32719391/2417851639229258349412352), (-81282481/9671406556917033397649408)), (17/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((1967603559/2475880078570760549798248448), (38680695/618970019642690137449562112)), (1/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-701158885/19807040628566084398385987584), (295463719/19807040628566084398385987584)), (29/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((727974367/633825300114114700748351602688), (-873639075/633825300114114700748351602688)), (13/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-357094249/20282409603651670423947251286016), (1616505269/20282409603651670423947251286016)), (43/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-37843869/40564819207303340847894502572032), (-71165979/20282409603651670423947251286016)), (9/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((637920711/33554432), (299748695/16777216)), (7/33554432), by norm_num⟩
  | 1 => ⟨((359349639/268435456), (33078851/134217728)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((130050451/17179869184), (-279309351/68719476736)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-239224831/4398046511104), (180346343/2199023255552)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((177742513/1125899906842624), (-1894862971/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((486700531/36028797018963968), (1156819941/36028797018963968)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-714240991/1152921504606846976), (-578888029/1152921504606846976)), (49/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1416912811/73786976294838206464), (272474623/73786976294838206464)), (121/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-567600845/1180591620717411303424), (352180965/2361183241434822606848)), (149/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((713556285/75557863725914323419136), (-722037901/75557863725914323419136)), (205/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-254369875/2417851639229258349412352), (854521991/2417851639229258349412352)), (277/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-318972443/154742504910672534362390528), (-1569266483/154742504910672534362390528)), (751/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((932220955/4951760157141521099596496896), (282335795/1237940039285380274899124224)), (1001/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1013796489/295147905179352825856), (-51219945/73786976294838206464)), (7/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-376628599/590295810358705651712), (605019057/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 2 => ⟨((417576549/9444732965739290427392), (-235778809/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((24952235/37778931862957161709568), (412161587/37778931862957161709568)), (11/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-564468899/1208925819614629174706176), (-946495955/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((549685769/9671406556917033397649408), (682772841/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-1377322491/309485009821345068724781056), (-54152973/154742504910672534362390528)), (25/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((631042997/2475880078570760549798248448), (-531834693/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-818971163/79228162514264337593543950336), (122855495/9903520314283042199192993792)), (15/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((30687787/158456325028528675187087900672), (-1111347373/1267650600228229401496703205376)), (29/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((3902649/316912650057057350374175801344), (939390923/20282409603651670423947251286016)), (7/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-538999259/324518553658426726783156020576256), (-593682945/324518553658426726783156020576256)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((1203383047/10384593717069655257060992658440192), (447953459/10384593717069655257060992658440192)), (49/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((637920711/33554432), (299748695/16777216)), (1/4194304), by norm_num⟩
  | 1 => ⟨((359349639/268435456), (33078851/134217728)), (1/134217728), by norm_num⟩
  | 2 => ⟨((130050451/17179869184), (-279309351/68719476736)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-239224831/4398046511104), (180346343/2199023255552)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((11108907/70368744177664), (-473715743/281474976710656)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((486700533/36028797018963968), (578409971/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-178560249/288230376151711744), (-578888029/1152921504606846976)), (25/576460752303423488), by norm_num⟩
  | 7 => ⟨((708456415/36893488147419103232), (272474615/73786976294838206464)), (61/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-567600857/1180591620717411303424), (176090497/1180591620717411303424)), (75/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((178389075/18889465931478580854784), (-722037967/75557863725914323419136)), (103/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-254369845/2417851639229258349412352), (854522103/2417851639229258349412352)), (139/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-79743175/38685626227668133590597632), (-784633383/77371252455336267181195264)), (47/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((932221529/4951760157141521099596496896), (564671697/2475880078570760549798248448)), (501/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-337435595/37778931862957161709568), (762113321/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-120980533/302231454903657293676544), (-1998359209/302231454903657293676544)), (35/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((342102363/604462909807314587353088), (71704239/75557863725914323419136)), (27/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-555238151/4835703278458516698824704), (-689669535/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((521713065/38685626227668133590597632), (41024979/38685626227668133590597632)), (27/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((-1338576055/1237940039285380274899124224), (141016775/309485009821345068724781056)), (43/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((579070519/9903520314283042199192993792), (-347470087/4951760157141521099596496896)), (7/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-223183905/158456325028528675187087900672), (505157897/79228162514264337593543950336)), (17/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-141914509/1267650600228229401496703205376), (-1067489685/2535301200456458802993406410752)), (5/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((748610083/40564819207303340847894502572032), (824559645/40564819207303340847894502572032)), (11/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-501409603/324518553658426726783156020576256), (-186647275/324518553658426726783156020576256)), (47/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((30605009/324518553658426726783156020576256), (-29754255/2596148429267413814265248164610048)), (47/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-90658187/20769187434139310514121985316880384), (494285563/166153499473114484112975882535043072)), (23/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((637920711/33554432), (299748695/16777216)), (9/33554432), by norm_num⟩
  | 1 => ⟨((359349639/268435456), (33078851/134217728)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((130050451/17179869184), (-279309351/68719476736)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-239224831/4398046511104), (180346343/2199023255552)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((11108907/70368744177664), (-473715743/281474976710656)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((486700533/36028797018963968), (578409971/18014398509481984)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-178560249/288230376151711744), (-578888029/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((708456415/36893488147419103232), (272474615/73786976294838206464)), (123/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-567600857/1180591620717411303424), (352180993/2361183241434822606848)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((713556301/75557863725914323419136), (-722037965/75557863725914323419136)), (207/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-254369849/2417851639229258349412352), (427261051/1208925819614629174706176)), (279/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-318972685/154742504910672534362390528), (-98079173/9671406556917033397649408)), (753/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((932221507/4951760157141521099596496896), (1129343409/4951760157141521099596496896)), (1003/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-554180765/4835703278458516698824704), (-929244913/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((674583845/9671406556917033397649408), (13092353/302231454903657293676544)), (27/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-1267705417/77371252455336267181195264), (-99686193/77371252455336267181195264)), (47/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((1355246965/618970019642690137449562112), (-571092111/618970019642690137449562112)), (59/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-879423579/4951760157141521099596496896), (263848165/1237940039285380274899124224)), (31/2475880078570760549798248448), by norm_num⟩
  | 5 => ⟨((237261659/39614081257132168796771975168), (-1074043405/39614081257132168796771975168)), (27/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((402309439/633825300114114700748351602688), (189137275/79228162514264337593543950336)), (41/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((-682140089/5070602400912917605986812821504), (-375672999/2535301200456458802993406410752)), (29/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((71388881/5070602400912917605986812821504), (212593297/40564819207303340847894502572032)), (73/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-340847873/324518553658426726783156020576256), (165686515/1298074214633706907132624082305024)), (87/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((1211591875/20769187434139310514121985316880384), (-206432119/5192296858534827628530496329220096)), (25/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((-355071069/166153499473114484112975882535043072), (164321953/41538374868278621028243970633760768)), (55/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((26328265/5316911983139663491615228241121378304), (-365478055/1329227995784915872903807060280344576)), (29/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((637920711/33554432), (299748695/16777216)), (5/16777216), by norm_num⟩
  | 1 => ⟨((359349639/268435456), (33078851/134217728)), (5/536870912), by norm_num⟩
  | 2 => ⟨((130050451/17179869184), (-279309351/68719476736)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-239224831/4398046511104), (180346343/2199023255552)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((11108907/70368744177664), (-473715743/281474976710656)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((486700533/36028797018963968), (578409971/18014398509481984)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-178560249/288230376151711744), (-578888029/1152921504606846976)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((708456415/36893488147419103232), (272474615/73786976294838206464)), (31/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-567600857/1180591620717411303424), (352180993/2361183241434822606848)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((713556301/75557863725914323419136), (-722037965/75557863725914323419136)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-254369849/2417851639229258349412352), (427261051/1208925819614629174706176)), (35/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-318972685/154742504910672534362390528), (-1569266767/154742504910672534362390528)), (377/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((932221507/4951760157141521099596496896), (70583963/309485009821345068724781056)), (251/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((419845288331113/4194304), (-630242630687669/4194304)), (232527377/2097152), by norm_num⟩
  | 1 => ⟨(171033549, (-705929403/4)), (713/4), by norm_num⟩
  | 2 => ⟨((545497493/4), (-788759935/8)), (577/4), by norm_num⟩
  | 3 => ⟨((1109529133/16), (-546080221/16)), (1255/16), by norm_num⟩
  | 4 => ⟨((1640335905/64), (-498075795/64)), (2061/64), by norm_num⟩
  | 5 => ⟨((947255647/128), (-131417719/128)), (341/32), by norm_num⟩
  | 6 => ⟨((447197105/256), (6184717/256)), (3031/1024), by norm_num⟩
  | 7 => ⟨((712062165/2048), (28837909/512)), (1455/2048), by norm_num⟩
  | 8 => ⟨((488675449/8192), (76326307/4096)), (1233/8192), by norm_num⟩
  | 9 => ⟨((587600837/65536), (554180729/131072)), (1873/65536), by norm_num⟩
  | 10 => ⟨((1252684513/1048576), (405414223/524288)), (5165/1048576), by norm_num⟩
  | 11 => ⟨((596798127/4194304), (507247409/4194304)), (3265/4194304), by norm_num⟩
  | 12 => ⟨((1021809183/67108864), (1119267613/67108864)), (7631/67108864), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804370196421151/5070602400912917605986812821504), (-1280651486327/10141204801825835211973625643008)), (388209/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((226479909995719/79228162514264337593543950336), (-784163313819/316912650057057350374175801344)), (476159/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((963491510438977/19807040628566084398385987584), (-884331317965/19807040628566084398385987584)), (537069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((964560289942597/1237940039285380274899124224), (-941465729265/1237940039285380274899124224)), (142957/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1810826028827611/154742504910672534362390528), (-471776308647/38685626227668133590597632)), (573163/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1586753287357305/9671406556917033397649408), (-221701029719/1208925819614629174706176)), (538761/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1291380385109531/604462909807314587353088), (-1556369032005/604462909807314587353088)), (472843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1940832174622841/75557863725914323419136), (-2537497075821/75557863725914323419136)), (771055/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1337388536725823/4722366482869645213696), (-1910502149151/4722366482869645213696)), (145163/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((838176540131749/295147905179352825856), (-2638991467497/590295810358705651712)), (802251/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1892275195643457/73786976294838206464), (-103653772407/2305843009213693952)), (126079/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1900291486329297/9223372036854775808), (-3756706738081/9223372036854775808)), (571385/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1671834034949089/1152921504606846976), (-3788429682767/1152921504606846976)), (1152931/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1263030954215769/144115188075855872), (-1675462023959/72057594037927936)), (510183/72057594037927936), by norm_num⟩
  | 4 => ⟨((398746103865579/9007199254740992), (-1274847870013/9007199254740992)), (1553959/36028797018963968), by norm_num⟩
  | 3 => ⟨((1619629807809689/9007199254740992), (-3252036019771/4503599627370496)), (992057/4503599627370496), by norm_num⟩
  | 2 => ⟨((1246154703461761/2251799813685248), (-6703036950027/2251799813685248)), (2048037/2251799813685248), by norm_num⟩
  | 1 => ⟨((1310936652142687/1125899906842624), (-5283520447667/562949953421312)), (1618479/562949953421312), by norm_num⟩
  | 0 => ⟨((1515157840654435/1125899906842624), (-23277056808603/1125899906842624)), (7165011/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1515157840654435/1125899906842624), (-23277056808603/1125899906842624)), (27332347874168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2038512879141531/1125899906842624), (-31324645216303/562949953421312)), (9790305/562949953421312), by norm_num⟩
  | 2 => ⟨((921842563358185/281474976710656), (-3544703014889/17592186044416)), (18270735/281474976710656), by norm_num⟩
  | 3 => ⟨((187977875984139/17592186044416), (-46436214711161/35184372088832)), (63518865/140737488355328), by norm_num⟩
  | 4 => ⟨((988978892744771/8796093022208), (-124046280946963/4398046511104)), (95318807/8796093022208), by norm_num⟩
  | 5 => ⟨((814041572840891/68719476736), (-435843907027455/68719476736)), (104730607/34359738368), by norm_num⟩
  | 6 => ⟨((419845288331113/4194304), (-630242630687669/4194304)), (232527377/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((637920711/33554432), (299748695/16777216)), (5/16777216), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((114688/4292403), (-601600/4292403)), 0, by norm_num⟩
  | 1 => ⟨((58128203776/6141574504803), (68996300800/18424723514409)), 0, by norm_num⟩
  | 2 => ⟨((-26722677/68719476736), (674257017/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-166152477/4398046511104), (-2435633/68719476736)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((841176647/281474976710656), (-305953401/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((506290327/4503599627370496), (536976829/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-656188103/36028797018963968), (84528253/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-98583447/1152921504606846976), (-1543756317/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1751988597/18446744073709551616), (219443557/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-310268455/147573952589676412928), (958743899/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1008658807/2361183241434822606848), (-276408271/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((208859929/9444732965739290427392), (-1012780421/37778931862957161709568)), (25/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((956990835/604462909807314587353088), (288302051/151115727451828646838272)), (35/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (3525/512)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (3525/512)))⁻¹=value ((114688/4292403), (-601600/4292403)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((114688/4292403), (-601600/4292403))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((606208/13827481), (-1804800/13827481)), 0, by norm_num⟩
  | 1 => ⟨((1444907450368/191199230805361), (1094084198400/191199230805361)), 0, by norm_num⟩
  | 2 => ⟨((-1185480309/2199023255552), (25271701/68719476736)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-428644415/35184372088832), (-1521487187/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((108690359/35184372088832), (86043301/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-349887125/4503599627370496), (892850873/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-809583687/72057594037927936), (-21202879/2251799813685248)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((992411387/1152921504606846976), (-607387149/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((71539365/4611686018427387904), (624642195/9223372036854775808)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-702421333/147573952589676412928), (-139356811/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((638229355/4722366482869645213696), (-1418034611/4722366482869645213696)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((157105197/9444732965739290427392), (581884803/37778931862957161709568)), (13/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-827997175/604462909807314587353088), (113025737/151115727451828646838272)), (37/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (3525/512)))⁻¹=value ((606208/13827481), (-1804800/13827481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((606208/13827481), (-1804800/13827481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1016242896896/59353120926843), (-571683635200/59353120926843)), 0, by norm_num⟩
  | 1 => ⟨((1048730329/549755813888), (-1087116549/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((330354645/2199023255552), (269909801/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-112571925/4398046511104), (274443091/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((-14173113/140737488355328), (-1309856905/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((1712354903/9007199254740992), (362205569/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-502792519/72057594037927936), (1016605139/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-545497417/576460752303423488), (-936369167/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((45807223/576460752303423488), (-16091263/288230376151711744)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((196076439/73786976294838206464), (1028422305/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1327773485/2361183241434822606848), (156200763/2361183241434822606848)), (25/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((207018929/37778931862957161709568), (-199333153/4722366482869645213696)), (19/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((892494005/302231454903657293676544), (87638157/75557863725914323419136)), (7/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((53/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((868352/15302041), (-1804800/15302041)), 0, by norm_num⟩
  | 1 => ⟨((1251633922048/234152458765681), (1567201689600/234152458765681)), 0, by norm_num⟩
  | 2 => ⟨((-1201494301/2199023255552), (137793931/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((285420229/35184372088832), (-78674609/2199023255552)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((66135809/35184372088832), (840778035/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-318428475/2251799813685248), (308376965/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-926083/36028797018963968), (-185227471/18014398509481984)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((174983519/288230376151711744), (334610417/1152921504606846976)), (17/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-633481003/18446744073709551616), (508523743/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-384470705/590295810358705651712), (-1657174097/590295810358705651712)), (37/590295810358705651712), by norm_num⟩
  | 10 => ⟨((869092879/4722366482869645213696), (389552067/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-289166739/37778931862957161709568), (731617263/75557863725914323419136)), (19/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-427773421/1208925819614629174706176), (-877831957/1208925819614629174706176)), (27/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (3525/512)))⁻¹=value ((868352/15302041), (-1804800/15302041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((868352/15302041), (-1804800/15302041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-36209399/17179869184), (12651827/8589934592)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-83581619/549755813888), (-1106759433/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1257362611/17592186044416), (26852125/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-373021511/140737488355328), (268568267/35184372088832)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((-184391313/281474976710656), (-277561085/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((284603813/4503599627370496), (-100842781/2251799813685248)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((304939003/144115188075855872), (954187383/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1383472145/2305843009213693952), (5628399/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((273096337/18446744073709551616), (-221325185/4611686018427387904)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((499228267/147573952589676412928), (341903593/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-606170861/2361183241434822606848), (481303043/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-355284299/37778931862957161709568), (-452685349/18889465931478580854784)), (27/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1199549237/604462909807314587353088), (-94956835/604462909807314587353088)), (41/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((69/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((376832/5766963), (-601600/5766963)), 0, by norm_num⟩
  | 1 => ⟨((36653367296/11085954081123), (226702131200/33257862243369)), 0, by norm_num⟩
  | 2 => ⟨((-1019389433/2199023255552), (-13813357/274877906944)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((625104733/35184372088832), (-792961097/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((334992167/562949953421312), (936196225/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-478207623/4503599627370496), (-52456521/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((675071773/144115188075855872), (-344243741/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((221683993/2305843009213693952), (115410363/288230376151711744)), (15/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-443203549/18446744073709551616), (-297636663/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 9 => ⟨((355878667/295147905179352825856), (-146039949/147573952589676412928)), (31/590295810358705651712), by norm_num⟩
  | 10 => ⟨((230880881/18889465931478580854784), (899361853/9444732965739290427392)), (85/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-810905487/151115727451828646838272), (-46724655/18889465931478580854784)), (59/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((367924369/1208925819614629174706176), (-481337549/2417851639229258349412352)), (81/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (3525/512)))⁻¹=value ((376832/5766963), (-601600/5766963)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((376832/5766963), (-601600/5766963))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((68399/4294967296), (1390266081/4398046511104)), (3/4398046511104), by norm_num⟩
  | 1 => ⟨((-1397624075/17592186044416), (-466618769/17592186044416)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((77481195/8796093022208), (-748260383/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((250492515/281474976710656), (445329773/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-231752425/1125899906842624), (277851665/9007199254740992)), (13/9007199254740992), by norm_num⟩
  | 5 => ⟨((329569263/72057594037927936), (-1532146733/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 6 => ⟨((1031043295/576460752303423488), (660137977/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 7 => ⟨((-11321431/72057594037927936), (547063287/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-46976937/9223372036854775808), (-154501671/9223372036854775808)), (23/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1774270909/1180591620717411303424), (5911541/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-230407877/4722366482869645213696), (1094372641/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-142883041/18889465931478580854784), (-522519875/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((435893341/604462909807314587353088), (-466504729/1208925819614629174706176)), (21/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((85/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((278528/3964805), (-72192/792961)), 0, by norm_num⟩
  | 1 => ⟨((26357137408/15719678688025), (20107493376/3143935737605)), 0, by norm_num⟩
  | 2 => ⟨((-769717809/2199023255552), (-40770779/274877906944)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((670138229/35184372088832), (-754603213/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-12727353/70368744177664), (1400249069/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-905396593/18014398509481984), (-935256323/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((1190007427/288230376151711744), (-133811133/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-285663403/2305843009213693952), (941918159/4611686018427387904)), (17/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-45617443/9223372036854775808), (-945472385/73786976294838206464)), (23/73786976294838206464), by norm_num⟩
  | 9 => ⟨((223427681/295147905179352825856), (132780255/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-173920373/4722366482869645213696), (125417409/4722366482869645213696)), (39/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((51186791/604462909807314587353088), (-1577246727/604462909807314587353088)), (51/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((559993265/4835703278458516698824704), (923694881/9671406556917033397649408)), (133/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (3525/512)))⁻¹=value ((278528/3964805), (-72192/792961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((278528/3964805), (-72192/792961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1051933109/35184372088832), (730318257/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-703046203/70368744177664), (422308705/70368744177664)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-19107083/70368744177664), (-623335113/281474976710656)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1427192109/4503599627370496), (430319831/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-488772683/18014398509481984), (576028053/18014398509481984)), (15/36028797018963968), by norm_num⟩
  | 5 => ⟨((-610190749/288230376151711744), (-1230266553/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((1149605143/2305843009213693952), (-66474137/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-151608075/9223372036854775808), (854912343/18446744073709551616)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1007965301/295147905179352825856), (-911764209/295147905179352825856)), (31/295147905179352825856), by norm_num⟩
  | 9 => ⟨((881778217/2361183241434822606848), (-210316255/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((9980041/4722366482869645213696), (676975877/18889465931478580854784)), (3/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-108297467/37778931862957161709568), (-145041421/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((386634949/2417851639229258349412352), (-229135915/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((101/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((1654784/22871449), (-1804800/22871449)), 0, by norm_num⟩
  | 1 => ⟨((259496476672/523103179359601), (2986554163200/523103179359601)), 0, by norm_num⟩
  | 2 => ⟨((-66852511/274877906944), (-822283805/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1138216039/70368744177664), (-49824959/17592186044416)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-532998271/1125899906842624), (208473935/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-435839825/36028797018963968), (-1638285433/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((1286494203/576460752303423488), (168280095/144115188075855872)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-292392291/2305843009213693952), (52816763/1152921504606846976)), (15/9223372036854775808), by norm_num⟩
  | 8 => ⟨((410221421/147573952589676412928), (-982899195/147573952589676412928)), (19/147573952589676412928), by norm_num⟩
  | 9 => ⟨((383048271/2361183241434822606848), (827880553/2361183241434822606848)), (3/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1488682923/75557863725914323419136), (-474749439/75557863725914323419136)), (59/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((580684935/604462909807314587353088), (-664992293/1208925819614629174706176)), (9/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-252415381/19342813113834066795298816), (279515211/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (3525/512)))⁻¹=value ((1654784/22871449), (-1804800/22871449)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((1654784/22871449), (-1804800/22871449))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((534955257/140737488355328), (-241352407/281474976710656)), (7/281474976710656), by norm_num⟩
  | 1 => ⟨((-198698947/562949953421312), (790149343/562949953421312)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((-533689673/2251799813685248), (-229120893/1125899906842624)), (13/4503599627370496), by norm_num⟩
  | 3 => ⟨((423979417/9007199254740992), (-180891197/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 4 => ⟨((-100960605/288230376151711744), (507160321/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 5 => ⟨((-435235289/576460752303423488), (-236464385/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((712916493/9223372036854775808), (-519991197/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 7 => ⟨((139902963/73786976294838206464), (1437280017/147573952589676412928)), (17/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-557073427/590295810358705651712), (-136676193/590295810358705651712)), (33/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((265572479/4722366482869645213696), (-672622423/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((567654137/151115727451828646838272), (1091266647/151115727451828646838272)), (27/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-1702061243/2417851639229258349412352), (105742073/2417851639229258349412352)), (23/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((393699075/19342813113834066795298816), (-1077175253/19342813113834066795298816)), (19/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((117/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((212992/2938129), (-601600/8814387)), 0, by norm_num⟩
  | 1 => ⟨((-23183884288/77693418185769), (128135987200/25897806061923)), 0, by norm_num⟩
  | 2 => ⟨((-695028815/4398046511104), (-833520243/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((214547537/17592186044416), (207787737/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-1108851625/2251799813685248), (816667577/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((24644069/4503599627370496), (-1079068681/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((474852733/576460752303423488), (733442691/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1351714869/18446744073709551616), (-332149469/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((965271419/295147905179352825856), (-17044751/9223372036854775808)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-261983831/4722366482869645213696), (843371423/4722366482869645213696)), (13/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-617119929/151115727451828646838272), (-1264303137/151115727451828646838272)), (15/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((262055567/604462909807314587353088), (99065315/604462909807314587353088)), (69/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-12879223/604462909807314587353088), (21408697/2417851639229258349412352)), (79/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (3525/512)))⁻¹=value ((212992/2938129), (-601600/8814387)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((212992/2938129), (-601600/8814387))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((488700605/2251799813685248), (-724158411/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 1 => ⟨((165099719/2251799813685248), (1305164421/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((-696669111/18014398509481984), (-47779873/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 3 => ⟨((125690095/36028797018963968), (-214020061/36028797018963968)), (15/144115188075855872), by norm_num⟩
  | 4 => ⟨((612491941/1152921504606846976), (1001302243/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-151751823/1152921504606846976), (38944735/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 6 => ⟨((115071817/18446744073709551616), (-1044848877/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 7 => ⟨((625307465/590295810358705651712), (384507367/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1577927197/9444732965739290427392), (86315281/2361183241434822606848)), (59/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((304060613/75557863725914323419136), (-1210996231/75557863725914323419136)), (7/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((704970763/604462909807314587353088), (595622979/604462909807314587353088)), (51/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1198737573/9671406556917033397649408), (267419603/4835703278458516698824704)), (45/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((10832495/38685626227668133590597632), (-1804366827/154742504910672534362390528)), (19/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((133/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((2179072/30539161), (-1804800/30539161)), 0, by norm_num⟩
  | 1 => ⟨((-745525870592/932640354583921), (3932789145600/932640354583921)), 0, by norm_num⟩
  | 2 => ⟨((-422582207/4398046511104), (-765538119/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1206309631/140737488355328), (474400099/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-228220601/562949953421312), (299522479/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((758977401/72057594037927936), (-1205141797/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((68262977/576460752303423488), (1046759119/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-286411371/9223372036854775808), (-66621393/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 8 => ⟨((144740605/73786976294838206464), (8353341/73786976294838206464)), (27/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-692569249/9444732965739290427392), (127325207/2361183241434822606848)), (29/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((309096703/302231454903657293676544), (-1236315381/302231454903657293676544)), (61/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((102017081/1208925819614629174706176), (425928919/2417851639229258349412352)), (65/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-1271360813/154742504910672534362390528), (-146667795/38685626227668133590597632)), (17/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (3525/512)))⁻¹=value ((2179072/30539161), (-1804800/30539161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((2179072/30539161), (-1804800/30539161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-126812807/36028797018963968), (-1288837067/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((1079249261/72057594037927936), (64658259/9007199254740992)), (17/72057594037927936), by norm_num⟩
  | 2 => ⟨((-1033099327/288230376151711744), (342609059/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 3 => ⟨((-51310779/1152921504606846976), (-1892527037/2305843009213693952)), (5/288230376151711744), by norm_num⟩
  | 4 => ⟨((132669901/1152921504606846976), (539941369/9223372036854775808)), (29/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-271682803/18446744073709551616), (715216839/73786976294838206464)), (19/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-11268255/73786976294838206464), (-637535279/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1047664357/4722366482869645213696), (485952067/4722366482869645213696)), (47/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-195659339/9444732965739290427392), (580512601/37778931862957161709568)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-226678663/604462909807314587353088), (-1536413977/604462909807314587353088)), (23/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((1111909247/4835703278458516698824704), (391627691/4835703278458516698824704)), (43/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-156408935/9671406556917033397649408), (587091909/38685626227668133590597632)), (77/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-41825943/77371252455336267181195264), (-578075673/309485009821345068724781056)), (133/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((149/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((2441216/35159449), (-1804800/35159449)), 0, by norm_num⟩
  | 1 => ⟨((-1351116259328/1236186853983601), (4405906636800/1236186853983601)), 0, by norm_num⟩
  | 2 => ⟨((-117718659/2199023255552), (-1335115443/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((809824533/140737488355328), (548238543/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1349926743/4503599627370496), (56065777/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((45425559/4503599627370496), (-73187053/9007199254740992)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-326555141/2305843009213693952), (1247377009/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-41356575/4611686018427387904), (-826971647/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 8 => ⟨((523375913/590295810358705651712), (80871213/147573952589676412928)), (23/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-105888981/2361183241434822606848), (35243431/9444732965739290427392)), (23/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((883184857/604462909807314587353088), (-774046769/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-172709281/9671406556917033397649408), (396318769/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-459134189/309485009821345068724781056), (-1022407445/309485009821345068724781056)), (43/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (3525/512)))⁻¹=value ((2441216/35159449), (-1804800/35159449)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((2441216/35159449), (-1804800/35159449))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-149926729/72057594037927936), (-663823353/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 1 => ⟨((1775228131/1152921504606846976), (-281141021/1152921504606846976)), (37/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-12540199/72057594037927936), (915505885/2305843009213693952)), (25/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-113838341/2305843009213693952), (-336435905/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((537949357/36893488147419103232), (-10638719/18446744073709551616)), (37/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-600002879/590295810358705651712), (538138707/295147905179352825856)), (49/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-157009157/1180591620717411303424), (-273336621/1180591620717411303424)), (59/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((147551905/4722366482869645213696), (14402169/37778931862957161709568)), (65/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-32945603/18889465931478580854784), (882218117/302231454903657293676544)), (17/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-413167049/2417851639229258349412352), (-733419605/2417851639229258349412352)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1309127687/38685626227668133590597632), (-339837/9671406556917033397649408)), (127/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-234865291/154742504910672534362390528), (852204845/309485009821345068724781056)), (117/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-749685635/4951760157141521099596496896), (-1171053921/4951760157141521099596496896)), (205/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((165/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((180224/2686935), (-24064/537387)), 0, by norm_num⟩
  | 1 => ⟨((-1000210432/802179966025), (4336910336/1443923938845)), 0, by norm_num⟩
  | 2 => ⟨((-111855093/4398046511104), (-565798727/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((525421717/140737488355328), (1054133189/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-941505507/4503599627370496), (-47297473/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((286490319/36028797018963968), (-471528391/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-445996435/2305843009213693952), (10367891/36028797018963968)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((806159/18446744073709551616), (-2063305939/147573952589676412928)), (29/147573952589676412928), by norm_num⟩
  | 8 => ⟨((367846125/1180591620717411303424), (1109467035/2361183241434822606848)), (27/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-396110027/18889465931478580854784), (-331780547/37778931862957161709568)), (25/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1087912599/1208925819614629174706176), (-211542741/1208925819614629174706176)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-253992207/9671406556917033397649408), (1006486411/38685626227668133590597632)), (83/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((184601477/618970019642690137449562112), (-904031921/618970019642690137449562112)), (75/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (3525/512)))⁻¹=value ((180224/2686935), (-24064/537387)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((180224/2686935), (-24064/537387))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-559605067/2305843009213693952), (-282732043/4611686018427387904)), (37/4611686018427387904), by norm_num⟩
  | 1 => ⟨((939591565/9223372036854775808), (-408982489/4611686018427387904)), (37/9223372036854775808), by norm_num⟩
  | 2 => ⟨((43123199/9223372036854775808), (1463898341/36893488147419103232)), (51/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-562510041/73786976294838206464), (-576799617/147573952589676412928)), (13/36893488147419103232), by norm_num⟩
  | 4 => ⟨((764652973/590295810358705651712), (-431640851/590295810358705651712)), (21/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-64234127/4722366482869645213696), (1045238267/4722366482869645213696)), (57/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-56166597/2361183241434822606848), (-653636193/37778931862957161709568)), (71/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((996750063/302231454903657293676544), (-25046233/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-81227971/1208925819614629174706176), (474141815/1208925819614629174706176)), (43/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-610709759/19342813113834066795298816), (-132264189/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((609606613/154742504910672534362390528), (-404598113/309485009821345068724781056)), (21/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-50350721/618970019642690137449562112), (476249351/1237940039285380274899124224)), (157/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-1054940479/39614081257132168796771975168), (-943069385/39614081257132168796771975168)), (35/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((181/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((2965504/45972889), (-1804800/45972889)), 0, by norm_num⟩
  | 1 => ⟨((-2768455467008/2113506523006321), (5352141619200/2113506523006321)), 0, by norm_num⟩
  | 2 => ⟨((-131237033/17592186044416), (-1889172509/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((661043945/281474976710656), (233419833/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-19823819/140737488355328), (-548419807/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1653912295/288230376151711744), (-230902241/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((-97621691/576460752303423488), (638588961/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((404918565/147573952589676412928), (-574815151/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 8 => ⟨((152100973/2361183241434822606848), (1440859733/4722366482869645213696)), (3/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-152375707/18889465931478580854784), (-648008287/75557863725914323419136)), (21/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((518045917/1208925819614629174706176), (285956521/2417851639229258349412352)), (9/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-312238703/19342813113834066795298816), (355664691/77371252455336267181195264)), (61/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((532814347/1237940039285380274899124224), (-575789563/1237940039285380274899124224)), (13/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (3525/512)))⁻¹=value ((2965504/45972889), (-1804800/45972889)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((2965504/45972889), (-1804800/45972889))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1332714825/73786976294838206464), (411201461/73786976294838206464)), (31/36893488147419103232), by norm_num⟩
  | 1 => ⟨((262889987/73786976294838206464), (-756619359/73786976294838206464)), (67/147573952589676412928), by norm_num⟩
  | 2 => ⟨((574261605/295147905179352825856), (409757741/147573952589676412928)), (3/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-1800284915/2361183241434822606848), (-9928495/2361183241434822606848)), (101/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((751100041/9444732965739290427392), (-266465069/2361183241434822606848)), (85/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((563820325/75557863725914323419136), (756043429/37778931862957161709568)), (15/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-1720991809/604462909807314587353088), (-411748179/604462909807314587353088)), (153/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((642864805/2417851639229258349412352), (-300923535/1208925819614629174706176)), (89/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((142622539/19342813113834066795298816), (199154355/4835703278458516698824704)), (195/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1286408703/309485009821345068724781056), (-528727075/309485009821345068724781056)), (203/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((229261703/618970019642690137449562112), (-657284329/2475880078570760549798248448)), (199/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((61808425/19807040628566084398385987584), (868383683/19807040628566084398385987584)), (47/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-286300643/79228162514264337593543950336), (-584059513/316912650057057350374175801344)), (171/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((197/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((3227648/52166041), (-1804800/52166041)), 0, by norm_num⟩
  | 1 => ⟨((-3580204285952/2721295833613681), (5825259110400/2721295833613681)), 0, by norm_num⟩
  | 2 => ⟨((8072203/2199023255552), (-782687945/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((401296555/281474976710656), (792704519/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-418037035/4503599627370496), (-562606967/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((569557633/144115188075855872), (47072887/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1179795079/9223372036854775808), (134340715/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((870491433/295147905179352825856), (-1185050579/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-51440411/2361183241434822606848), (413754923/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-356224599/151115727451828646838272), (-876153069/151115727451828646838272)), (13/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((418823989/2417851639229258349412352), (335083821/2417851639229258349412352)), (41/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-300053545/38685626227668133590597632), (-199755447/154742504910672534362390528)), (65/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((162342683/618970019642690137449562112), (-58329375/618970019642690137449562112)), (101/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (3525/512)))⁻¹=value ((3227648/52166041), (-1804800/52166041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((3227648/52166041), (-1804800/52166041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-545856711/590295810358705651712), (71550327/73786976294838206464)), (49/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-72304925/590295810358705651712), (-948849335/1180591620717411303424)), (7/147573952589676412928), by norm_num⟩
  | 2 => ⟨((1105694023/4722366482869645213696), (75101545/590295810358705651712)), (83/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-536125735/9444732965739290427392), (123881165/4722366482869645213696)), (91/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((21896501/9444732965739290427392), (-1741961381/151115727451828646838272)), (157/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((774772859/604462909807314587353088), (416101039/302231454903657293676544)), (115/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-1272736809/4835703278458516698824704), (86891407/2417851639229258349412352)), (151/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((297098031/19342813113834066795298816), (-585404467/19342813113834066795298816)), (45/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((597131925/309485009821345068724781056), (135208133/38685626227668133590597632)), (201/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-540281099/1237940039285380274899124224), (-90725635/2475880078570760549798248448)), (213/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((275991469/9903520314283042199192993792), (-706245299/19807040628566084398385987584)), (213/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((3626083/2475880078570760549798248448), (663903175/158456325028528675187087900672)), (51/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-1027131333/2535301200456458802993406410752), (-236519229/2535301200456458802993406410752)), (377/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29215999/549755813888), (1038001171/4398046511104)), (127/549755813888), by norm_num⟩
  | 1 => ⟨((-263997477/2199023255552), (587140699/2199023255552)), (2117/4398046511104), by norm_num⟩
  | 2 => ⟨((-662947167/4398046511104), (187186395/2199023255552)), (1141/2199023255552), by norm_num⟩
  | 3 => ⟨((-1164895463/17592186044416), (-125433269/17592186044416)), (421/1099511627776), by norm_num⟩
  | 4 => ⟨((-31189291/2199023255552), (-53810819/4398046511104)), (15191/70368744177664), by norm_num⟩
  | 5 => ⟨((-315423407/281474976710656), (-138988795/35184372088832)), (27793/281474976710656), by norm_num⟩
  | 6 => ⟨((225874671/1125899906842624), (-792027759/1125899906842624)), (21437/562949953421312), by norm_num⟩
  | 7 => ⟨((175960249/2251799813685248), (-344319469/4503599627370496)), (28665/2251799813685248), by norm_num⟩
  | 8 => ⟨((485438697/36028797018963968), (-298740615/72057594037927936)), (271255/72057594037927936), by norm_num⟩
  | 9 => ⟨((460594513/288230376151711744), (244237025/1152921504606846976)), (288315/288230376151711744), by norm_num⟩
  | 10 => ⟨((1341118391/9223372036854775808), (768571847/9223372036854775808)), (17425/72057594037927936), by norm_num⟩
  | 11 => ⟨((379903645/36893488147419103232), (914607951/73786976294838206464)), (3963553/73786976294838206464), by norm_num⟩
  | 12 => ⟨((298318429/590295810358705651712), (797804273/590295810358705651712)), (6525349/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29215999/549755813888), (1038001171/4398046511104)), (1017/4398046511104), by norm_num⟩
  | 1 => ⟨((-263997477/2199023255552), (587140699/2199023255552)), (1059/2199023255552), by norm_num⟩
  | 2 => ⟨((-662947167/4398046511104), (187186395/2199023255552)), (4565/8796093022208), by norm_num⟩
  | 3 => ⟨((-1164895463/17592186044416), (-125433269/17592186044416)), (6737/17592186044416), by norm_num⟩
  | 4 => ⟨((-31189291/2199023255552), (-53810819/4398046511104)), (7597/35184372088832), by norm_num⟩
  | 5 => ⟨((-315423407/281474976710656), (-138988795/35184372088832)), (27805/281474976710656), by norm_num⟩
  | 6 => ⟨((225874671/1125899906842624), (-792027759/1125899906842624)), (85839/2251799813685248), by norm_num⟩
  | 7 => ⟨((175960249/2251799813685248), (-344319469/4503599627370496)), (115021/9007199254740992), by norm_num⟩
  | 8 => ⟨((485438697/36028797018963968), (-298740615/72057594037927936)), (137069/36028797018963968), by norm_num⟩
  | 9 => ⟨((460594513/288230376151711744), (244237025/1152921504606846976)), (1199377/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1341118391/9223372036854775808), (768571847/9223372036854775808)), (2599335/9223372036854775808), by norm_num⟩
  | 11 => ⟨((379903645/36893488147419103232), (914607951/73786976294838206464)), (6915033/73786976294838206464), by norm_num⟩
  | 12 => ⟨((298318429/590295810358705651712), (797804273/590295810358705651712)), (15068591/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile037Gamma
