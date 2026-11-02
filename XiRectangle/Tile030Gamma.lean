/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile030Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (1551/128))
  have he : value ((7/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((880640/14239201), (-397056/14239201)), 0, by norm_num⟩
  | 1 => ⟨((-308936671232/202754845118401), (349663395840/202754845118401)), 0, by norm_num⟩
  | 2 => ⟨((405902825/17592186044416), (-5247586887/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((183653227/562949953421312), (5917073043/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-841715449/18014398509481984), (-2763710543/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((2898864271/1152921504606846976), (1983726715/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-3753588619/36893488147419103232), (-669630429/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((4013080297/1180591620717411303424), (-506029259/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-3519562791/37778931862957161709568), (1395964183/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2237109643/1208925819614629174706176), (-541624115/151115727451828646838272)), (27/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-280518435/38685626227668133590597632), (5285762527/38685626227668133590597632)), (5/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-2080687501/1237940039285380274899124224), (-1338905305/309485009821345068724781056)), (29/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((2224179955/19807040628566084398385987584), (1092821097/9903520314283042199192993792)), (21/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (1551/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (1551/256)))⁻¹=value ((880640/14239201), (-397056/14239201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((880640/14239201), (-397056/14239201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5777970609/2147483648), (454814405/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((440320/14239201), (-198528/14239201)), 0, by norm_num⟩
  | 2 => ⟨((-77234167808/202754845118401), (87415848960/202754845118401)), 0, by norm_num⟩
  | 3 => ⟨((1082407533/281474976710656), (-1749195629/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((183653227/4503599627370496), (5917073043/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2693489437/576460752303423488), (-4421936869/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((3865152361/18446744073709551616), (2644968953/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-4289815565/590295810358705651712), (-765291919/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((4013080297/18889465931478580854784), (-506029259/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-3128500259/604462909807314587353088), (2481714103/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((894843857/9671406556917033397649408), (-108324823/604462909807314587353088)), (11/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-408026815/1237940039285380274899124224), (7688381857/1237940039285380274899124224)), (15/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-1387125001/19807040628566084398385987584), (-3570414147/19807040628566084398385987584)), (5/2475880078570760549798248448), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (33/4096)), 0, by norm_num⟩
  | 45 => ⟨((18933248341/816127672320), (-130383/12058624)), 0, by norm_num⟩
  | 44 => ⟨((-51361581774781/2298215525253120), (249320730791/23708219473920)), 0, by norm_num⟩
  | 43 => ⟨((392610995/17179869184), (-1394559143/137438953472)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-1623661083/68719476736), (1412682623/137438953472)), (1/137438953472), by norm_num⟩
  | 41 => ⟨((834329789/34359738368), (-1455887813/137438953472)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-427397101/17179869184), (374221461/34359738368)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3504864315/137438953472), (-767224163/68719476736)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-3597103051/137438953472), (393227701/34359738368)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3695063123/137438953472), (-1613998125/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-1899188113/68719476736), (414418071/34359738368)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((3907463251/137438953472), (-1703787731/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-2011483483/68719476736), (1752480531/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((4145522101/137438953472), (-1804015867/137438953472)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-1068946529/34359738368), (1858676559/137438953472)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((68976533/2147483648), (-958378429/68719476736)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4562504717/137438953472), (1978583757/137438953472)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4720773205/137438953472), (-2044530215/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-2445204631/68719476736), (264377779/17179869184)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5072682439/137438953472), (-547636679/34359738368)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-329316147/8589934592), (567915595/34359738368)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5481238297/137438953472), (-1179506839/68719476736)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-5711208537/137438953472), (306668505/17179869184)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((5961302471/137438953472), (-1277768647/68719476736)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-779284983/17179869184), (1333302319/68719476736)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((3266714409/68719476736), (-1393879481/68719476736)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-1715674611/34359738368), (1460219479/68719476736)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((3613436801/68719476736), (-766592605/34359738368)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-1907952025/34359738368), (1613820795/68719476736)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((2021185129/34359738368), (-1703401763/68719476736)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4297364453/68719476736), (1803502887/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((4586630017/68719476736), (-479022837/17179869184)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-4917560325/68719476736), (1021828501/34359738368)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5299836145/68719476736), (-2189398207/68719476736)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-5746382801/68719476736), (2357492941/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1568712757/17179869184), (-1276752331/34359738368)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-3454994411/34359738368), (1392504029/34359738368)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((3843799143/34359738368), (-1531293695/34359738368)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-1082683213/8589934592), (1700747347/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((309882463/2147483648), (-956134877/17179869184)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-2898296387/17179869184), (1091856953/17179869184)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3486709261/17179869184), (-1272342739/17179869184)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4371597591/17179869184), (1524058325/17179869184)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((2924829299/8589934592), (-1899445831/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-2201886453/4294967296), (1259626093/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((4409126837/4294967296), (-934639465/4294967296)), (1/2147483648), by norm_num⟩
  | 0 => ⟨((-704473337/8589934592), (3638515241/8589934592)), (3/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (1551/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (1551/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (1551/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5777970609/2147483648), (454814405/1073741824)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (1551/256))) (z:=((-41/256), (1551/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5777970609/2147483648), (454814405/1073741824))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((2163794479/67108864), (2923418709/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((3929523721/2147483648), (469784895/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((1606068329984/202754845118401), (-750427948512/202754845118401)), 0, by norm_num⟩
  | 3 => ⟨((-1150705943/17592186044416), (2746884767/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((1036494225/2251799813685248), (-967052081/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((115547063/18014398509481984), (165200017/4503599627370496)), (19/72057594037927936), by norm_num⟩
  | 6 => ⟨((-284850459/576460752303423488), (-1639289517/2305843009213693952)), (63/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2744885435/147573952589676412928), (1607072319/147573952589676412928)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-5293085643/9444732965739290427392), (-512277287/9444732965739290427392)), (195/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4349307549/302231454903657293676544), (-760018049/151115727451828646838272)), (129/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1475111071/4835703278458516698824704), (1425984931/4835703278458516698824704)), (173/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((84537151/19342813113834066795298816), (-3482061797/309485009821345068724781056)), (231/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((421544615/19807040628566084398385987584), (863849371/2475880078570760549798248448)), (1241/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((1262019119/67108864), (2110248021/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((2855781897/2147483648), (469784895/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((1606068329984/202754845118401), (-750427948512/202754845118401)), 0, by norm_num⟩
  | 3 => ⟨((-1150705943/17592186044416), (2746884767/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((1036494225/2251799813685248), (-967052081/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((115547063/18014398509481984), (165200017/4503599627370496)), (19/72057594037927936), by norm_num⟩
  | 6 => ⟨((-284850459/576460752303423488), (-1639289517/2305843009213693952)), (63/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2744885435/147573952589676412928), (1607072319/147573952589676412928)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-5293085643/9444732965739290427392), (-512277287/9444732965739290427392)), (195/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4349307549/302231454903657293676544), (-760018049/151115727451828646838272)), (129/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1475111071/4835703278458516698824704), (1425984931/4835703278458516698824704)), (173/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((84537151/19342813113834066795298816), (-3482061797/309485009821345068724781056)), (231/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((421544615/19807040628566084398385987584), (863849371/2475880078570760549798248448)), (1241/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((3946810947/2147483648), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((3946810947/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((165461005/8388608), (2110248021/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((2855781897/2147483648), (469784895/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((1606068329984/202754845118401), (-750427948512/202754845118401)), 0, by norm_num⟩
  | 3 => ⟨((-1150705943/17592186044416), (2746884767/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((1036494225/2251799813685248), (-967052081/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((115547063/18014398509481984), (165200017/4503599627370496)), (19/72057594037927936), by norm_num⟩
  | 6 => ⟨((-284850459/576460752303423488), (-1639289517/2305843009213693952)), (63/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2744885435/147573952589676412928), (1607072319/147573952589676412928)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-5293085643/9444732965739290427392), (-512277287/9444732965739290427392)), (195/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4349307549/302231454903657293676544), (-760018049/151115727451828646838272)), (129/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1475111071/4835703278458516698824704), (1425984931/4835703278458516698824704)), (173/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((84537151/19342813113834066795298816), (-3482061797/309485009821345068724781056)), (231/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((421544615/19807040628566084398385987584), (863849371/2475880078570760549798248448)), (1241/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((617873342464/202754845118401), (-699326791680/202754845118401)), 0, by norm_num⟩
  | 1 => ⟨((-405902825/4398046511104), (5247586887/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-550959681/281474976710656), (-2218902391/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((841715449/2251799813685248), (2763710543/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3623580339/144115188075855872), (-1239829197/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((5630382929/4611686018427387904), (251111411/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-877861315/18446744073709551616), (885551203/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((3519562791/2361183241434822606848), (-1395964183/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2516748349/75557863725914323419136), (4874617035/75557863725914323419136)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((350648045/2417851639229258349412352), (-6607203159/2417851639229258349412352)), (31/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((89404541/2417851639229258349412352), (3681989589/38685626227668133590597632)), (3/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-834067483/309485009821345068724781056), (-819615823/309485009821345068724781056)), (9/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((5161078121/39614081257132168796771975168), (1901977407/39614081257132168796771975168)), (27/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((405902825/4398046511104), (-5247586887/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((550959681/140737488355328), (2218902391/70368744177664)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-2525146347/2251799813685248), (-4145565815/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((3623580339/36028797018963968), (1239829197/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-7037978661/1152921504606846976), (-1255557055/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((2633583945/9223372036854775808), (-1328326805/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-1539808721/147573952589676412928), (305367165/36893488147419103232)), (9/295147905179352825856), by norm_num⟩
  | 7 => ⟨((2516748349/9444732965739290427392), (-4874617035/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-394479051/302231454903657293676544), (3716551777/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-447022705/1208925819614629174706176), (-4602486987/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((1146842789/38685626227668133590597632), (2253943513/77371252455336267181195264)), (9/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-3870808591/2475880078570760549798248448), (-89155191/154742504910672534362390528)), (7/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((651400729/9903520314283042199192993792), (-183996107/39614081257132168796771975168)), (11/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-183653227/70368744177664), (-5917073043/281474976710656)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((841715449/562949953421312), (2763710543/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-3623580339/18014398509481984), (-1239829197/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2345992887/144115188075855872), (837038037/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-4389306575/4611686018427387904), (276734751/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 5 => ⟨((1539808721/36893488147419103232), (-305367165/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-367025801/295147905179352825856), (710881651/295147905179352825856)), (9/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((131493017/18889465931478580854784), (-4955402369/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((1341068115/604462909807314587353088), (431483155/75557863725914323419136)), (7/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-3822809297/19342813113834066795298816), (-3756572523/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((443530151/38685626227668133590597632), (326902367/77371252455336267181195264)), (21/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-651400729/1237940039285380274899124224), (183996107/4951760157141521099596496896)), (35/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((3120317487/158456325028528675187087900672), (-1680718747/158456325028528675187087900672)), (29/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-841715449/1125899906842624), (-2763710543/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((3623580339/18014398509481984), (1239829197/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 2 => ⟨((-7037978661/288230376151711744), (-1255557055/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((4389306575/2305843009213693952), (-276734751/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-3849521803/36893488147419103232), (1526835825/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 5 => ⟨((2202154805/590295810358705651712), (-4265289905/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-57528195/2361183241434822606848), (4335977073/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-1341068115/151115727451828646838272), (-431483155/18889465931478580854784)), (7/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((4300660459/4835703278458516698824704), (528268011/604462909807314587353088)), (13/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-4435301511/77371252455336267181195264), (-1634511835/77371252455336267181195264)), (25/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((7165408019/2475880078570760549798248448), (-252994647/1237940039285380274899124224)), (43/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-2340238115/19807040628566084398385987584), (315134765/4951760157141521099596496896)), (37/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((584453279/158456325028528675187087900672), (-763820649/158456325028528675187087900672)), (1/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2898864271/36028797018963968), (-1983726715/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((5630382929/288230376151711744), (251111411/72057594037927936)), (9/288230376151711744), by norm_num⟩
  | 2 => ⟨((-2633583945/1152921504606846976), (1328326805/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 3 => ⟨((1539808721/9223372036854775808), (-305367165/2305843009213693952)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-1101077403/147573952589676412928), (4265289905/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 5 => ⟨((34516917/590295810358705651712), (-650396561/590295810358705651712)), (17/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((1877495361/75557863725914323419136), (604076417/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-3440528367/1208925819614629174706176), (-1690457635/604462909807314587353088)), (11/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((3991771359/19342813113834066795298816), (367765163/4835703278458516698824704)), (11/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-1791352005/154742504910672534362390528), (252994647/309485009821345068724781056)), (43/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((5148523853/9903520314283042199192993792), (-693296483/2475880078570760549798248448)), (5/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-2805375739/158456325028528675187087900672), (3666339115/158456325028528675187087900672)), (9/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((1615383757/5070602400912917605986812821504), (-3456395927/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3753588619/576460752303423488), (-669630429/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((877861315/576460752303423488), (-885551203/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1539808721/9223372036854775808), (305367165/2305843009213693952)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((367025801/36893488147419103232), (-2843526603/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-57528195/590295810358705651712), (4335977073/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-1877495361/37778931862957161709568), (-604076417/4722366482869645213696)), (11/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((2006974881/302231454903657293676544), (3944401149/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-1330590453/2417851639229258349412352), (-980707101/4835703278458516698824704)), (31/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((2687028007/77371252455336267181195264), (-189745985/77371252455336267181195264)), (17/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-67038071/38685626227668133590597632), (2310988277/2475880078570760549798248448)), (35/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((642898607/9903520314283042199192993792), (-3360810855/39614081257132168796771975168)), (17/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-1615383757/1267650600228229401496703205376), (3456395927/633825300114114700748351602688)), (1/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-557135445/10141204801825835211973625643008), (-22151915/79228162514264337593543950336)), (59/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4013080297/9223372036854775808), (506029259/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((3519562791/36893488147419103232), (-1395964183/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-2516748349/295147905179352825856), (2437308517/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 3 => ⟨((262986035/2361183241434822606848), (-4955402369/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((1341068115/18889465931478580854784), (431483155/2361183241434822606848)), (9/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-3440528367/302231454903657293676544), (-1690457635/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((5322361813/4835703278458516698824704), (980707101/2417851639229258349412352)), (17/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-3070889151/38685626227668133590597632), (433705109/77371252455336267181195264)), (21/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((5516275557/1237940039285380274899124224), (-2971270641/1237940039285380274899124224)), (3/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-3673706325/19807040628566084398385987584), (4801158365/19807040628566084398385987584)), (13/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((1269230095/316912650057057350374175801344), (-2715739657/158456325028528675187087900672)), (27/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((477544667/2535301200456458802993406410752), (4860763063/5070602400912917605986812821504)), (53/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-1232527377/40564819207303340847894502572032), (-867626049/20282409603651670423947251286016)), (51/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3519562791/147573952589676412928), (1395964183/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((2516748349/590295810358705651712), (-4874617035/590295810358705651712)), (13/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-394479051/4722366482869645213696), (7433103553/4722366482869645213696)), (37/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-670534057/9444732965739290427392), (-431483155/2361183241434822606848)), (11/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((4300660459/302231454903657293676544), (528268011/37778931862957161709568)), (39/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-3991771359/2417851639229258349412352), (-1471060651/2417851639229258349412352)), (15/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((5374056015/38685626227668133590597632), (-379491971/38685626227668133590597632)), (21/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-5516275557/618970019642690137449562112), (1485635321/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((64576869/154742504910672534362390528), (-675162895/1237940039285380274899124224)), (33/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-1586537619/158456325028528675187087900672), (3394674571/79228162514264337593543950336)), (37/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-656623917/1267650600228229401496703205376), (-1670887303/633825300114114700748351602688)), (5/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((924395533/10141204801825835211973625643008), (2602878147/20282409603651670423947251286016)), (21/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-4984563857/649037107316853453566312041152512), (-2918000855/649037107316853453566312041152512)), (41/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2237109643/2361183241434822606848), (541624115/295147905179352825856)), (27/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((350648045/9444732965739290427392), (-6607203159/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((447022705/9444732965739290427392), (2301243493/18889465931478580854784)), (33/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-238925581/18889465931478580854784), (-3756572523/302231454903657293676544)), (41/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((2217650755/1208925819614629174706176), (1634511835/2417851639229258349412352)), (41/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-7165408019/38685626227668133590597632), (252994647/19342813113834066795298816)), (33/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((67038071/4835703278458516698824704), (-2310988277/309485009821345068724781056)), (49/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-3673706325/4951760157141521099596496896), (4801158365/4951760157141521099596496896)), (33/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((1586537619/79228162514264337593543950336), (-3394674571/39614081257132168796771975168)), (85/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((364791065/316912650057057350374175801344), (3713082895/633825300114114700748351602688)), (25/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-2259633525/10141204801825835211973625643008), (-3181295513/10141204801825835211973625643008)), (57/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((830760643/40564819207303340847894502572032), (1945333903/162259276829213363391578010288128)), (31/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-7273350509/5192296858534827628530496329220096), (-193545551/1298074214633706907132624082305024)), (127/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-280518435/37778931862957161709568), (5285762527/37778931862957161709568)), (5/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-89404541/4722366482869645213696), (-3681989589/75557863725914323419136)), (17/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((1146842789/151115727451828646838272), (2253943513/302231454903657293676544)), (29/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-443530151/302231454903657293676544), (-326902367/604462909807314587353088)), (19/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((7165408019/38685626227668133590597632), (-252994647/19342813113834066795298816)), (81/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-5148523853/309485009821345068724781056), (693296483/77371252455336267181195264)), (35/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((642898607/618970019642690137449562112), (-3360810855/2475880078570760549798248448)), (7/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-1269230095/39614081257132168796771975168), (2715739657/19807040628566084398385987584)), (39/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-656623917/316912650057057350374175801344), (-6683549211/633825300114114700748351602688)), (105/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((2259633525/5070602400912917605986812821504), (3181295513/5070602400912917605986812821504)), (65/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-3655346829/81129638414606681695789005144064), (-1069933647/40564819207303340847894502572032)), (39/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((4364010305/1298074214633706907132624082305024), (232254661/649037107316853453566312041152512)), (87/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-518558365/2596148429267413814265248164610048), (1363428641/20769187434139310514121985316880384)), (47/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((220160/42717603), (-33088/14239201)), 0, by norm_num⟩
  | 1 => ⟨((-77234167808/608264535355203), (29138616320/202754845118401)), 0, by norm_num⟩
  | 2 => ⟨((1082407533/562949953421312), (-1749195629/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((489741939/18014398509481984), (1972357681/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-2244574531/576460752303423488), (-3684947391/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((3865152361/18446744073709551616), (2644968953/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-5004784825/590295810358705651712), (-223210143/147573952589676412928)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((5350773729/18889465931478580854784), (-1349411357/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1173187597/151115727451828646838272), (3722571155/604462909807314587353088)), (25/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((1491406429/9671406556917033397649408), (-2888661947/9671406556917033397649408)), (19/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-93506145/154742504910672534362390528), (7047683369/618970019642690137449562112)), (27/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-1387125001/9903520314283042199192993792), (-3570414147/9903520314283042199192993792)), (5/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((2965573273/316912650057057350374175801344), (364273699/39614081257132168796771975168)), (57/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1324033909/67108864), (263742017/16777216)), (5/134217728), by norm_num⟩
  | 1 => ⟨((2855509221/2147483648), (940187035/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4355800825/549755813888), (-1019075077/274877906944)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2300455359/35184372088832), (2754589289/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((256931589/562949953421312), (-1941301325/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 5 => ⟨((954573007/144115188075855872), (1326766091/36028797018963968)), (39/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2317903553/4611686018427387904), (-3285554351/4611686018427387904)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((2786688355/147573952589676412928), (1596530043/147573952589676412928)), (81/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1341602467/2361183241434822606848), (-454112113/9444732965739290427392)), (49/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((274744625/18889465931478580854784), (-50322087/9444732965739290427392)), (259/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-739016569/2417851639229258349412352), (2962089915/9671406556917033397649408)), (87/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((163655845/38685626227668133590597632), (-3593637239/309485009821345068724781056)), (29/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((606892945/19807040628566084398385987584), (3546465909/9903520314283042199192993792)), (623/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-288642009/1125899906842624), (1865808671/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-391793551/36028797018963968), (-6311544579/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((1795659625/576460752303423488), (2947957913/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-2576768241/9223372036854775808), (-440828159/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((2502392413/147573952589676412928), (223210143/73786976294838206464)), (7/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-3745541611/4722366482869645213696), (472293975/2361183241434822606848)), (7/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((2189950181/75557863725914323419136), (-6785937/295147905179352825856)), (13/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-1789687715/2417851639229258349412352), (108324823/75557863725914323419136)), (11/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((70129609/19342813113834066795298816), (-5285762527/77371252455336267181195264)), (5/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((635765625/618970019642690137449562112), (3272879635/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-407766325/4951760157141521099596496896), (-400701069/4951760157141521099596496896)), (13/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((1376287499/316912650057057350374175801344), (1014387951/633825300114114700748351602688)), (41/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-7411492739/40564819207303340847894502572032), (32710419/2535301200456458802993406410752)), (1/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((331008473/16777216), (2109936247/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((5711018395/4294967296), (940186659/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((4355802537/549755813888), (-2038147343/549755813888)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-2300465189/35184372088832), (1377291281/17592186044416)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1027764539/2251799813685248), (-1941297919/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((477229351/72057594037927936), (5307093191/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-2317769889/4611686018427387904), (-3285660381/4611686018427387904)), (65/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2786579121/147573952589676412928), (1596741615/147573952589676412928)), (41/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-5366375625/9444732965739290427392), (-113689337/2361183241434822606848)), (197/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((274764027/18889465931478580854784), (-1609507741/302231454903657293676544)), (65/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-2956862695/9671406556917033397649408), (92540853/302231454903657293676544)), (349/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1310590791/309485009821345068724781056), (-898285483/77371252455336267181195264)), (465/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((150818513/4951760157141521099596496896), (886648421/2475880078570760549798248448)), (1247/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2736243237/4611686018427387904), (-4492126343/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((1472438995/9223372036854775808), (2015214441/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-2859877043/147573952589676412928), (-510194613/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 3 => ⟨((1783591243/1180591620717411303424), (-224901893/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-3128500259/37778931862957161709568), (2481714103/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((1789687715/604462909807314587353088), (-3466394335/604462909807314587353088)), (11/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-187012291/9671406556917033397649408), (7047683369/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-2179767857/309485009821345068724781056), (-5610650803/309485009821345068724781056)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((3495139929/4951760157141521099596496896), (214661287/309485009821345068724781056)), (11/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-1802281249/39614081257132168796771975168), (-664182587/39614081257132168796771975168)), (21/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((5823315723/2535301200456458802993406410752), (-51402087/316912650057057350374175801344)), (9/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-3803815603/40564819207303340847894502572032), (1024438093/20282409603651670423947251286016)), (31/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((1899937009/649037107316853453566312041152512), (-620755829/162259276829213363391578010288128)), (27/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((331008473/16777216), (2109936247/134217728)), (7/134217728), by norm_num⟩
  | 1 => ⟨((1427754599/1073741824), (940186659/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((2177901263/274877906944), (-2038147345/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-143779071/2199023255552), (2754582549/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1027764353/2251799813685248), (-1941297845/1125899906842624)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((954459129/144115188075855872), (5307092365/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1158884989/2305843009213693952), (-3285658701/4611686018427387904)), (33/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1393289041/73786976294838206464), (399184735/36893488147419103232)), (83/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5366368959/9444732965739290427392), (-454750797/9444732965739290427392)), (99/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((2198105341/151115727451828646838272), (-201189101/37778931862957161709568)), (261/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2956840481/9671406556917033397649408), (2961305727/9671406556917033397649408)), (175/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((655280885/154742504910672534362390528), (-898281575/77371252455336267181195264)), (233/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((603332033/19807040628566084398385987584), (886638949/2475880078570760549798248448)), (39/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4575803269/1180591620717411303424), (204077845/295147905179352825856)), (5/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-535077373/590295810358705651712), (539764543/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((1877100155/18889465931478580854784), (-2978056923/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-1789687715/302231454903657293676544), (3466394335/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((280518437/4835703278458516698824704), (-5285762527/4835703278458516698824704)), (19/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((1144378125/38685626227668133590597632), (5891183343/77371252455336267181195264)), (7/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-1223298975/309485009821345068724781056), (-2404206415/618970019642690137449562112)), (17/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((3244106247/9903520314283042199192993792), (74720541/618970019642690137449562112)), (5/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-1637807547/79228162514264337593543950336), (231309391/158456325028528675187087900672)), (43/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((2615123227/2535301200456458802993406410752), (-2817204757/5070602400912917605986812821504)), (11/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-3134896065/81129638414606681695789005144064), (4096988471/81129638414606681695789005144064)), (21/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((984614861/1298074214633706907132624082305024), (-4213511225/1298074214633706907132624082305024)), (5/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((1358349275/41538374868278621028243970633760768), (6913085245/41538374868278621028243970633760768)), (73/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((331008473/16777216), (2109936247/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((1427754599/1073741824), (940186659/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((2177901263/274877906944), (-2038147345/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-143779071/2199023255552), (2754582549/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((1027764353/2251799813685248), (-970648923/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((954459133/144115188075855872), (663386547/18014398509481984)), (21/72057594037927936), by norm_num⟩
  | 6 => ⟨((-579442499/1152921504606846976), (-3285658719/4611686018427387904)), (67/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1393289065/73786976294838206464), (798369479/73786976294838206464)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-2683184577/4722366482869645213696), (-454750783/9444732965739290427392)), (199/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2198105497/151115727451828646838272), (-100594561/18889465931478580854784)), (131/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2956840855/9671406556917033397649408), (2961306215/9671406556917033397649408)), (351/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1310562005/309485009821345068724781056), (-3593127305/309485009821345068724781056)), (467/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((603332681/19807040628566084398385987584), (886639361/2475880078570760549798248448)), (1249/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3033697221/151115727451828646838272), (2406510645/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((1084659221/302231454903657293676544), (-525211263/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-340022347/4835703278458516698824704), (6406984881/4835703278458516698824704)), (33/4835703278458516698824704), by norm_num⟩
  | 3 => ⟨((-1155937499/19342813113834066795298816), (-5950690245/38685626227668133590597632)), (39/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((3706966591/309485009821345068724781056), (113835531/9671406556917033397649408)), (35/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-3440718747/2475880078570760549798248448), (-633992469/1237940039285380274899124224)), (27/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((2316091481/19807040628566084398385987584), (-163552095/19807040628566084398385987584)), (19/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-148586547/19807040628566084398385987584), (1280547617/316912650057057350374175801344)), (3/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((3562381891/10141204801825835211973625643008), (-4655668717/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-1367520641/162259276829213363391578010288128), (1463024731/40564819207303340847894502572032)), (65/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-1131957729/2596148429267413814265248164610048), (-5760904371/2596148429267413814265248164610048)), (35/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((3187141501/41538374868278621028243970633760768), (560889567/5192296858534827628530496329220096)), (73/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((-2148229541/332306998946228968225951765070086144), (-628794797/166153499473114484112975882535043072)), (71/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((331008473/16777216), (2109936247/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((1427754599/1073741824), (940186659/4294967296)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((2177901263/274877906944), (-2038147345/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-143779071/2199023255552), (2754582549/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((1027764353/2251799813685248), (-970648923/562949953421312)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((954459133/144115188075855872), (663386547/18014398509481984)), (43/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2317769995/4611686018427387904), (-3285658719/4611686018427387904)), (17/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2786578129/147573952589676412928), (1596738959/147573952589676412928)), (85/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5366369151/9444732965739290427392), (-454750787/9444732965739290427392)), (25/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((4396210991/302231454903657293676544), (-1609512965/302231454903657293676544)), (263/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2956840859/9671406556917033397649408), (1480653097/4835703278458516698824704)), (11/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1310562029/309485009821345068724781056), (-449140909/38685626227668133590597632)), (117/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((603332553/19807040628566084398385987584), (7093114813/19807040628566084398385987584)), (625/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((275405645/19342813113834066795298816), (-2594711533/9671406556917033397649408)), (5/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((1404400549/38685626227668133590597632), (3614880843/38685626227668133590597632)), (17/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((-562970091/38685626227668133590597632), (-2212862647/154742504910672534362390528)), (29/154742504910672534362390528), by norm_num⟩
  | 3 => ⟨((3483570189/1237940039285380274899124224), (320944173/309485009821345068724781056)), (39/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-7034809729/19807040628566084398385987584), (496767023/19807040628566084398385987584)), (81/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((2527342867/79228162514264337593543950336), (-340330155/19807040628566084398385987584)), (35/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-2524723987/1267650600228229401496703205376), (3299555983/1267650600228229401496703205376)), (7/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((623048415/10141204801825835211973625643008), (-5332483987/20282409603651670423947251286016)), (39/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((322328073/81129638414606681695789005144064), (6561733385/324518553658426726783156020576256)), (13/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-2218448951/2596148429267413814265248164610048), (-3123312527/2596148429267413814265248164610048)), (65/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((112147615/1298074214633706907132624082305024), (1050432803/20769187434139310514121985316880384)), (77/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((-4284470901/664613997892457936451903530140172288), (-228021537/332306998946228968225951765070086144)), (43/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((4072856057/10633823966279326983230456482242756608), (-1338578493/10633823966279326983230456482242756608)), (93/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((331008473/16777216), (2109936247/134217728)), (5/67108864), by norm_num⟩
  | 1 => ⟨((1427754599/1073741824), (940186659/4294967296)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((2177901263/274877906944), (-2038147345/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-143779071/2199023255552), (2754582549/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((1027764353/2251799813685248), (-970648923/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((954459133/144115188075855872), (663386547/18014398509481984)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2317769995/4611686018427387904), (-3285658719/4611686018427387904)), (69/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2786578129/147573952589676412928), (1596738959/147573952589676412928)), (43/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-5366369151/9444732965739290427392), (-454750787/9444732965739290427392)), (201/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4396210991/302231454903657293676544), (-1609512965/302231454903657293676544)), (33/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-1478420429/4835703278458516698824704), (1480653097/4835703278458516698824704)), (353/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1310562027/309485009821345068724781056), (-449140909/38685626227668133590597632)), (469/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((603332561/19807040628566084398385987584), (7093114811/19807040628566084398385987584)), (1251/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1552751539085131/4194304), (-4769824871937/1048576)), (75877257/1048576), by norm_num⟩
  | 1 => ⟨((-3930124893/8), (-696704255/8)), 113, by norm_num⟩
  | 2 => ⟨((-1280144195/4), (-882672851/8)), (1425/16), by norm_num⟩
  | 3 => ⟨((-2185366175/16), (-2288981377/32)), (1511/32), by norm_num⟩
  | 4 => ⟨((-2747721825/64), (-1991753945/64)), (1213/64), by norm_num⟩
  | 5 => ⟨((-1353810963/128), (-1304349963/128)), (1571/256), by norm_num⟩
  | 6 => ⟨((-2167795143/1024), (-685063733/256)), (855/512), by norm_num⟩
  | 7 => ⟨((-2875771149/8192), (-4807554705/8192)), (1609/4096), by norm_num⟩
  | 8 => ⟨((-396825241/8192), (-3621573241/32768)), (2673/32768), by norm_num⟩
  | 9 => ⟨((-358069987/65536), (-1195575335/65536)), (3981/262144), by norm_num⟩
  | 10 => ⟨((-979964439/2097152), (-2810773813/1048576)), (2691/1048576), by norm_num⟩
  | 11 => ⟨((-343517573/16777216), (-1488583661/4194304)), (6673/16777216), by norm_num⟩
  | 12 => ⟨((310722767/134217728), (-2869208487/67108864)), (7651/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804837914611793/5070602400912917605986812821504), (-509533783753/1267650600228229401496703205376)), (97053/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1812974273809817/633825300114114700748351602688), (-4997647810811/633825300114114700748351602688)), (3737/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((15064544936853/309485009821345068724781056), (-5636672677207/39614081257132168796771975168)), (134945/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1930481069317433/2475880078570760549798248448), (-1500324788645/618970019642690137449562112)), (143723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1812188587996591/154742504910672534362390528), (-6015106647715/154742504910672534362390528)), (144107/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1588032889106819/9671406556917033397649408), (-2826937631495/4835703278458516698824704)), (67755/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((80781390178397/37778931862957161709568), (-2480951934277/302231454903657293676544)), (59491/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1942659337925327/75557863725914323419136), (-252840053125/2361183241434822606848)), (194119/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((669381271712427/2361183241434822606848), (-6092583448299/4722366482869645213696)), (73135/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1678248259730871/590295810358705651712), (-8417191335633/590295810358705651712)), (101117/295147905179352825856), by norm_num⟩
  | 8 => ⟨((947326537990109/36893488147419103232), (-10581680248725/73786976294838206464)), (31809/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1902978889068881/9223372036854775808), (-11987737771627/9223372036854775808)), (144305/4611686018427387904), by norm_num⟩
  | 6 => ⟨((837268429628509/576460752303423488), (-12092806185437/1152921504606846976)), (291551/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1265413360426265/144115188075855872), (-2675158567809/36028797018963968)), (258455/144115188075855872), by norm_num⟩
  | 4 => ⟨((1598593108587699/36028797018963968), (-8146455333737/18014398509481984)), (394477/36028797018963968), by norm_num⟩
  | 3 => ⟨((1624202551399357/9007199254740992), (-20796640947827/9007199254740992)), (505219/9007199254740992), by norm_num⟩
  | 2 => ⟨((312705305379053/562949953421312), (-5364196142777/562949953421312)), (523871/2251799813685248), by norm_num⟩
  | 1 => ⟨((1318174208629563/1125899906842624), (-16943503377547/562949953421312)), (104265/140737488355328), by norm_num⟩
  | 0 => ⟨((765302008228819/562949953421312), (-37449600008703/562949953421312)), (1871931/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((765302008228819/562949953421312), (-37449600008703/562949953421312)), (7140850071433639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037898107473459/562949953421312), (-50910838378873/281474976710656)), (2669325/562949953421312), by norm_num⟩
  | 2 => ⟨((947566316646257/281474976710656), (-93863162226383/140737488355328)), (1351045/70368744177664), by norm_num⟩
  | 3 => ⟨((1532357798961231/140737488355328), (-157991967774549/35184372088832)), (21797057/140737488355328), by norm_num⟩
  | 4 => ⟨((865413089606603/8796093022208), (-860112777419039/8796093022208)), (10475161/2199023255552), by norm_num⟩
  | 5 => ⟨((2030781272689/17179869184), (-330559071722337/17179869184)), (32107937/17179869184), by norm_num⟩
  | 6 => ⟨((-1552751539085131/4194304), (-4769824871937/1048576)), (75877257/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((331008473/16777216), (2109936247/134217728)), (5/67108864), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((94208/2541025), (-397056/2541025)), 0, by norm_num⟩
  | 1 => ⟨((74389159936/6456808050625), (37405851648/6456808050625)), 0, by norm_num⟩
  | 2 => ⟨((-10930135905599488/16406910676839390625), (13006365907746816/16406910676839390625)), 0, by norm_num⟩
  | 3 => ⟨((-1744665771/35184372088832), (-4696704647/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((1726529811/281474976710656), (-371107279/140737488355328)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((207865445/2251799813685248), (2378415229/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-6192960481/144115188075855872), (-185743305/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((1150602467/1152921504606846976), (-3815712331/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((4428623939/18446744073709551616), (1285031419/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-2263135033/147573952589676412928), (298362123/18446744073709551616)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-2312535591/2361183241434822606848), (-3537017179/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((2553698993/18889465931478580854784), (-920873769/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((787459111/604462909807314587353088), (866355257/75557863725914323419136)), (19/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (1551/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (1551/256)))⁻¹=value ((94208/2541025), (-397056/2541025)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((94208/2541025), (-397056/2541025))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((53248/931659), (-132352/931659)), 0, by norm_num⟩
  | 1 => ⟨((2446950400/289329497427), (7047479296/867988492281)), 0, by norm_num⟩
  | 2 => ⟨((-661816812240896/808669290730024179), (298156080234496/808669290730024179)), 0, by norm_num⟩
  | 3 => ⟨((-197129125/70368744177664), (-302003595/4398046511104)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((5581692087/1125899906842624), (1985335535/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1202107357/4503599627370496), (2717874091/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-248692329/18014398509481984), (-248440677/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((5427263673/2305843009213693952), (-221780331/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1977417019/36893488147419103232), (6370810949/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-1584047531/147573952589676412928), (-1290060073/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 10 => ⟨((4380819913/4722366482869645213696), (-2420778247/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((93515915/9444732965739290427392), (1521397587/18889465931478580854784)), (25/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-1814561631/302231454903657293676544), (-966144771/604462909807314587353088)), (5/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (1551/256)))⁻¹=value ((53248/931659), (-132352/931659)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((53248/931659), (-132352/931659))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47534768128/2367368810475), (-33611055104/2367368810475)), 0, by norm_num⟩
  | 1 => ⟨((842151285/274877906944), (-2557553561/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((334716245/2199023255552), (932468107/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-3292202417/70368744177664), (135352873/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((331106789/281474976710656), (-2477096883/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((3235676493/9007199254740992), (1019478183/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-4203421847/144115188075855872), (1801782111/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-781514685/576460752303423488), (-1796965999/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((5417332447/18446744073709551616), (-307671319/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-679087501/147573952589676412928), (28726227/1152921504606846976)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-2251472773/1180591620717411303424), (-1163314027/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((1183333581/9444732965739290427392), (-2442271355/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1104145593/151115727451828646838272), (987123353/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((55/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((20480/289091), (-36096/289091)), 0, by norm_num⟩
  | 1 => ⟨((441745408/83573606281), (739246080/83573606281)), 0, by norm_num⟩
  | 2 => ⟨((-17865386229760/24160377413380571), (402741264384/24160377413380571)), 0, by norm_num⟩
  | 3 => ⟨((884944923/35184372088832), (-25703521/549755813888)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((2283303889/1125899906842624), (908130533/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-2461253827/9007199254740992), (222050051/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((2567989681/288230376151711744), (-5042852841/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((895457745/1152921504606846976), (2711558391/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((-3723515735/36893488147419103232), (252160591/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1858393753/590295810358705651712), (-241391591/36893488147419103232)), (21/590295810358705651712), by norm_num⟩
  | 10 => ⟨((2804720447/9444732965739290427392), (2022612637/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-5630258327/151115727451828646838272), (508987845/151115727451828646838272)), (27/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1341242243/1208925819614629174706176), (-1478108109/604462909807314587353088)), (11/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (1551/256)))⁻¹=value ((20480/289091), (-36096/289091)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((20480/289091), (-36096/289091))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2186736696295424/684385016789028225), (1027460581818368/684385016789028225)), 0, by norm_num⟩
  | 1 => ⟨((-474464281/8796093022208), (-7036679765/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((508334643/4398046511104), (1266764949/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-2650366891/281474976710656), (3354719411/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1973961043/2251799813685248), (-51671987/35184372088832)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((6357274759/36028797018963968), (-1135785401/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-232472093/72057594037927936), (2528594317/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-1690601731/1152921504606846976), (-2016372471/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((284017693/2305843009213693952), (-1837333909/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 9 => ⟨((1369558469/295147905179352825856), (1000362691/73786976294838206464)), (1/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-5992175391/4722366482869645213696), (-104932611/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((1475853041/37778931862957161709568), (-1950022731/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((2179081689/302231454903657293676544), (1846255871/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((71/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((290816/3696097), (-397056/3696097)), 0, by norm_num⟩
  | 1 => ⟨((36539760640/13661133033409), (115470237696/13661133033409)), 0, by norm_num⟩
  | 2 => ⟨((-4919059935/8796093022208), (-830619137/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((70687605/2199023255552), (-3181794399/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-113206945/2251799813685248), (5890756075/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-2495646249/18014398509481984), (-237828663/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((6412057867/576460752303423488), (-947153223/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1204062859/4611686018427387904), (3351471211/4611686018427387904)), (11/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-2122370725/73786976294838206464), (-1572190161/36893488147419103232)), (17/73786976294838206464), by norm_num⟩
  | 9 => ⟨((8076473915/2361183241434822606848), (310537639/2361183241434822606848)), (13/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-1337664391/9444732965739290427392), (1686375175/9444732965739290427392)), (5/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-1214561951/302231454903657293676544), (-69096709/4722366482869645213696)), (15/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((570621083/604462909807314587353088), (434942219/1208925819614629174706176)), (91/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (1551/256)))⁻¹=value ((290816/3696097), (-397056/3696097)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((290816/3696097), (-397056/3696097))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-792757027/8796093022208), (4058249427/8796093022208)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-3920179209/35184372088832), (-2819705839/35184372088832)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((761735253/35184372088832), (-1747314095/140737488355328)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((99814675/281474976710656), (4053901467/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-3909922507/9007199254740992), (-1296901967/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((2544223417/72057594037927936), (-2816536119/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((1349750317/576460752303423488), (371913603/72057594037927936)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((-5337205459/9223372036854775808), (105464599/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1560045695/73786976294838206464), (-970302937/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 9 => ⟨((2252015505/590295810358705651712), (556828251/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-4297206017/9444732965739290427392), (1804316905/9444732965739290427392)), (27/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-57110999/151115727451828646838272), (-418150771/9444732965739290427392)), (49/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((2186011863/604462909807314587353088), (53932093/37778931862957161709568)), (43/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((87/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((118784/1447755), (-132352/1447755)), 0, by norm_num⟩
  | 1 => ⟨((189300736/232888282225), (15721299968/2095994540025)), 0, by norm_num⟩
  | 2 => ⟨((-1141559290494976/3034486575293893875), (-820974958149632/3034486575293893875)), 0, by norm_num⟩
  | 3 => ⟨((3912424001/140737488355328), (-858050341/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-970243429/1125899906842624), (3424556189/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((-307715145/9007199254740992), (-14324113/140737488355328)), (5/36028797018963968), by norm_num⟩
  | 6 => ⟨((3489749269/576460752303423488), (188340467/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-212033209/576460752303423488), (195406421/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 8 => ⟨((270873177/36893488147419103232), (-876802441/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1853819901/2361183241434822606848), (3094461875/2361183241434822606848)), (13/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-6959877727/75557863725914323419136), (-337669807/18889465931478580854784)), (73/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((2778059031/604462909807314587353088), (-2101777319/604462909807314587353088)), (51/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-143158289/4835703278458516698824704), (3411290921/9671406556917033397649408)), (143/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (1551/256)))⁻¹=value ((118784/1447755), (-132352/1447755)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((118784/1447755), (-132352/1447755))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((611913725/17592186044416), (3243521607/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-5629988373/281474976710656), (232879193/70368744177664)), (3/140737488355328), by norm_num⟩
  | 2 => ⟨((184446563/140737488355328), (-4557506327/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((275574199/562949953421312), (2202093161/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1643103541/18014398509481984), (1087597825/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((971666729/576460752303423488), (-6826667683/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((327461879/288230376151711744), (1780763717/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-2367454647/18446744073709551616), (1366679587/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-88213653/73786976294838206464), (-4472732127/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1652463663/1180591620717411303424), (1246339031/2361183241434822606848)), (19/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-3831284355/37778931862957161709568), (1881264443/18889465931478580854784)), (37/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-675555747/151115727451828646838272), (-930809405/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((2837883295/2417851639229258349412352), (13230143/151115727451828646838272)), (1/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((103/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((421888/5121505), (-397056/5121505)), 0, by norm_num⟩
  | 1 => ⟨((-10168008704/26229813465025), (167513161728/26229813465025)), 0, by norm_num⟩
  | 2 => ⟨((-2037104883/8796093022208), (-2445909007/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((5718921923/281474976710656), (696841863/281474976710656)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-4200999159/4503599627370496), (1543876687/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((426702799/36028797018963968), (-1160095721/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((2315647897/1152921504606846976), (3587338749/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-3750957477/18446744073709551616), (-231968251/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((3047387815/295147905179352825856), (-1714936037/295147905179352825856)), (21/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-1889228131/9444732965739290427392), (3020197463/4722366482869645213696)), (55/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-2501346569/151115727451828646838272), (-5152390947/151115727451828646838272)), (71/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((4844007129/2417851639229258349412352), (1844078643/2417851639229258349412352)), (23/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-2167980677/19342813113834066795298816), (894539745/19342813113834066795298816)), (59/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (1551/256)))⁻¹=value ((421888/5121505), (-397056/5121505)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((421888/5121505), (-397056/5121505))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7249418897/1125899906842624), (619422267/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((-1912837651/1125899906842624), (4565670231/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 2 => ⟨((-482968957/2251799813685248), (-82249855/140737488355328)), (5/4503599627370496), by norm_num⟩
  | 3 => ⟨((1976551397/18014398509481984), (651570151/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 4 => ⟨((-2995701187/288230376151711744), (3766095299/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((-1977649291/2305843009213693952), (-4720664589/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((309151135/1152921504606846976), (490940573/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-2494633993/147573952589676412928), (1870574627/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-460368557/295147905179352825856), (-1685342235/590295810358705651712)), (21/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((6255070635/18889465931478580854784), (-149241763/18889465931478580854784)), (43/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-527602751/37778931862957161709568), (276050539/9444732965739290427392)), (43/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-2274108763/1208925819614629174706176), (-729409081/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((663711709/2417851639229258349412352), (-554153631/9671406556917033397649408)), (77/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((119/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((487424/6030817), (-397056/6030817)), 0, by norm_num⟩
  | 1 => ⟨((-39964344320/36370753687489), (193534623744/36370753687489)), 0, by norm_num⟩
  | 2 => ⟨((-1150203281/8796093022208), (-1104813289/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1907512265/140737488355328), (822880099/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-833384093/1125899906842624), (945272073/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1657512983/72057594037927936), (-2366974707/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((10936321/72057594037927936), (4806899641/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1379042577/18446744073709551616), (-730927047/9223372036854775808)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((6646483291/1180591620717411303424), (218856769/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-4758557979/18889465931478580854784), (1467344741/9444732965739290427392)), (39/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1531068573/302231454903657293676544), (-2201925267/151115727451828646838272)), (47/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((664782705/2417851639229258349412352), (114182805/151115727451828646838272)), (7/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-1392080085/38685626227668133590597632), (-415553031/19342813113834066795298816)), (67/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (1551/256)))⁻¹=value ((487424/6030817), (-397056/6030817)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((487424/6030817), (-397056/6030817))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5339815699/9007199254740992), (-3017279697/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-150884939/9007199254740992), (5562479683/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((-2352665157/36028797018963968), (-1662467247/36028797018963968)), (15/72057594037927936), by norm_num⟩
  | 3 => ⟨((4097575559/288230376151711744), (-217867487/36028797018963968)), (11/288230376151711744), by norm_num⟩
  | 4 => ⟨((-819035807/2305843009213693952), (1413873183/576460752303423488)), (19/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-155927743/576460752303423488), (-2027347661/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 6 => ⟨((3068871873/73786976294838206464), (-2291064205/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-511705217/590295810358705651712), (6089933299/1180591620717411303424)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-529867529/1180591620717411303424), (-861956039/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((4261283129/75557863725914323419136), (-53038041/2361183241434822606848)), (21/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-224880297/302231454903657293676544), (3654590987/604462909807314587353088)), (83/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-4641193217/9671406556917033397649408), (-3288566625/9671406556917033397649408)), (83/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((947796319/19342813113834066795298816), (-1915726247/77371252455336267181195264)), (79/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((135/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((61440/785689), (-132352/2357067)), 0, by norm_num⟩
  | 1 => ⟨((-8228405248/5555764842489), (2710568960/617307204721)), 0, by norm_num⟩
  | 2 => ⟨((-31705247252480/485011480370037769), (-2792777263874048/13095309969991019763)), 0, by norm_num⟩
  | 3 => ⟨((601194203/70368744177664), (3661008353/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-2326686007/4503599627370496), (-16224833/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1484707295/72057594037927936), (-251142035/18014398509481984)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1910233641/4611686018427387904), (5181571565/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1132584165/73786976294838206464), (-1024909783/18446744073709551616)), (9/73786976294838206464), by norm_num⟩
  | 8 => ⟨((2550129807/1180591620717411303424), (256991297/147573952589676412928)), (5/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-629720261/4722366482869645213696), (-281260103/37778931862957161709568)), (23/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((3277923437/604462909807314587353088), (-2087054889/604462909807314587353088)), (13/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-2226230883/19342813113834066795298816), (5556231909/19342813113834066795298816)), (57/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-551599983/154742504910672534362390528), (-4475972131/309485009821345068724781056)), (31/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (1551/256)))⁻¹=value ((61440/785689), (-132352/2357067)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((61440/785689), (-132352/2357067))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1985151299/72057594037927936), (-1071569269/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((2395374825/144115188075855872), (4062045819/144115188075855872)), (7/72057594037927936), by norm_num⟩
  | 2 => ⟨((-5268011669/576460752303423488), (-332660743/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((330215731/288230376151711744), (-3470618239/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((990657071/9223372036854775808), (2792440731/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-53258173/1152921504606846976), (-199635189/18446744073709551616)), (19/73786976294838206464), by norm_num⟩
  | 6 => ⟨((2650801927/590295810358705651712), (-1305494861/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((804989831/4722366482869645213696), (3546854605/4722366482869645213696)), (29/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-6297510975/75557863725914323419136), (-2110028973/75557863725914323419136)), (65/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((4347170409/604462909807314587353088), (-3730413283/604462909807314587353088)), (69/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((838401821/4835703278458516698824704), (2315783407/2417851639229258349412352)), (35/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1746445441/19342813113834066795298816), (-38957507/1208925819614629174706176)), (71/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((2128146623/309485009821345068724781056), (-1845323843/309485009821345068724781056)), (137/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((151/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((618496/8242657), (-397056/8242657)), 0, by norm_num⟩
  | 1 => ⟨((-112441917440/67941394419649), (245577547776/67941394419649)), 0, by norm_num⟩
  | 2 => ⟨((-878424447/35184372088832), (-6173861105/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1453254989/281474976710656), (3367578877/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-6084993601/18014398509481984), (-1802888247/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((4347522211/288230376151711744), (-78918973/18014398509481984)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1061580541/2305843009213693952), (1216688689/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((673529515/147573952589676412928), (-2278923431/73786976294838206464)), (15/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1352132093/2361183241434822606848), (2995576779/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-3932130185/75557863725914323419136), (-2554283349/75557863725914323419136)), (33/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((3344747035/1208925819614629174706176), (35984807/2417851639229258349412352)), (33/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-31480393/302231454903657293676544), (1278154507/19342813113834066795298816)), (33/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((716868749/309485009821345068724781056), (-3087354189/618970019642690137449562112)), (33/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (1551/256)))⁻¹=value ((618496/8242657), (-397056/8242657)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((618496/8242657), (-397056/8242657))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-920254511/1152921504606846976), (-6676024899/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 1 => ⟨((1599307119/576460752303423488), (871802637/576460752303423488)), (15/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-1969262509/2305843009213693952), (1876919371/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 3 => ⟨((658571179/18446744073709551616), (-1881260921/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1934448895/73786976294838206464), (3845198315/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-206555817/36893488147419103232), (1259715355/1180591620717411303424)), (49/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((1455635911/4722366482869645213696), (-3414723721/4722366482869645213696)), (33/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((2071126987/37778931862957161709568), (3124303545/37778931862957161709568)), (41/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-3520365939/302231454903657293676544), (82889961/604462909807314587353088)), (23/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((3269237875/4835703278458516698824704), (-2648045047/2417851639229258349412352)), (25/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((581840653/9671406556917033397649408), (4676699371/38685626227668133590597632)), (13/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1044205291/77371252455336267181195264), (-357537131/309485009821345068724781056)), (53/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((236114155/309485009821345068724781056), (-2625335117/2475880078570760549798248448)), (105/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((167/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((684032/9545185), (-397056/9545185)), 0, by norm_num⟩
  | 1 => ⟨((-155123154944/91110556684225), (271599009792/91110556684225)), 0, by norm_num⟩
  | 2 => ⟨((-17506015/17592186044416), (-2502030265/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1685324365/562949953421312), (714294337/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3834017181/18014398509481984), (-2154355453/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((2914969337/288230376151711744), (-10198117/72057594037927936)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3315154875/9223372036854775808), (124178779/576460752303423488)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2478782173/295147905179352825856), (-2242285107/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((35644855/2361183241434822606848), (6791788517/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-146369571/9444732965739290427392), (-1923142891/75557863725914323419136)), (33/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((2622586675/2417851639229258349412352), (712867019/1208925819614629174706176)), (61/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1977985309/38685626227668133590597632), (221484887/154742504910672534362390528)), (111/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1115552833/618970019642690137449562112), (-2759914231/2475880078570760549798248448)), (101/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (1551/256)))⁻¹=value ((684032/9545185), (-397056/9545185)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((684032/9545185), (-397056/9545185))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1374615275/4611686018427387904), (-440140457/1152921504606846976)), (5/2305843009213693952), by norm_num⟩
  | 1 => ⟨((5171493253/18446744073709551616), (4159585/9223372036854775808)), (15/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2004303785/36893488147419103232), (2601226173/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1607351551/295147905179352825856), (-5831565423/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 4 => ⟨((4213176331/1180591620717411303424), (1619046091/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-2423641823/4722366482869645213696), (3158731581/9444732965739290427392)), (57/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((260220753/75557863725914323419136), (-1649031801/18889465931478580854784)), (79/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((2738552469/302231454903657293676544), (517243255/75557863725914323419136)), (51/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-6267394189/4835703278458516698824704), (264466237/604462909807314587353088)), (29/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((48635423/1208925819614629174706176), (-5773492979/38685626227668133590597632)), (129/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((3405118783/309485009821345068724781056), (3820583043/309485009821345068724781056)), (17/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-4125338095/2475880078570760549798248448), (41024661/154742504910672534362390528)), (35/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((2565131589/39614081257132168796771975168), (-376033585/2475880078570760549798248448)), (35/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((183/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((249856/3659595), (-132352/3659595)), 0, by norm_num⟩
  | 1 => ⟨((-2495053824/1488070618225), (33068941312/13392635564025)), 0, by norm_num⟩
  | 2 => ⟨((442893839/35184372088832), (-504062697/4398046511104)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((924801713/562949953421312), (4661335909/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-147430473/1125899906842624), (-2010854277/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((3740404269/576460752303423488), (831657137/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-570901389/2305843009213693952), (1255900547/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2131217581/295147905179352825856), (-4014756003/590295810358705651712)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-291635557/2361183241434822606848), (107064627/295147905179352825856)), (17/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-88523121/37778931862957161709568), (-552202011/37778931862957161709568)), (29/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((3329874865/9671406556917033397649408), (4415956141/9671406556917033397649408)), (49/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1548203931/77371252455336267181195264), (-1448548355/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((4220682801/4951760157141521099596496896), (-209366449/4951760157141521099596496896)), (71/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (1551/256)))⁻¹=value ((249856/3659595), (-132352/3659595)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((249856/3659595), (-132352/3659595))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5040730491/147573952589676412928), (-2255583847/147573952589676412928)), (35/147573952589676412928), by norm_num⟩
  | 1 => ⟨((759976945/36893488147419103232), (-1505855387/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-990445635/590295810358705651712), (4426844789/590295810358705651712)), (47/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-687526363/590295810358705651712), (-3396235301/2361183241434822606848)), (23/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((6781640457/18889465931478580854784), (-139674389/18889465931478580854784)), (39/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-2649572543/75557863725914323419136), (3637323285/75557863725914323419136)), (15/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-784448135/302231454903657293676544), (-5054689017/604462909807314587353088)), (85/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((5348463181/4835703278458516698824704), (914455029/2417851639229258349412352)), (7/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-2268150131/19342813113834066795298816), (1621586857/19342813113834066795298816)), (33/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-12669935/77371252455336267181195264), (-5145669135/309485009821345068724781056)), (149/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((3723477127/2475880078570760549798248448), (1249761995/1237940039285380274899124224)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-3441780613/19807040628566084398385987584), (352030845/4951760157141521099596496896)), (83/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((1132790611/316912650057057350374175801344), (-5793259369/316912650057057350374175801344)), (21/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((199/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((815104/12543457), (-397056/12543457)), 0, by norm_num⟩
  | 1 => ⟨((-253370531840/157338313510849), (323641933824/157338313510849)), 0, by norm_num⟩
  | 2 => ⟨((695457299/35184372088832), (-3248264287/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((922071545/1125899906842624), (1864754641/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-1423791379/18014398509481984), (-852659325/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((4688072961/1152921504606846976), (2103884805/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-2969916257/18446744073709551616), (46731161/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((3040540859/590295810358705651712), (-1601350673/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-2350268987/18889465931478580854784), (1602449679/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((820429817/604462909807314587353088), (-4522535935/604462909807314587353088)), (13/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((718758411/9671406556917033397649408), (2558844001/9671406556917033397649408)), (41/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-2043286433/309485009821345068724781056), (-574111791/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((3287526327/9903520314283042199192993792), (338198355/2475880078570760549798248448)), (51/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (1551/256)))⁻¹=value ((815104/12543457), (-397056/12543457)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((815104/12543457), (-397056/12543457))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6383328215/2361183241434822606848), (103905563/1180591620717411303424)), (55/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((650522321/590295810358705651712), (-3213072855/2361183241434822606848)), (45/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((269379851/2361183241434822606848), (2843312965/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-2539741619/18889465931478580854784), (-2809124927/37778931862957161709568)), (21/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((4328124511/151115727451828646838272), (-109153233/9444732965739290427392)), (73/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-908243563/604462909807314587353088), (6125695439/1208925819614629174706176)), (115/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-1123681543/2417851639229258349412352), (-3141551201/4835703278458516698824704)), (83/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((4225525159/38685626227668133590597632), (2005961/604462909807314587353088)), (7/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-2651545557/309485009821345068724781056), (3336402093/309485009821345068724781056)), (17/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-531322299/1237940039285380274899124224), (-3865152123/2475880078570760549798248448)), (155/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((3334261647/19807040628566084398385987584), (613301051/9903520314283042199192993792)), (85/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-4909275231/316912650057057350374175801344), (853476613/79228162514264337593543950336)), (89/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-8590505/633825300114114700748351602688), (-4807518813/2535301200456458802993406410752)), (91/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((275215617/274877906944), (-44606455/2199023255552)), (29/137438953472), by norm_num⟩
  | 1 => ⟨((1013318869/1099511627776), (3038867445/4398046511104)), (2263/4398046511104), by norm_num⟩
  | 2 => ⟨((1543863927/8796093022208), (5446835169/8796093022208)), (5305/8796093022208), by norm_num⟩
  | 3 => ⟨((-1433030093/17592186044416), (3829524671/17592186044416)), (4099/8796093022208), by norm_num⟩
  | 4 => ⟨((-3533363611/70368744177664), (1213774007/35184372088832)), (19021/70368744177664), by norm_num⟩
  | 5 => ⟨((-869679641/70368744177664), (82270801/281474976710656)), (71029/562949953421312), by norm_num⟩
  | 6 => ⟨((-3988760519/2251799813685248), (-2236367435/2251799813685248)), (111417/2251799813685248), by norm_num⟩
  | 7 => ⟨((-2773328415/18014398509481984), (-4229818597/18014398509481984)), (75595/4503599627370496), by norm_num⟩
  | 8 => ⟨((-786995413/144115188075855872), (-4836389817/144115188075855872)), (725065/144115188075855872), by norm_num⟩
  | 9 => ⟨((885582387/1152921504606846976), (-2110233185/576460752303423488)), (390221/288230376151711744), by norm_num⟩
  | 10 => ⟨((1822061977/9223372036854775808), (-187790677/576460752303423488)), (3054833/9223372036854775808), by norm_num⟩
  | 11 => ⟨((4038060253/147573952589676412928), (-3430396965/147573952589676412928)), (10982299/147573952589676412928), by norm_num⟩
  | 12 => ⟨((424368453/147573952589676412928), (-1452056145/1180591620717411303424)), (4571657/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((275215617/274877906944), (-44606455/2199023255552)), (929/4398046511104), by norm_num⟩
  | 1 => ⟨((1013318869/1099511627776), (3038867445/4398046511104)), (283/549755813888), by norm_num⟩
  | 2 => ⟨((1543863927/8796093022208), (5446835169/8796093022208)), (2653/4398046511104), by norm_num⟩
  | 3 => ⟨((-1433030093/17592186044416), (3829524671/17592186044416)), (8199/17592186044416), by norm_num⟩
  | 4 => ⟨((-3533363611/70368744177664), (1213774007/35184372088832)), (1189/4398046511104), by norm_num⟩
  | 5 => ⟨((-869679641/70368744177664), (82270801/281474976710656)), (17763/140737488355328), by norm_num⟩
  | 6 => ⟨((-3988760519/2251799813685248), (-2236367435/2251799813685248)), (27877/562949953421312), by norm_num⟩
  | 7 => ⟨((-2773328415/18014398509481984), (-4229818597/18014398509481984)), (303101/18014398509481984), by norm_num⟩
  | 8 => ⟨((-786995413/144115188075855872), (-4836389817/144115188075855872)), (365415/72057594037927936), by norm_num⟩
  | 9 => ⟨((885582387/1152921504606846976), (-2110233185/576460752303423488)), (1607001/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1822061977/9223372036854775808), (-187790677/576460752303423488)), (427971/1152921504606846976), by norm_num⟩
  | 11 => ⟨((4038060253/147573952589676412928), (-3430396965/147573952589676412928)), (8442629/73786976294838206464), by norm_num⟩
  | 12 => ⟨((424368453/147573952589676412928), (-1452056145/1180591620717411303424)), (65510293/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile030Gamma
