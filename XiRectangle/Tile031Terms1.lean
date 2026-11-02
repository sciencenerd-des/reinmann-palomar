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
namespace Reinmann.XiRectangle.Tile031Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8037/640))
  have he : value ((5/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-368633113/268435456), (-3703380415/134217728)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-221378546676545/1125899906842624), (-719014472180365/4503599627370496)), (19225197/2251799813685248), by norm_num⟩
  | 1 => ⟨((927769439/2147483648), (3013298549/8589934592)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((-4077035627/8589934592), (-3310446815/8589934592)), (183/8589934592), by norm_num⟩
  | 3 => ⟨((1493027147/4294967296), (75768699/268435456)), (17/1073741824), by norm_num⟩
  | 4 => ⟨((-1640257971/8589934592), (-1331846781/8589934592)), (19/2147483648), by norm_num⟩
  | 5 => ⟨((1441606051/17179869184), (36579581/536870912)), (17/4294967296), by norm_num⟩
  | 6 => ⟨((-527922041/17179869184), (-3429271655/137438953472)), (101/68719476736), by norm_num⟩
  | 7 => ⟨((331418081/34359738368), (2152822847/274877906944)), (129/274877906944), by norm_num⟩
  | 8 => ⟨((-728199953/274877906944), (-2365117635/1099511627776)), (9/68719476736), by norm_num⟩
  | 9 => ⟨((2844477927/4398046511104), (2309642043/4398046511104)), (143/4398046511104), by norm_num⟩
  | 10 => ⟨((-624995681/4398046511104), (-2029920905/17592186044416)), (1/137438953472), by norm_num⟩
  | 11 => ⟨((1997463085/70368744177664), (3243776075/140737488355328)), (207/140737488355328), by norm_num⟩
  | 12 => ⟨((-2925916655/562949953421312), (-593942043/140737488355328)), (77/281474976710656), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582186935648693/10141204801825835211973625643008), (-100121704443/316912650057057350374175801344)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889921602010567/316912650057057350374175801344), (-3796031414555/633825300114114700748351602688)), (8679/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890950005104539/39614081257132168796771975168), (-133437408091/1237940039285380274899124224)), (4883/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472699965904129/618970019642690137449562112), (-141757312675/77371252455336267181195264)), (10379/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772465298348941/154742504910672534362390528), (-2267758164453/77371252455336267181195264)), (5191/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387686876938391/2417851639229258349412352), (-2125642008745/4835703278458516698824704)), (19473/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259832640647729/604462909807314587353088), (-3719110963835/604462909807314587353088)), (17045/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889486853887843/75557863725914323419136), (-6042125509915/75557863725914323419136)), (27709/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324702285438471/1180591620717411303424), (-2265171514931/2361183241434822606848)), (2599/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623191632476133/590295810358705651712), (-3113594291801/295147905179352825856)), (14303/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912825280829487/36893488147419103232), (-7780936035579/73786976294838206464)), (17891/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825100070603137/9223372036854775808), (-8749359598857/9223372036854775808)), (40289/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596342628117719/1152921504606846976), (-8744117633039/1152921504606846976)), (40331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196636250233715/144115188075855872), (-7645205497349/144115188075855872)), (17669/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494707285147135/36028797018963968), (-2864003212695/9007199254740992)), (3319/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493071723966847/9007199254740992), (-3574843243429/2251799813685248)), (66549/9007199254740992), by norm_num⟩
  | 2 => ⟨((34929787821741/70368744177664), (-14268406165717/2251799813685248)), (33401/1125899906842624), by norm_num⟩
  | 1 => ⟨((556816882184431/562949953421312), (-5331296293351/281474976710656)), (12605/140737488355328), by norm_num⟩
  | 0 => ⟨((34412025434173/35184372088832), (-42340636117619/1125899906842624)), (102115/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((34412025434173/35184372088832), (-42340636117619/1125899906842624)), (389537813426780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((33606874641015/35184372088832), (-82822398722929/1125899906842624)), (414855/1125899906842624), by norm_num⟩
  | 2 => ⟨((255277710517357/281474976710656), (-79109042057713/562949953421312)), (853545/1125899906842624), by norm_num⟩
  | 3 => ⟨((451920452016177/562949953421312), (-286985015488231/1125899906842624)), (447025/281474976710656), by norm_num⟩
  | 4 => ⟨((1304854856498215/2251799813685248), (-921534123117673/2251799813685248)), (3782425/1125899906842624), by norm_num⟩
  | 5 => ⟨((189497541315635/1125899906842624), (-1068006373098491/2251799813685248)), (14958967/2251799813685248), by norm_num⟩
  | 6 => ⟨((-221378546676545/1125899906842624), (-719014472180365/4503599627370496)), (19225197/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/268435456), (-3703380415/134217728)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-386309675/268435456), (-7761927137/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-855914834476915/4503599627370496), (638728034832623/4503599627370496)), (35984011/4503599627370496), by norm_num⟩
  | 1 => ⟨((939758653/2147483648), (-171215/524288)), (5/268435456), by norm_num⟩
  | 2 => ⟨((-4327748531/8589934592), (1614795189/4294967296)), (187/8589934592), by norm_num⟩
  | 3 => ⟨((3321669751/8589934592), (-619700555/2147483648)), (145/8589934592), by norm_num⟩
  | 4 => ⟨((-1912106813/8589934592), (356728315/2147483648)), (169/17179869184), by norm_num⟩
  | 5 => ⟨((3522230915/34359738368), (-2628471361/34359738368)), (79/17179869184), by norm_num⟩
  | 6 => ⟨((-2703412133/68719476736), (504356581/17179869184)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((444631177/34359738368), (-2654454731/274877906944)), (41/68719476736), by norm_num⟩
  | 8 => ⟨((-31993785/8589934592), (3056053947/1099511627776)), (191/1099511627776), by norm_num⟩
  | 9 => ⟨((261932133/274877906944), (-3127477449/4398046511104)), (99/2199023255552), by norm_num⟩
  | 10 => ⟨((-3859974559/17592186044416), (2880513181/17592186044416)), (185/17592186044416), by norm_num⟩
  | 11 => ⟨((3231970865/70368744177664), (-1205932129/35184372088832)), (157/70368744177664), by norm_num⟩
  | 12 => ⟨((-2480629311/281474976710656), (1851174229/281474976710656)), (61/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791050579124123/5070602400912917605986812821504), (3257173495951/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889870660434155/316912650057057350374175801344), (1929369175853/316912650057057350374175801344)), (17359/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472708846809841/9903520314283042199192993792), (2170254162567/19807040628566084398385987584)), (9767/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890678080719227/2475880078570760549798248448), (4611110667583/2475880078570760549798248448)), (2595/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772343513882315/154742504910672534362390528), (4610346241615/154742504910672534362390528)), (10383/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775316666583939/4835703278458516698824704), (4321387399667/9671406556917033397649408)), (9737/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314933184064653/151115727451828646838272), (1890200886805/302231454903657293676544)), (17047/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889324506251411/75557863725914323419136), (3070815003449/37778931862957161709568)), (433/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((162335922305471/590295810358705651712), (2302444995741/2361183241434822606848)), (10397/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811512101906759/295147905179352825856), (6329558408123/590295810358705651712)), (28609/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825441269813979/73786976294838206464), (7908700024129/73786976294838206464)), (17893/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824864609248179/9223372036854775808), (8892821563599/9223372036854775808)), (40295/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199513394636397/144115188075855872), (2221809784739/288230376151711744)), (20169/576460752303423488), by norm_num⟩
  | 5 => ⟨((598215101353153/72057594037927936), (1942513516553/36028797018963968)), (35345/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494398194349083/36028797018963968), (727657554755/2251799813685248)), (53115/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492685329142507/9007199254740992), (7265585533193/4503599627370496)), (66565/9007199254740992), by norm_num⟩
  | 2 => ⟨((279341693522145/562949953421312), (7249100939201/1125899906842624)), (8353/281474976710656), by norm_num⟩
  | 1 => ⟨((1113054026166827/1125899906842624), (21664883429543/1125899906842624)), (50441/562949953421312), by norm_num⟩
  | 0 => ⟨((275006279709167/281474976710656), (43000115499099/1125899906842624)), (204359/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((275006279709167/281474976710656), (43000115499099/1125899906842624)), (779567722800826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((33534459990511/35184372088832), (42011911426953/562949953421312)), (51867/140737488355328), by norm_num⟩
  | 2 => ⟨((1016510825924331/1125899906842624), (80083666652629/562949953421312)), (426445/562949953421312), by norm_num⟩
  | 3 => ⟨((447482355420469/562949953421312), (9037872021013/35184372088832)), (222839/140737488355328), by norm_num⟩
  | 4 => ⟨((1274213282169891/2251799813685248), (919564686217121/2251799813685248)), (7499943/2251799813685248), by norm_num⟩
  | 5 => ⟨((345510409758531/2251799813685248), (1040697783054373/2251799813685248)), (14613387/2251799813685248), by norm_num⟩
  | 6 => ⟨((-855914834476915/4503599627370496), (638728034832623/4503599627370496)), (35984011/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-386309675/268435456), (-7761927137/268435456)), (3/268435456), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-402300069/268435456), (-126300221/4194304)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((66415314650515/1125899906842624), (242627029400135/1125899906842624)), (27426663/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1215034249/8589934592), (-1109684385/2147483648)), (127/8589934592), by norm_num⟩
  | 2 => ⟨((1456762441/8589934592), (2660906941/4294967296)), (77/4294967296), by norm_num⟩
  | 3 => ⟨((-291096981/2147483648), (-2126858725/4294967296)), (125/8589934592), by norm_num⟩
  | 4 => ⟨((1396040149/17179869184), (5099984483/17179869184)), (19/2147483648), by norm_num⟩
  | 5 => ⟨((-669511615/17179869184), (-4891691473/34359738368)), (37/8589934592), by norm_num⟩
  | 6 => ⟨((535139579/34359738368), (1954960643/34359738368)), (15/8589934592), by norm_num⟩
  | 7 => ⟨((-1466524191/274877906944), (-167421103/8589934592)), (167/274877906944), by norm_num⟩
  | 8 => ⟨((1758285713/1099511627776), (6423332343/1099511627776)), (203/1099511627776), by norm_num⟩
  | 9 => ⟨((-58558125/137438953472), (-3422772947/2199023255552)), (55/1099511627776), by norm_num⟩
  | 10 => ⟨((898664007/8796093022208), (820745107/2199023255552)), (107/8796093022208), by norm_num⟩
  | 11 => ⟨((-1567201581/70368744177664), (-2862633909/35184372088832)), (189/70368744177664), by norm_num⟩
  | 12 => ⟨((626330877/140737488355328), (4576197545/281474976710656)), (153/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197752945394709/1267650600228229401496703205376), (849047031549/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111228449450381/39614081257132168796771975168), (1005758088903/316912650057057350374175801344)), (8663/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890738842754773/39614081257132168796771975168), (2262653202335/39614081257132168796771975168)), (9747/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945287972775951/1237940039285380274899124224), (2403701136351/2475880078570760549798248448)), (10357/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772241877267567/154742504910672534362390528), (2403287327423/154742504910672534362390528)), (10359/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550538578326597/9671406556917033397649408), (2252642273067/9671406556917033397649408)), (9713/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314912588750567/151115727451828646838272), (1970622477561/604462909807314587353088)), (17001/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236148953559165/9444732965739290427392), (3201437622865/75557863725914323419136)), (27633/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324647146840241/1180591620717411303424), (1200178741251/2361183241434822606848)), (10365/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622889774340597/590295810358705651712), (1649660341639/295147905179352825856)), (891/18446744073709551616), by norm_num⟩
  | 8 => ⟨((228159417949145/9223372036854775808), (515299395485/9223372036854775808)), (35653/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456170210365821/2305843009213693952), (4635281448009/9223372036854775808)), (627/144115188075855872), by norm_num⟩
  | 6 => ⟨((797963504495183/576460752303423488), (4632266502567/1152921504606846976)), (40151/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598138319653603/72057594037927936), (2024921680409/72057594037927936)), (17579/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494175966746393/36028797018963968), (3033995171853/18014398509481984)), (52787/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492421716789811/9007199254740992), (3786571682933/4503599627370496)), (66073/9007199254740992), by norm_num⟩
  | 2 => ⟨((2234248706144085/4503599627370496), (15110797648695/4503599627370496)), (66207/2251799813685248), by norm_num⟩
  | 1 => ⟨((278185784767485/281474976710656), (22577629807253/2251799813685248)), (199295/2251799813685248), by norm_num⟩
  | 0 => ⟨((2199225841008149/2251799813685248), (44801928503503/2251799813685248)), (401291/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2199225841008149/2251799813685248), (44801928503503/2251799813685248)), (1530803689009856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2146987959399545/2251799813685248), (87511827910361/2251799813685248)), (799813/2251799813685248), by norm_num⟩
  | 2 => ⟨((2043653680853201/2251799813685248), (83438518684793/1125899906842624)), (1587337/2251799813685248), by norm_num⟩
  | 3 => ⟨((57574395551979/70368744177664), (75725841524095/562949953421312)), (779123/562949953421312), by norm_num⟩
  | 4 => ⟨((366664036748281/562949953421312), (247829891203237/1125899906842624)), (5938149/2251799813685248), by norm_num⟩
  | 5 => ⟨((846168305920207/2251799813685248), (161418093710115/562949953421312)), (5174761/1125899906842624), by norm_num⟩
  | 6 => ⟨((66415314650515/1125899906842624), (242627029400135/1125899906842624)), (27426663/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-402300069/268435456), (-126300221/4194304)), (3/268435456), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-104224539/67108864), (-1047065775/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((931831427540643/4503599627370496), (24940451031031/562949953421312)), (8858627/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4416492673/8589934592), (-472829381/4294967296)), (11/2147483648), by norm_num⟩
  | 2 => ⟨((2743643003/4294967296), (1174936873/8589934592)), (57/8589934592), by norm_num⟩
  | 3 => ⟨((-2272565581/4294967296), (-7603147/67108864)), (49/8589934592), by norm_num⟩
  | 4 => ⟨((1411778331/4294967296), (604579537/8589934592)), (63/17179869184), by norm_num⟩
  | 5 => ⟨((-1403254945/8589934592), (-1201858969/34359738368)), (65/34359738368), by norm_num⟩
  | 6 => ⟨((4649276725/68719476736), (62218903/4294967296)), (7/8589934592), by norm_num⟩
  | 7 => ⟨((-6601724943/274877906944), (-1413560373/274877906944)), (41/137438953472), by norm_num⟩
  | 8 => ⟨((4101167553/549755813888), (878141393/549755813888)), (53/549755813888), by norm_num⟩
  | 9 => ⟨((-2264670783/1099511627776), (-484910975/1099511627776)), (61/2199023255552), by norm_num⟩
  | 10 => ⟨((2250998195/4398046511104), (963966805/8796093022208)), (63/8796093022208), by norm_num⟩
  | 11 => ⟨((-508501853/4398046511104), (-54440171/2199023255552)), (59/35184372088832), by norm_num⟩
  | 12 => ⟨((6739091391/281474976710656), (721486629/140737488355328)), (25/70368744177664), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581952724385157/10141204801825835211973625643008), (274766060551/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222446673305675/79228162514264337593543950336), (81362809965/158456325028528675187087900672)), (5765/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890646947460577/39614081257132168796771975168), (366082438233/39614081257132168796771975168)), (12971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890478477524535/2475880078570760549798248448), (97225241069/618970019642690137449562112)), (6891/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772144601204475/154742504910672534362390528), (194415826447/77371252455336267181195264)), (13783/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775223792945025/4835703278458516698824704), (364456048633/9671406556917033397649408)), (12921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314892735098067/151115727451828646838272), (318825436163/604462909807314587353088)), (11307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944531480795395/37778931862957161709568), (129488340835/18889465931478580854784)), (9187/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162311552638975/590295810358705651712), (194172169965/2361183241434822606848)), (13781/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50711190248619/18446744073709551616), (133444359021/147573952589676412928)), (9475/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456277887055905/18446744073709551616), (333463942165/36893488147419103232)), (2961/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912248843938057/4611686018427387904), (749889963769/9223372036854775808)), (26651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398936312238301/288230376151711744), (749385412759/1152921504606846976)), (13327/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196119164676991/144115188075855872), (655145071921/144115188075855872)), (23325/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493942879758465/36028797018963968), (981584417513/36028797018963968)), (34993/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492135813591831/9007199254740992), (76562499799/562949953421312)), (43751/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116846606946651/2251799813685248), (2444068636799/4503599627370496)), (87529/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112346820947237/1125899906842624), (912827566761/562949953421312)), (16421/281474976710656), by norm_num⟩
  | 0 => ⟨((2197801880822141/2251799813685248), (1810915878931/562949953421312)), (263035/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2197801880822141/2251799813685248), (1810915878931/562949953421312)), (1003398903853606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2145075511299149/2251799813685248), (14139922387547/2251799813685248)), (128787/562949953421312), by norm_num⟩
  | 2 => ⟨((255415078629927/281474976710656), (13469759194783/1125899906842624)), (30873/70368744177664), by norm_num⟩
  | 3 => ⟨((1853820854783349/2251799813685248), (48890734715623/2251799813685248)), (1816579/2251799813685248), by norm_num⟩
  | 4 => ⟨((1525118457163469/2251799813685248), (40249876152699/1125899906842624)), (767481/562949953421312), by norm_num⟩
  | 5 => ⟨((1030067630418441/2251799813685248), (109043137220199/2251799813685248)), (547243/281474976710656), by norm_num⟩
  | 6 => ⟨((931831427540643/4503599627370496), (24940451031031/562949953421312)), (8858627/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-104224539/67108864), (-1047065775/33554432)), (1/134217728), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215163547/134217728), (-67549587/2097152)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((635275350259807/4503599627370496), (-646592490920701/4503599627370496)), (12858907/4503599627370496), by norm_num⟩
  | 1 => ⟨((-776981879/2147483648), (3163293827/8589934592)), (65/8589934592), by norm_num⟩
  | 2 => ⟨((3985838343/8589934592), (-2028422117/4294967296)), (43/4294967296), by norm_num⟩
  | 3 => ⟨((-3407824499/8589934592), (3468533337/8589934592)), (75/8589934592), by norm_num⟩
  | 4 => ⟨((2185224315/8589934592), (-4344049/16777216)), (25/4294967296), by norm_num⟩
  | 5 => ⟨((-2241995881/17179869184), (1140968007/8589934592)), (53/17179869184), by norm_num⟩
  | 6 => ⟨((3833737263/68719476736), (-1951016771/34359738368)), (93/68719476736), by norm_num⟩
  | 7 => ⟨((-2809526265/137438953472), (2859576693/137438953472)), (35/68719476736), by norm_num⟩
  | 8 => ⟨((1801573147/274877906944), (-3667334701/549755813888)), (23/137438953472), by norm_num⟩
  | 9 => ⟨((-1026876419/549755813888), (4180679015/2199023255552)), (27/549755813888), by norm_num⟩
  | 10 => ⟨((2107108809/4398046511104), (-4289291981/8796093022208)), (113/8796093022208), by norm_num⟩
  | 11 => ⟨((-3930638099/35184372088832), (2000330311/17592186044416)), (27/8796093022208), by norm_num⟩
  | 12 => ⟨((1680314611/70368744177664), (-3420497297/140737488355328)), (47/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395471889758183/2535301200456458802993406410752), (-64660548709/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889747728808359/316912650057057350374175801344), (-612655573743/316912650057057350374175801344)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118159952907143/2475880078570760549798248448), (-689139785207/19807040628566084398385987584)), (12985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945192627596587/1237940039285380274899124224), (-1464182489467/2475880078570760549798248448)), (13797/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886025666910253/77371252455336267181195264), (-182989132115/19342813113834066795298816)), (6899/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550360099877205/9671406556917033397649408), (-343033070821/2417851639229258349412352)), (12937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314873585580547/151115727451828646838272), (-600164806429/302231454903657293676544)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888938400152309/75557863725914323419136), (-243749908987/9444732965739290427392)), (575/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1298398921722103/4722366482869645213696), (-731015151329/2361183241434822606848)), (6901/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622629399165295/590295810358705651712), (-502382396051/147573952589676412928)), (18981/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912475248380153/36893488147419103232), (-2510769362627/73786976294838206464)), (5933/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228039530429083/1152921504606846976), (-2823045254453/9223372036854775808)), (26705/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595563478109421/1152921504606846976), (-2821083636781/1152921504606846976)), (13357/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195959748721295/144115188075855872), (-2466243053123/144115188075855872)), (23385/144115188075855872), by norm_num⟩
  | 4 => ⟨((373425756180027/9007199254740992), (-1847479272725/18014398509481984)), (35099/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491834719470949/9007199254740992), (-4610997116951/9007199254740992)), (21955/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116543608045079/2251799813685248), (-4599464488025/2251799813685248)), (10991/562949953421312), by norm_num⟩
  | 1 => ⟨((1111887589278605/1125899906842624), (-13740862902663/2251799813685248)), (66083/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097963715002395/1125899906842624), (-13626198749005/1125899906842624)), (265433/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1097963715002395/1125899906842624), (-13626198749005/1125899906842624)), (1012546547896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2141111547916653/2251799813685248), (-13288101108183/562949953421312)), (65515/281474976710656), by norm_num⟩
  | 2 => ⟨((1017304792078081/1125899906842624), (-101079346608709/2251799813685248)), (1021457/2251799813685248), by norm_num⟩
  | 3 => ⟨((916915238320219/1125899906842624), (-91330057903215/1125899906842624)), (1937575/2251799813685248), by norm_num⟩
  | 4 => ⟨((739312944008947/1125899906842624), (-148755535548385/1125899906842624)), (3470205/2251799813685248), by norm_num⟩
  | 5 => ⟨((116452496495365/281474976710656), (-97679102960683/562949953421312)), (5474341/2251799813685248), by norm_num⟩
  | 6 => ⟨((635275350259807/4503599627370496), (-646592490920701/4503599627370496)), (12858907/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-215163547/134217728), (-67549587/2097152)), (1/134217728), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-110690087/67108864), (-4448081151/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-265608653429061/9007199254740992), (-106896893419449/562949953421312)), (36034909/4503599627370496), by norm_num⟩
  | 1 => ⟨((41780261/536870912), (4304611665/8589934592)), (183/8589934592), by norm_num⟩
  | 2 => ⟨((-13782563/134217728), (-2840029241/4294967296)), (61/2147483648), by norm_num⟩
  | 3 => ⟨((775956777/8589934592), (156145833/268435456)), (217/8589934592), by norm_num⟩
  | 4 => ⟨((-511948605/8589934592), (-6593244881/17179869184)), (289/17179869184), by norm_num⟩
  | 5 => ⟨((1080849375/34359738368), (6959980491/34359738368)), (307/34359738368), by norm_num⟩
  | 6 => ⟨((-475403911/34359738368), (-3061297921/34359738368)), (273/68719476736), by norm_num⟩
  | 7 => ⟨((2800487/536870912), (288533597/8589934592)), (13/8589934592), by norm_num⟩
  | 8 => ⟨((-946002655/549755813888), (-11897761/1073741824)), (277/549755813888), by norm_num⟩
  | 9 => ⟨((1109580107/2199023255552), (3572494037/1099511627776)), (327/2199023255552), by norm_num⟩
  | 10 => ⟨((-585649103/4398046511104), (-3771206629/4398046511104)), (87/2199023255552), by norm_num⟩
  | 11 => ⟨((1124044769/35184372088832), (7238131269/35184372088832)), (21/2199023255552), by norm_num⟩
  | 12 => ⟨((-988806195/140737488355328), (-3183640563/70368744177664)), (149/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225343001/10141204801825835211973625643008), (-2246823488809/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444855255198517/158456325028528675187087900672), (-2660864738677/633825300114114700748351602688)), (5779/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890475344741535/39614081257132168796771975168), (-1496515779865/19807040628566084398385987584)), (13005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890295904169293/2475880078570760549798248448), (-3179560218135/2475880078570760549798248448)), (3455/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771961751876061/154742504910672534362390528), (-3178957510753/154742504910672534362390528)), (13823/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550275871580783/9671406556917033397649408), (-1489816196491/4835703278458516698824704)), (6481/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259420397485093/604462909807314587353088), (-1303269093297/302231454903657293676544)), (22689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236102222572619/9444732965739290427392), (-2117212252517/37778931862957161709568)), (2305/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((649154027771705/2361183241434822606848), (-1587384291661/2361183241434822606848)), (13835/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101406487894491/36893488147419103232), (-4363601347053/590295810358705651712)), (38061/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824792528921395/73786976294838206464), (-2725972155447/36893488147419103232)), (2975/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824137188199669/9223372036854775808), (-3064961138843/4611686018427387904)), (26791/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24927855446529/18014398509481984), (-3062765205661/576460752303423488)), (26811/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195799730187275/144115188075855872), (-5354900974397/144115188075855872)), (46965/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493459245001761/36028797018963968), (-8022481976783/36028797018963968)), (8817/4503599627370496), by norm_num⟩
  | 3 => ⟨((1491523448000227/9007199254740992), (-10010846143797/9007199254740992)), (11041/1125899906842624), by norm_num⟩
  | 2 => ⟨((1116222554340045/2251799813685248), (-9984992201101/2251799813685248)), (44283/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111381685841869/1125899906842624), (-14912960387963/1125899906842624)), (133443/1125899906842624), by norm_num⟩
  | 0 => ⟨((548427705255331/562949953421312), (-29568450973679/1125899906842624)), (33659/140737488355328), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((548427705255331/562949953421312), (-29568450973679/1125899906842624)), (128398895800542787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((533891818876211/562949953421312), (-3600710333329/70368744177664)), (538795/1125899906842624), by norm_num⟩
  | 2 => ⟨((1009719266097371/1125899906842624), (-218550415991943/2251799813685248)), (1077107/1125899906842624), by norm_num⟩
  | 3 => ⟨((1789842807734577/2251799813685248), (-195998386978733/1125899906842624)), (4282005/2251799813685248), by norm_num⟩
  | 4 => ⟨((1354416936652451/2251799813685248), (-623157176103219/2251799813685248)), (8297939/2251799813685248), by norm_num⟩
  | 5 => ⟨((642206453421533/2251799813685248), (-374817791697663/1125899906842624)), (7287411/1125899906842624), by norm_num⟩
  | 6 => ⟨((-265608653429061/9007199254740992), (-106896893419449/562949953421312)), (36034909/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-110690087/67108864), (-4448081151/134217728)), (1/67108864), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-56791929/33554432), (-2282183665/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-176628610383717/1125899906842624), (-108372749131315/1125899906842624)), (37173721/4503599627370496), by norm_num⟩
  | 1 => ⟨((3649285461/8589934592), (279883237/1073741824)), (97/4294967296), by norm_num⟩
  | 2 => ⟨((-4941224113/8589934592), (-3031751425/8589934592)), (265/8589934592), by norm_num⟩
  | 3 => ⟨((557545123/1073741824), (2736711685/8589934592)), (121/4294967296), by norm_num⟩
  | 4 => ⟨((-3019720365/8589934592), (-1852788157/8589934592)), (165/8589934592), by norm_num⟩
  | 5 => ⟨((3271021737/17179869184), (2006977337/17179869184)), (181/17179869184), by norm_num⟩
  | 6 => ⟨((-46135891/536870912), (-1811665127/34359738368)), (165/34359738368), by norm_num⟩
  | 7 => ⟨((571146555/17179869184), (1401737175/68719476736)), (129/68719476736), by norm_num⟩
  | 8 => ⟨((-1546693543/137438953472), (-1897987319/274877906944)), (177/274877906944), by norm_num⟩
  | 9 => ⟨((3723132231/1099511627776), (2284375529/1099511627776)), (215/1099511627776), by norm_num⟩
  | 10 => ⟨((-4032971595/4398046511104), (-618620361/1099511627776)), (235/4398046511104), by norm_num⟩
  | 11 => ⟨((1985725371/8796093022208), (2436734535/17592186044416)), (117/8796093022208), by norm_num⟩
  | 12 => ⟨((-896240665/17592186044416), (-274949977/8796093022208)), (213/70368744177664), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (-3375405635325/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889674873050633/316912650057057350374175801344), (-999284006997/158456325028528675187087900672)), (23149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890394898478215/39614081257132168796771975168), (-1124021673991/9903520314283042199192993792)), (26049/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945105046741235/1237940039285380274899124224), (-298516550477/154742504910672534362390528)), (6921/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442968890702239/38685626227668133590597632), (-4775334057571/154742504910672534362390528)), (27693/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550194667519693/9671406556917033397649408), (-279742925959/604462909807314587353088)), (25971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259348942366437/604462909807314587353088), (-978853041301/151115727451828646838272)), (22733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944350456799949/37778931862957161709568), (-3180345455529/37778931862957161709568)), (36957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649109873733703/2361183241434822606848), (-596112024707/590295810358705651712)), (27733/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811190657347135/295147905179352825856), (-3277298403755/295147905179352825856)), (38155/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912318907044697/36893488147419103232), (-8189293273519/73786976294838206464)), (47729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28499389630693/144115188075855872), (-4603760335883/4611686018427387904)), (53743/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595203753844325/1152921504606846976), (-2300182244073/288230376151711744)), (53803/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597820014878197/72057594037927936), (-8042998758693/144115188075855872)), (23573/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493213548571169/36028797018963968), (-12049223872865/36028797018963968)), (35427/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491205604473543/9007199254740992), (-15034808768993/9007199254740992)), (88805/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115888690531009/2251799813685248), (-14994745090869/2251799813685248)), (44581/1125899906842624), by norm_num⟩
  | 1 => ⟨((34713783244309/35184372088832), (-22392021851511/1125899906842624)), (134637/1125899906842624), by norm_num⟩
  | 0 => ⟨((547808102570401/562949953421312), (-22192023125915/562949953421312)), (8527/35184372088832), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((547808102570401/562949953421312), (-22192023125915/562949953421312)), (32527923718202103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1064397392807457/1125899906842624), (-86380467797695/1125899906842624)), (138141/281474976710656), by norm_num⟩
  | 2 => ⟨((249906811821879/281474976710656), (-163323833947535/1125899906842624)), (282387/281474976710656), by norm_num⟩
  | 3 => ⟨((107978066353131/140737488355328), (-290013265927445/1125899906842624)), (2333439/1125899906842624), by norm_num⟩
  | 4 => ⟨((294024860299485/562949953421312), (-890027867842545/2251799813685248)), (9565363/2251799813685248), by norm_num⟩
  | 5 => ⟨((262483497181947/2251799813685248), (-929710777715275/2251799813685248)), (4388325/562949953421312), by norm_num⟩
  | 6 => ⟨((-176628610383717/1125899906842624), (-108372749131315/1125899906842624)), (37173721/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-2282183665/67108864)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile031Terms1
