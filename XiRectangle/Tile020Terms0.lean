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
namespace Reinmann.XiRectangle.Tile020Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5781/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5781/640))
  have he : value ((3/4), (5781/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

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

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-279097919/536870912), (-3361385565/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1338600723966211/2251799813685248), (7402594760367/562949953421312)), (1285105/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1769728313/4294967296), (-156588369/17179869184)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((2453364381/17179869184), (54269393/17179869184)), (13/34359738368), by norm_num⟩
  | 3 => ⟨((-1133695069/34359738368), (-50155569/68719476736)), (7/68719476736), by norm_num⟩
  | 4 => ⟨((3143270163/549755813888), (139060765/1099511627776)), (21/1099511627776), by norm_num⟩
  | 5 => ⟨((-1742999081/2199023255552), (-38555831/2199023255552)), (13/4398046511104), by norm_num⟩
  | 6 => ⟨((3221746397/35184372088832), (17816577/8796093022208)), (13/35184372088832), by norm_num⟩
  | 7 => ⟨((-2552165065/281474976710656), (-112909807/562949953421312)), (23/562949953421312), by norm_num⟩
  | 8 => ⟨((7076104077/9007199254740992), (156526229/9007199254740992)), (17/4503599627370496), by norm_num⟩
  | 9 => ⟨((-2179902929/36028797018963968), (-96440635/72057594037927936)), (23/72057594037927936), by norm_num⟩
  | 10 => ⟨((2417589711/576460752303423488), (106956087/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 11 => ⟨((-4874895977/18446744073709551616), (-107834633/18446744073709551616)), (15/9223372036854775808), by norm_num⟩
  | 12 => ⟨((563170067/36893488147419103232), (49830181/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197912323863903/1267650600228229401496703205376), (7202397029/2535301200456458802993406410752)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781168934426959/633825300114114700748351602688), (34182134005/633825300114114700748351602688)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892441776379895/39614081257132168796771975168), (4806636847/4951760157141521099596496896)), (1621/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473096321429711/618970019642690137449562112), (40854244929/2475880078570760549798248448)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221756398401695/19342813113834066795298816), (40851805813/154742504910672534362390528)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388058693560197/2417851639229258349412352), (38295976595/9671406556917033397649408)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261134494210283/604462909807314587353088), (33506388397/604462909807314587353088)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472900823539793/18889465931478580854784), (54443023283/75557863725914323419136)), (287/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((650198641771835/2361183241434822606848), (20414008663/2361183241434822606848)), (861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406344161277117/147573952589676412928), (28065809137/295147905179352825856)), (37/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1828383801933449/73786976294838206464), (8769270767/9223372036854775808)), (5919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228522209692649/1152921504606846976), (39454599529/4611686018427387904)), (6659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199927952458101/144115188075855872), (78891405689/1152921504606846976)), (6659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599667959375149/72057594037927936), (69009967853/144115188075855872)), (5827/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498764372826385/36028797018963968), (51737470529/18014398509481984)), (2185/9007199254740992), by norm_num⟩
  | 3 => ⟨((749078159550563/4503599627370496), (32318421999/2251799813685248)), (10925/9007199254740992), by norm_num⟩
  | 2 => ⟨((2245715165404499/4503599627370496), (258337532687/4503599627370496)), (21851/4503599627370496), by norm_num⟩
  | 1 => ⟨((2242679000684837/2251799813685248), (96745529099/562949953421312)), (32777/2251799813685248), by norm_num⟩
  | 0 => ⟨((279197850680387/281474976710656), (192967513511/562949953421312)), (8195/281474976710656), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((279197850680387/281474976710656), (192967513511/562949953421312)), (31261445165538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2215512907793947/2251799813685248), (765625643217/1125899906842624)), (65053/1125899906842624), by norm_num⟩
  | 2 => ⟨((17029763362927/17592186044416), (3013151497351/2251799813685248)), (256197/2251799813685248), by norm_num⟩
  | 3 => ⟨((2110117100922111/2251799813685248), (5833641918859/2251799813685248)), (496699/2251799813685248), by norm_num⟩
  | 4 => ⟨((494333479508879/562949953421312), (5466590546295/1125899906842624)), (233367/562949953421312), by norm_num⟩
  | 5 => ⟨((1736268857117587/2251799813685248), (19201129403259/2251799813685248)), (824223/1125899906842624), by norm_num⟩
  | 6 => ⟨((1338600723966211/2251799813685248), (7402594760367/562949953421312)), (1285105/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/536870912), (-3361385565/536870912)), (1/536870912), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/67108864), (-5327670071/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-867492350447913/2251799813685248), (236270453614363/1125899906842624)), (10873269/2251799813685248), by norm_num⟩
  | 1 => ⟨((908887631/2147483648), (-495089767/2147483648)), (3/536870912), by norm_num⟩
  | 2 => ⟨((-1997030241/8589934592), (271955851/2147483648)), (55/17179869184), by norm_num⟩
  | 3 => ⟨((1462641309/17179869184), (-796730773/17179869184)), (21/17179869184), by norm_num⟩
  | 4 => ⟨((-401718929/17179869184), (437649109/34359738368)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((2824533453/549755813888), (-769290703/274877906944)), (11/137438953472), by norm_num⟩
  | 6 => ⟨((-2068711441/2199023255552), (2253739253/4398046511104)), (67/4398046511104), by norm_num⟩
  | 7 => ⟨((5194769853/35184372088832), (-2829697873/35184372088832)), (87/35184372088832), by norm_num⟩
  | 8 => ⟨((-2853518999/140737488355328), (388592607/35184372088832)), (25/70368744177664), by norm_num⟩
  | 9 => ⟨((1393293795/562949953421312), (-758955757/562949953421312)), (51/1125899906842624), by norm_num⟩
  | 10 => ⟨((-306137937/1125899906842624), (667038497/4503599627370496)), (23/4503599627370496), by norm_num⟩
  | 11 => ⟨((3913622105/144115188075855872), (-1065915185/72057594037927936)), (19/36028797018963968), by norm_num⟩
  | 12 => ⟨((-716592223/288230376151711744), (390342507/288230376151711744)), (57/1152921504606846976), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (3442557440851/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890345087205319/316912650057057350374175801344), (4082496869347/633825300114114700748351602688)), (1447/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236487833689599/4951760157141521099596496896), (4592446478507/39614081257132168796771975168)), (6513/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472952966631841/618970019642690137449562112), (4879061240893/2475880078570760549798248448)), (3461/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886738536371847/77371252455336267181195264), (4878596266199/154742504910672534362390528)), (6925/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193961975423361/1208925819614629174706176), (4573189814801/9671406556917033397649408)), (3247/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630331078196907/302231454903657293676544), (2000523367755/302231454903657293676544)), (5685/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890834361324379/75557863725914323419136), (6500773678285/75557863725914323419136)), (9241/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299819373485681/4722366482869645213696), (4874768544329/4722366482869645213696)), (6935/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624580052700411/590295810358705651712), (6701487045951/590295810358705651712)), (9541/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827385113834929/73786976294838206464), (2093719522049/18446744073709551616)), (11935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827050102981683/9223372036854775808), (9419012468421/9223372036854775808)), (13439/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598290985773945/1152921504606846976), (2353900727075/288230376151711744)), (6727/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198339177478211/144115188075855872), (8234812898623/144115188075855872)), (5895/72057594037927936), by norm_num⟩
  | 4 => ⟨((374314475128747/9007199254740992), (6172265172945/18014398509481984)), (17719/36028797018963968), by norm_num⟩
  | 3 => ⟨((1496253376895507/9007199254740992), (7708592690303/4503599627370496)), (22209/9007199254740992), by norm_num⟩
  | 2 => ⟨((17514451884289/35184372088832), (7698462789307/1125899906842624)), (5575/562949953421312), by norm_num⟩
  | 1 => ⟨((1118366409999637/1125899906842624), (2880573406467/140737488355328)), (8419/281474976710656), by norm_num⟩
  | 0 => ⟨((555275025155463/562949953421312), (45885064764249/1125899906842624)), (8533/140737488355328), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555275025155463/562949953421312), (45885064764249/1125899906842624)), (32550812304449037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1093539459053599/1125899906842624), (45259494803013/562949953421312)), (17529/140737488355328), by norm_num⟩
  | 2 => ⟨((1054831654048575/1125899906842624), (87917306259879/562949953421312)), (294953/1125899906842624), by norm_num⟩
  | 3 => ⟨((960788788460291/1125899906842624), (329471410444183/1125899906842624)), (322399/562949953421312), by norm_num⟩
  | 4 => ⟨((723477887137593/1125899906842624), (562310086978659/1125899906842624)), (738927/562949953421312), by norm_num⟩
  | 5 => ⟨((11503443711987/70368744177664), (722655559647969/1125899906842624)), (1687723/562949953421312), by norm_num⟩
  | 6 => ⟨((-867492350447913/2251799813685248), (236270453614363/1125899906842624)), (10873269/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-5327670071/536870912)), (1/268435456), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-279097919/268435456), (-3361385565/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((795352727525437/2251799813685248), (17602130784877/1125899906842624)), (3148879/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4206058507/8589934592), (-186170461/8589934592)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((5830835191/17179869184), (64521765/4294967296)), (27/17179869184), by norm_num⟩
  | 3 => ⟨((-1347208991/8589934592), (-238523091/34359738368)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((3735256455/68719476736), (20666451/8589934592)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((-4142531969/274877906944), (-183358621/274877906944)), (3/34359738368), by norm_num⟩
  | 6 => ⟨((3828512473/1099511627776), (42364837/274877906944)), (47/2199023255552), by norm_num⟩
  | 7 => ⟨((-3032825859/4398046511104), (-33560077/1099511627776)), (39/8796093022208), by norm_num⟩
  | 8 => ⟨((4204389387/35184372088832), (93048291/17592186044416)), (7/8796093022208), by norm_num⟩
  | 9 => ⟨((-2590453911/140737488355328), (-114659841/140737488355328)), (9/70368744177664), by norm_num⟩
  | 10 => ⟨((359113165/140737488355328), (127161833/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | 11 => ⟨((-5793007193/18014398509481984), (-256412701/18014398509481984)), (11/4503599627370496), by norm_num⟩
  | 12 => ⟨((5353875471/144115188075855872), (118487827/72057594037927936)), (43/144115188075855872), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414717067/10141204801825835211973625643008), (57619176231/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780365817188295/633825300114114700748351602688), (68305764247/633825300114114700748351602688)), (1441/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236442291576819/4951760157141521099596496896), (76836849905/39614081257132168796771975168)), (6485/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891425452975197/2475880078570760549798248448), (81630490893/2475880078570760549798248448)), (6889/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773091440248345/154742504910672534362390528), (81620747613/154742504910672534362390528)), (3445/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551335102589243/9671406556917033397649408), (76509100299/9671406556917033397649408)), (6459/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630173686315439/302231454903657293676544), (66935114025/604462909807314587353088)), (1413/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890324392407707/75557863725914323419136), (108750160345/75557863725914323419136)), (287/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((162429782083299/590295810358705651712), (10193206155/590295810358705651712)), (861/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624058225935879/590295810358705651712), (112097697175/590295810358705651712)), (9471/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826736142055115/73786976294838206464), (140080778573/73786976294838206464)), (5919/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456581140163781/2305843009213693952), (78767025185/4611686018427387904)), (6659/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399392782040113/288230376151711744), (78731524943/576460752303423488)), (13319/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197715691943441/144115188075855872), (137700336289/144115188075855872)), (5827/72057594037927936), by norm_num⟩
  | 4 => ⟨((748167719198963/18014398509481984), (25798868451/4503599627370496)), (17481/36028797018963968), by norm_num⟩
  | 3 => ⟨((747561304763135/4503599627370496), (257709702655/9007199254740992)), (21853/9007199254740992), by norm_num⟩
  | 2 => ⟨((279956889376475/562949953421312), (514583429231/4503599627370496)), (10927/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116803661910913/1125899906842624), (384894296463/1125899906842624)), (65569/2251799813685248), by norm_num⟩
  | 0 => ⟨((1107756453896973/1125899906842624), (1531251286435/2251799813685248)), (131169/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1107756453896973/1125899906842624), (1531251286435/2251799813685248)), (500370034224700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1089904855227327/1125899906842624), (3013151497353/2251799813685248)), (129145/1125899906842624), by norm_num⟩
  | 2 => ⟨((2110117100922107/2251799813685248), (5833641918863/2251799813685248)), (500757/2251799813685248), by norm_num⟩
  | 3 => ⟨((1977333918035509/2251799813685248), (10933181092597/2251799813685248)), (941095/2251799813685248), by norm_num⟩
  | 4 => ⟨((1736268857117575/2251799813685248), (2400141175409/281474976710656)), (1661915/2251799813685248), by norm_num⟩
  | 5 => ⟨((83662545247887/140737488355328), (1850648690093/140737488355328)), (1295605/1125899906842624), by norm_num⟩
  | 6 => ⟨((795352727525437/2251799813685248), (17602130784877/1125899906842624)), (3148879/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/268435456), (-3361385565/268435456)), (1/268435456), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/134217728), (-7804895581/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-525228187536349/4503599627370496), (-1240261752670447/4503599627370496)), (14622755/4503599627370496), by norm_num⟩
  | 1 => ⟨((806162031/4294967296), (118978279/268435456)), (23/4294967296), by norm_num⟩
  | 2 => ⟨((-162183467/1073741824), (-191488153/536870912)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((174016147/2147483648), (1643670897/8589934592)), (11/4294967296), by norm_num⟩
  | 4 => ⟨((-2240545475/68719476736), (-5290772515/68719476736)), (73/68719476736), by norm_num⟩
  | 5 => ⟨((1442407533/137438953472), (3406067949/137438953472)), (49/137438953472), by norm_num⟩
  | 6 => ⟨((-1547643579/549755813888), (-1827284963/274877906944)), (27/274877906944), by norm_num⟩
  | 7 => ⟨((1423335001/2199023255552), (1680515255/1099511627776)), (51/2199023255552), by norm_num⟩
  | 8 => ⟨((-2290769313/17592186044416), (-676171241/2199023255552)), (21/4398046511104), by norm_num⟩
  | 9 => ⟨((409650109/17592186044416), (3869353353/70368744177664)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((-527445133/140737488355328), (-2490993593/281474976710656)), (41/281474976710656), by norm_num⟩
  | 11 => ⟨((1234749373/2251799813685248), (728927187/562949953421312)), (49/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1324834969/18014398509481984), (-3128434801/18014398509481984)), (27/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (-2567942920249/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780102476835163/633825300114114700748351602688), (-3043378099593/633825300114114700748351602688)), (2891/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472810453117769/9903520314283042199192993792), (-3423423166859/39614081257132168796771975168)), (3253/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472777517788515/618970019642690137449562112), (-1818468981077/1237940039285380274899124224)), (3457/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886387844131563/77371252455336267181195264), (-3636432648347/154742504910672534362390528)), (1729/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551038691958085/9671406556917033397649408), (-1704309361817/4835703278458516698824704)), (6485/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630043810178577/302231454903657293676544), (-1491002256079/302231454903657293676544)), (1419/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472475389627535/18889465931478580854784), (-2365600941/36893488147419103232)), (4613/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162390060901961/590295810358705651712), (-113521321691/147573952589676412928)), (6923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811810123543721/295147905179352825856), (-1248376746671/147573952589676412928)), (9523/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456546775230727/18446744073709551616), (-6239737075133/73786976294838206464)), (5955/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825704735934167/9223372036854775808), (-3508376353521/4611686018427387904)), (13407/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399237153643747/288230376151711744), (-7013063559309/1152921504606846976)), (13419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37411499113449/4503599627370496), (-3066140321207/72057594037927936)), (5877/72057594037927936), by norm_num⟩
  | 4 => ⟨((373876956546965/9007199254740992), (-4595060912531/18014398509481984)), (8829/18014398509481984), by norm_num⟩
  | 3 => ⟨((186759695181489/1125899906842624), (-2868282655307/2251799813685248)), (5529/2251799813685248), by norm_num⟩
  | 2 => ⟨((559383377820933/1125899906842624), (-11451351846309/2251799813685248)), (22185/2251799813685248), by norm_num⟩
  | 1 => ⟨((139396654182273/140737488355328), (-8561297031087/562949953421312)), (33445/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104339645824765/1125899906842624), (-4253441810575/140737488355328)), (33785/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104339645824765/1125899906842624), (-4253441810575/140737488355328)), (128879549266624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1082163852072841/1125899906842624), (-16687964512935/281474976710656)), (136637/1125899906842624), by norm_num⟩
  | 2 => ⟨((129521148493047/140737488355328), (-16039713522329/140737488355328)), (278861/1125899906842624), by norm_num⟩
  | 3 => ⟨((938965484754109/1125899906842624), (-118091186147439/562949953421312)), (576837/1125899906842624), by norm_num⟩
  | 4 => ⟨((733523525099751/1125899906842624), (-24621093574177/70368744177664)), (602069/562949953421312), by norm_num⟩
  | 5 => ⟨((680113761193261/2251799813685248), (-1026600747897029/2251799813685248)), (4823231/2251799813685248), by norm_num⟩
  | 6 => ⟨((-525228187536349/4503599627370496), (-1240261752670447/4503599627370496)), (14622755/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-7804895581/536870912)), (1/268435456), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-90182207/67108864), (-2172263909/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-521901633701611/2251799813685248), (67374641652111/562949953421312)), (13005217/2251799813685248), by norm_num⟩
  | 1 => ⟨((3567208077/8589934592), (-1842028079/8589934592)), (91/8589934592), by norm_num⟩
  | 2 => ⟨((-3195789425/8589934592), (1650235627/8589934592)), (83/8589934592), by norm_num⟩
  | 3 => ⟨((3817390643/17179869184), (-985608437/8589934592)), (101/17179869184), by norm_num⟩
  | 4 => ⟨((-854980729/8589934592), (882986625/17179869184)), (23/8589934592), by norm_num⟩
  | 5 => ⟨((4902143415/137438953472), (-2531359435/137438953472)), (67/68719476736), by norm_num⟩
  | 6 => ⟨((-731955157/68719476736), (1511862413/274877906944)), (41/137438953472), by norm_num⟩
  | 7 => ⟨((1498842953/549755813888), (-1547939311/1099511627776)), (43/549755813888), by norm_num⟩
  | 8 => ⟨((-1342783027/2199023255552), (1386767459/4398046511104)), (39/2199023255552), by norm_num⟩
  | 9 => ⟨((1069308535/8796093022208), (-2208669979/35184372088832)), (63/17592186044416), by norm_num⟩
  | 10 => ⟨((-3065509909/140737488355328), (395740535/35184372088832)), (23/35184372088832), by norm_num⟩
  | 11 => ⟨((1997329603/562949953421312), (-515688619/281474976710656)), (61/562949953421312), by norm_num⟩
  | 12 => ⟨((-4771645639/9007199254740992), (2463973243/9007199254740992)), (37/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646016907/5070602400912917605986812821504), (1735683514483/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779887311910009/633825300114114700748351602688), (2056568615769/316912650057057350374175801344)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890999541268099/39614081257132168796771975168), (4626704364835/39614081257132168796771975168)), (6513/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472713097374711/618970019642690137449562112), (4915196567087/2475880078570760549798248448)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886258852342563/77371252455336267181195264), (4914435013929/154742504910672534362390528)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550796511720783/9671406556917033397649408), (575809203239/1208925819614629174706176)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314968848049111/151115727451828646838272), (503731895923/75557863725914323419136)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472389021820411/18889465931478580854784), (6546997175407/75557863725914323419136)), (9241/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298860858767525/4722366482869645213696), (4908919976345/4722366482869645213696)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811631202759557/295147905179352825856), (6747606901827/590295810358705651712)), (9541/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825738521537949/73786976294838206464), (2107817786473/18446744073709551616)), (11935/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912599164852089/4611686018427387904), (9480727882811/9223372036854775808)), (13439/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798220009186203/576460752303423488), (2368790440821/288230376151711744)), (26909/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196720490433509/144115188075855872), (8284503395805/144115188075855872)), (5895/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494831695849949/36028797018963968), (12414225667279/36028797018963968)), (35441/36028797018963968), by norm_num⟩
  | 3 => ⟨((746611916095369/4503599627370496), (15495848606705/9007199254740992)), (22211/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117900224077691/2251799813685248), (15462934594401/2251799813685248)), (22303/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113841595497641/1125899906842624), (11556034660135/562949953421312)), (8421/140737488355328), by norm_num⟩
  | 0 => ⟨((137693749712111/140737488355328), (11473632267435/281474976710656)), (34145/281474976710656), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137693749712111/140737488355328), (11473632267435/281474976710656)), (130252839208507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((537927964229237/562949953421312), (44901965160335/562949953421312)), (69597/281474976710656), by norm_num⟩
  | 2 => ⟨((127609171329613/140737488355328), (171624653749739/1125899906842624)), (576439/1125899906842624), by norm_num⟩
  | 3 => ⟨((449741318453805/562949953421312), (155615110804319/562949953421312)), (1221073/1125899906842624), by norm_num⟩
  | 4 => ⟨((316282450565677/562949953421312), (497284312249273/1125899906842624)), (2626111/1125899906842624), by norm_num⟩
  | 5 => ⟨((135755111093949/1125899906842624), (279389490931101/562949953421312)), (10541291/2251799813685248), by norm_num⟩
  | 6 => ⟨((-521901633701611/2251799813685248), (67374641652111/562949953421312)), (13005217/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-90182207/67108864), (-2172263909/134217728)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-391763459/268435456), (-4718301155/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((153770830196837/2251799813685248), (1000282611988471/4503599627370496)), (9385411/4503599627370496), by norm_num⟩
  | 1 => ⟨((-570724905/4294967296), (-3712577985/8589934592)), (9/2147483648), by norm_num⟩
  | 2 => ⟨((1110579385/8589934592), (1806085795/4294967296)), (9/2147483648), by norm_num⟩
  | 3 => ⟨((-1440725131/17179869184), (-2342987119/8589934592)), (3/1073741824), by norm_num⟩
  | 4 => ⟨((1401760827/34359738368), (2279621207/17179869184)), (3/2147483648), by norm_num⟩
  | 5 => ⟨((-136385031/8589934592), (-1774375217/34359738368)), (39/68719476736), by norm_num⟩
  | 6 => ⟨((1415429419/274877906944), (4603699657/274877906944)), (13/68719476736), by norm_num⟩
  | 7 => ⟨((-1573884841/1099511627776), (-5119077649/1099511627776)), (59/1099511627776), by norm_num⟩
  | 8 => ⟨((1531319243/4398046511104), (4980632575/4398046511104)), (59/4398046511104), by norm_num⟩
  | 9 => ⟨((-1324359847/17592186044416), (-2153747439/8796093022208)), (53/17592186044416), by norm_num⟩
  | 10 => ⟨((1030834107/70368744177664), (104774975/2199023255552)), (21/35184372088832), by norm_num⟩
  | 11 => ⟨((-1458844037/562949953421312), (-4744906175/562949953421312)), (61/562949953421312), by norm_num⟩
  | 12 => ⟨((473129903/1125899906842624), (6155440721/4503599627370496)), (81/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693180315/10141204801825835211973625643008), (1657592087655/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779715862296873/633825300114114700748351602688), (1963665713559/633825300114114700748351602688)), (361/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((59087721703265/1237940039285380274899124224), (138052260211/2475880078570760549798248448)), (3249/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945324229796067/1237940039285380274899124224), (73329333943/77371252455336267181195264)), (6905/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110769649214313/9671406556917033397649408), (2346145294805/154742504910672534362390528)), (3453/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550606552478397/9671406556917033397649408), (2199093305415/9671406556917033397649408)), (6475/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259709828256789/604462909807314587353088), (1923788812353/604462909807314587353088)), (5667/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944644132381689/37778931862957161709568), (781343389001/18889465931478580854784)), (9211/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298661057790573/4722366482869645213696), (1171672488945/2361183241434822606848)), (3455/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622989410136001/590295810358705651712), (3220986225279/590295810358705651712)), (297/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1825399871743377/73786976294838206464), (4024563650269/73786976294838206464)), (2971/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228102614096645/1152921504606846976), (2262669970381/4611686018427387904)), (13375/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798033525831481/576460752303423488), (282654597997/72057594037927936)), (13383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196399144341793/144115188075855872), (1976970768485/72057594037927936)), (5859/72057594037927936), by norm_num⟩
  | 4 => ⟨((747179829736685/18014398509481984), (5924471220293/36028797018963968)), (17593/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492651218767881/9007199254740992), (7394327438741/9007199254740992)), (22021/9007199254740992), by norm_num⟩
  | 2 => ⟨((2234707366366257/4503599627370496), (14754911350083/4503599627370496)), (1379/140737488355328), by norm_num⟩
  | 1 => ⟨((278271675296167/281474976710656), (11024076221463/1125899906842624)), (66411/2251799813685248), by norm_num⟩
  | 0 => ⟨((550149146165843/562949953421312), (43760311354415/2251799813685248)), (33425/562949953421312), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((550149146165843/562949953421312), (43760311354415/2251799813685248)), (127506258250999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((67178351264883/70368744177664), (42765254320157/1125899906842624)), (266517/2251799813685248), by norm_num⟩
  | 2 => ⟨((512248660361233/562949953421312), (163305416927617/2251799813685248)), (264557/1125899906842624), by norm_num⟩
  | 3 => ⟨((1852611567031267/2251799813685248), (297195090051987/2251799813685248)), (519833/1125899906842624), by norm_num⟩
  | 4 => ⟨((742482674619857/1125899906842624), (489019546186151/2251799813685248)), (15509/17592186044416), by norm_num⟩
  | 5 => ⟨((109133922559541/281474976710656), (644974812391443/2251799813685248)), (3480471/2251799813685248), by norm_num⟩
  | 6 => ⟨((153770830196837/2251799813685248), (1000282611988471/4503599627370496)), (9385411/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-391763459/268435456), (-4718301155/268435456)), (1/268435456), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-418646879/268435456), (-5042078347/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1889363906628285/9007199254740992), (125544281827645/9007199254740992)), (7713511/4503599627370496), by norm_num⟩
  | 1 => ⟨((-7493632879/17179869184), (-497936239/17179869184)), (1/268435456), by norm_num⟩
  | 2 => ⟨((3895642877/8589934592), (258857325/8589934592)), (69/17179869184), by norm_num⟩
  | 3 => ⟨((-2700253877/8589934592), (-179426225/8589934592)), (25/8589934592), by norm_num⟩
  | 4 => ⟨((5615020085/34359738368), (186553173/17179869184)), (27/17179869184), by norm_num⟩
  | 5 => ⟨((-4670442409/68719476736), (-155170567/34359738368)), (47/68719476736), by norm_num⟩
  | 6 => ⟨((809325997/34359738368), (107556041/68719476736)), (67/274877906944), by norm_num⟩
  | 7 => ⟨((-7693467881/1099511627776), (-511214857/1099511627776)), (83/1099511627776), by norm_num⟩
  | 8 => ⟨((1999764589/1099511627776), (531520705/4398046511104)), (89/4398046511104), by norm_num⟩
  | 9 => ⟨((-7392699663/17592186044416), (-491229437/17592186044416)), (85/17592186044416), by norm_num⟩
  | 10 => ⟨((3074537357/35184372088832), (408593159/70368744177664)), (73/70368744177664), by norm_num⟩
  | 11 => ⟨((-4649687783/281474976710656), (-19310127/17592186044416)), (57/281474976710656), by norm_num⟩
  | 12 => ⟨((6445835955/2251799813685248), (428312323/2251799813685248)), (81/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238520483/10141204801825835211973625643008), (86428766773/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889781693137345/316912650057057350374175801344), (51185446799/316912650057057350374175801344)), (11527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890635701777383/39614081257132168796771975168), (115151402195/39614081257132168796771975168)), (1621/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945233267325071/1237940039285380274899124224), (122328899405/2475880078570760549798248448)), (13779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886066332349521/77371252455336267181195264), (7644187915/9671406556917033397649408)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550436402180549/9671406556917033397649408), (14329945401/1208925819614629174706176)), (6459/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259561161407785/604462909807314587353088), (50143184265/302231454903657293676544)), (1413/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((236130885426513/9444732965739290427392), (162921769723/75557863725914323419136)), (18367/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298480523558603/4722366482869645213696), (30538302199/1180591620717411303424)), (861/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1622741746814507/590295810358705651712), (41974686093/147573952589676412928)), (9471/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825091148767557/73786976294838206464), (209780597321/73786976294838206464)), (11839/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824474775538541/9223372036854775808), (235875596967/9223372036854775808)), (13319/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797861191438879/576460752303423488), (117858116977/576460752303423488)), (13319/576460752303423488), by norm_num⟩
  | 5 => ⟨((299024802208955/36028797018963968), (206072566637/144115188075855872)), (23309/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493913049771497/36028797018963968), (308750936779/36028797018963968)), (17483/18014398509481984), by norm_num⟩
  | 3 => ⟨((746049353660531/4503599627370496), (192656569357/4503599627370496)), (43711/9007199254740992), by norm_num⟩
  | 2 => ⟨((279202442927723/562949953421312), (768752939437/4503599627370496)), (43715/2251799813685248), by norm_num⟩
  | 1 => ⟨((278073060735589/281474976710656), (143557181267/281474976710656)), (65585/1125899906842624), by norm_num⟩
  | 0 => ⟨((2197588934833399/2251799813685248), (2278295221787/2251799813685248)), (262443/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2197588934833399/2251799813685248), (2278295221787/2251799813685248)), (1001140603072356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1072340424429069/1125899906842624), (4446892960249/2251799813685248)), (256391/1125899906842624), by norm_num⟩
  | 2 => ⟨((2042648791712171/2251799813685248), (4235352588097/1125899906842624)), (978803/2251799813685248), by norm_num⟩
  | 3 => ⟨((231611526260001/281474976710656), (3841965788421/562949953421312)), (1783145/2251799813685248), by norm_num⟩
  | 4 => ⟨((762273215872359/1125899906842624), (25290875103533/2251799813685248)), (739715/562949953421312), by norm_num⟩
  | 5 => ⟨((515943331210089/1125899906842624), (68491192086371/4503599627370496)), (2036483/1125899906842624), by norm_num⟩
  | 6 => ⟨((1889363906628285/9007199254740992), (125544281827645/9007199254740992)), (7713511/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-418646879/268435456), (-5042078347/268435456)), (1/134217728), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile020Terms0
