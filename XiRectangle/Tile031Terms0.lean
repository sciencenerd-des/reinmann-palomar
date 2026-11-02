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
namespace Reinmann.XiRectangle.Tile031Terms0
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
  | 0 => ⟨((-232581599/536870912), (-4673145785/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-1097368121570605/2251799813685248), (-481588231708193/1125899906842624)), (4044723/562949953421312), by norm_num⟩
  | 1 => ⟨((2901602247/8589934592), (2546779823/8589934592)), (45/8589934592), by norm_num⟩
  | 2 => ⟨((-4022474833/34359738368), (-882646627/8589934592)), (65/34359738368), by norm_num⟩
  | 3 => ⟨((3717556119/137438953472), (3262954779/137438953472)), (63/137438953472), by norm_num⟩
  | 4 => ⟨((-2576813543/549755813888), (-2261707905/549755813888)), (23/274877906944), by norm_num⟩
  | 5 => ⟨((714444417/1099511627776), (627078583/1099511627776)), (53/4398046511104), by norm_num⟩
  | 6 => ⟨((-1320573689/17592186044416), (-579543669/8796093022208)), (51/35184372088832), by norm_num⟩
  | 7 => ⟨((4184465963/562949953421312), (1836384275/281474976710656)), (21/140737488355328), by norm_num⟩
  | 8 => ⟨((-2900450785/4503599627370496), (-2545769165/4503599627370496)), (15/1125899906842624), by norm_num⟩
  | 9 => ⟨((3574114283/72057594037927936), (3137053723/72057594037927936)), (19/18014398509481984), by norm_num⟩
  | 10 => ⟨((-3963819581/1152921504606846976), (-1739551955/576460752303423488)), (87/1152921504606846976), by norm_num⟩
  | 11 => ⟨((999094679/4611686018427387904), (3507681551/18446744073709551616)), (45/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-1846719093/147573952589676412928), (-3241786103/295147905179352825856)), (85/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453610655/10141204801825835211973625643008), (-3153918526123/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781295397083249/633825300114114700748351602688), (-1871304817189/316912650057057350374175801344)), (5787/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946291791896589/19807040628566084398385987584), (-4210253110891/39614081257132168796771975168)), (6511/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946267698046991/1237940039285380274899124224), (-1118298476373/618970019642690137449562112)), (865/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774200667629931/154742504910672534362390528), (-4472968726021/154742504910672534362390528)), (3461/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776187121444641/4835703278458516698824704), (-1048292195051/2417851639229258349412352)), (6491/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78828491258521/37778931862957161709568), (-1834391558343/302231454903657293676544)), (2841/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472949814840637/18889465931478580854784), (-5961323026683/75557863725914323419136)), (2309/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300543160036803/4722366482869645213696), (-1117649643185/1180591620717411303424)), (6931/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625575442397321/590295810358705651712), (-3073216310237/295147905179352825856)), (9535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828629624913129/73786976294838206464), (-1920519749327/18446744073709551616)), (5963/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828450553292649/9223372036854775808), (-1080126819321/1152921504606846976)), (13429/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599691903255939/1152921504606846976), (-8639356351015/1152921504606846976)), (13443/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199565503073965/144115188075855872), (-7557567471383/144115188075855872)), (5889/72057594037927936), by norm_num⟩
  | 4 => ⟨((46846825862127/1125899906842624), (-11332602901451/36028797018963968)), (8849/18014398509481984), by norm_num⟩
  | 3 => ⟨((374638959466443/2251799813685248), (-3539793109159/2251799813685248)), (11089/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123230053654753/2251799813685248), (-1768657174289/281474976710656)), (22261/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121830681029495/1125899906842624), (-5299736831907/281474976710656)), (525/17592186044416), by norm_num⟩
  | 0 => ⟨((1117504226032571/1125899906842624), (-2643577161807/70368744177664)), (68033/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117504226032571/1125899906842624), (-2643577161807/70368744177664)), (259525303367232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107582149681351/1125899906842624), (-83963659851705/1125899906842624)), (35041/281474976710656), by norm_num⟩
  | 2 => ⟨((270825211616159/281474976710656), (-10324702301297/70368744177664)), (148337/562949953421312), by norm_num⟩
  | 3 => ⟨((509037815313965/562949953421312), (-158944981514117/562949953421312)), (657957/1125899906842624), by norm_num⟩
  | 4 => ⟨((830823375505543/1125899906842624), (-287446532869725/562949953421312)), (195179/140737488355328), by norm_num⟩
  | 5 => ⟨((159767951868837/562949953421312), (-848449483883193/1125899906842624)), (3898981/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1097368121570605/2251799813685248), (-481588231708193/1125899906842624)), (4044723/562949953421312), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/536870912), (-4673145785/536870912)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-368633113/536870912), (-3703380415/268435456)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((47374385328903/281474976710656), (-1068006373098477/2251799813685248)), (462455/70368744177664), by norm_num⟩
  | 1 => ⟨((-794160185/4294967296), (4475879387/8589934592)), (65/8589934592), by norm_num⟩
  | 2 => ⟨((1744948277/17179869184), (-4917256097/17179869184)), (37/8589934592), by norm_num⟩
  | 3 => ⟨((-639007207/17179869184), (1800719325/17179869184)), (7/4294967296), by norm_num⟩
  | 4 => ⟨((351010585/34359738368), (-1978292379/68719476736)), (1/2147483648), by norm_num⟩
  | 5 => ⟨((-1233998535/549755813888), (3477402109/549755813888)), (29/274877906944), by norm_num⟩
  | 6 => ⟨((1807581273/4398046511104), (-2546877793/2199023255552)), (87/4398046511104), by norm_num⟩
  | 7 => ⟨((-1134760571/17592186044416), (1598874995/8796093022208)), (7/2199023255552), by norm_num⟩
  | 8 => ⟨((311665477/35184372088832), (-3513087435/140737488355328)), (63/140737488355328), by norm_num⟩
  | 9 => ⟨((-608710263/562949953421312), (1715342679/562949953421312)), (1/17592186044416), by norm_num⟩
  | 10 => ⟨((2139957041/18014398509481984), (-6030388949/18014398509481984)), (115/18014398509481984), by norm_num⟩
  | 11 => ⟨((-1709805893/144115188075855872), (2409112511/72057594037927936)), (47/72057594037927936), by norm_num⟩
  | 12 => ⟨((313068961/288230376151711744), (-3528907479/1152921504606846976)), (71/1152921504606846976), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583081351377037/10141204801825835211973625643008), (-100121704443/633825300114114700748351602688)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780909295161745/633825300114114700748351602688), (-1900164045847/633825300114114700748351602688)), (4331/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892149581640711/39614081257132168796771975168), (-1068775065345/19807040628566084398385987584)), (4873/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473018676378785/618970019642690137449562112), (-567746888101/618970019642690137449562112)), (2589/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886870234167705/77371252455336267181195264), (-2270808153095/154742504910672534362390528)), (5179/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551943327984659/9671406556917033397649408), (-2128692030475/9671406556917033397649408)), (607/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((630439665733125/302231454903657293676544), (-1862414912171/604462909807314587353088)), (2125/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891188378649645/75557863725914323419136), (-3026066827045/75557863725914323419136)), (6907/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300085855447977/4722366482869645213696), (-2269237387667/4722366482869645213696)), (2591/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624948039249761/590295810358705651712), (-389961651485/73786976294838206464)), (7127/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28560116508341/1152921504606846976), (-3898854210773/73786976294838206464)), (17823/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913786740395723/4611686018427387904), (-4385162803163/9223372036854775808)), (5015/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1598818413340477/1152921504606846976), (-1095963137419/288230376151711744)), (10035/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198805228330915/144115188075855872), (-3834396913797/144115188075855872)), (8787/72057594037927936), by norm_num⟩
  | 4 => ⟨((748983034820029/18014398509481984), (-5748647157497/36028797018963968)), (1649/2251799813685248), by norm_num⟩
  | 3 => ⟨((1497154476872735/9007199254740992), (-1795162349859/2251799813685248)), (33021/9007199254740992), by norm_num⟩
  | 2 => ⟨((280462451390231/562949953421312), (-7172909737345/2251799813685248)), (33085/2251799813685248), by norm_num⟩
  | 1 => ⟨((559906516086505/562949953421312), (-5370007146149/562949953421312)), (49785/1125899906842624), by norm_num⟩
  | 0 => ⟨((556839732676787/562949953421312), (-21402620656811/1125899906842624)), (50101/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((556839732676787/562949953421312), (-21402620656811/1125899906842624)), (191120149852561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1101184813893535/1125899906842624), (-10585159029405/281474976710656)), (25255/140737488355328), by norm_num⟩
  | 2 => ⟨((537709994256239/562949953421312), (-82822398722931/1125899906842624)), (205203/562949953421312), by norm_num⟩
  | 3 => ⟨((63819427629339/70368744177664), (-79109042057715/562949953421312)), (105549/140737488355328), by norm_num⟩
  | 4 => ⟨((451920452016173/562949953421312), (-286985015488237/1125899906842624)), (884463/562949953421312), by norm_num⟩
  | 5 => ⟨((1304854856498183/2251799813685248), (-230383530779421/562949953421312)), (7483731/2251799813685248), by norm_num⟩
  | 6 => ⟨((47374385328903/281474976710656), (-1068006373098477/2251799813685248)), (462455/70368744177664), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/536870912), (-3703380415/268435456)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-232581599/268435456), (-4673145785/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((30698543103127/562949953421312), (1877536608674597/4503599627370496)), (35831859/4503599627370496), by norm_num⟩
  | 1 => ⟨((-40585725/536870912), (-4964482143/8589934592)), (97/8589934592), by norm_num⟩
  | 2 => ⟨((900220187/17179869184), (6882233601/17179869184)), (137/17179869184), by norm_num⟩
  | 3 => ⟨((-831980113/34359738368), (-3180267211/17179869184)), (129/34359738368), by norm_num⟩
  | 4 => ⟨((288342335/34359738368), (2204393251/34359738368)), (91/68719476736), by norm_num⟩
  | 5 => ⟨((-639563765/274877906944), (-2444750347/137438953472)), (51/137438953472), by norm_num⟩
  | 6 => ⟨((591082427/1099511627776), (4518858161/1099511627776)), (3/34359738368), by norm_num⟩
  | 7 => ⟨((-234118353/2199023255552), (-7159391529/8796093022208)), (77/4398046511104), by norm_num⟩
  | 8 => ⟨((649113905/35184372088832), (4962512053/35184372088832)), (109/35184372088832), by norm_num⟩
  | 9 => ⟨((-399939087/140737488355328), (-191097291/8796093022208)), (137/281474976710656), by norm_num⟩
  | 10 => ⟨((443546641/1125899906842624), (3390938841/1125899906842624)), (77/1125899906842624), by norm_num⟩
  | 11 => ⟨((-447189969/9007199254740992), (-3418792287/9007199254740992)), (157/18014398509481984), by norm_num⟩
  | 12 => ⟨((826582577/144115188075855872), (6319269959/144115188075855872)), (37/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197855892514491/1267650600228229401496703205376), (1876713331639/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780630807936933/633825300114114700748351602688), (2225421205949/633825300114114700748351602688)), (11553/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945918131677391/19807040628566084398385987584), (625850170057/9903520314283042199192993792)), (12999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891741778317255/2475880078570760549798248448), (2659627560737/2475880078570760549798248448)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773407511325589/154742504910672534362390528), (664840608977/38685626227668133590597632)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775815574567603/4835703278458516698824704), (1246435295831/4835703278458516698824704)), (12955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630303071672733/302231454903657293676544), (2180980079221/604462909807314587353088)), (5669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945372194352699/37778931862957161709568), (885891117583/18889465931478580854784)), (4607/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299752811201411/4722366482869645213696), (1328605610841/2361183241434822606848)), (13825/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624490019355085/590295810358705651712), (3652914481023/590295810358705651712)), (2377/73786976294838206464), by norm_num⟩
  | 8 => ⟨((228409350719721/9223372036854775808), (1141254175767/18446744073709551616)), (23779/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826929075830795/9223372036854775808), (5134095034241/9223372036854775808)), (26765/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799086896380465/576460752303423488), (5132159150031/1152921504606846976)), (13391/576460752303423488), by norm_num⟩
  | 5 => ⟨((299560235835221/36028797018963968), (4488461472055/144115188075855872)), (23453/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497119159659109/36028797018963968), (3364168427769/18014398509481984)), (2201/2251799813685248), by norm_num⟩
  | 3 => ⟨((1496094998333685/9007199254740992), (4201399847027/4503599627370496)), (22043/4503599627370496), by norm_num⟩
  | 2 => ⟨((560394536015735/1125899906842624), (8391368628685/2251799813685248)), (44185/2251799813685248), by norm_num⟩
  | 1 => ⟨((1118218817489209/1125899906842624), (12558478836725/1125899906842624)), (16631/281474976710656), by norm_num⟩
  | 0 => ⟨((555239358363953/562949953421312), (25002683111917/1125899906842624)), (134039/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((555239358363953/562949953421312), (25002683111917/1125899906842624)), (511318211082076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1094713516407763/1125899906842624), (24660227155305/562949953421312)), (270361/1125899906842624), by norm_num⟩
  | 2 => ⟨((265557614962929/281474976710656), (95908646303393/1125899906842624)), (68679/140737488355328), by norm_num⟩
  | 3 => ⟨((496995814014873/562949953421312), (90485028773387/562949953421312)), (565165/562949953421312), by norm_num⟩
  | 4 => ⟨((424224741941589/562949953421312), (4992748495901/17592186044416)), (2359171/1125899906842624), by norm_num⟩
  | 5 => ⟨((1097368121570571/2251799813685248), (481588231708169/1125899906842624)), (9789423/2251799813685248), by norm_num⟩
  | 6 => ⟨((30698543103127/562949953421312), (1877536608674597/4503599627370496)), (35831859/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/268435456), (-4673145785/268435456)), (1/134217728), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-270018875/268435456), (-5425354245/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((21391645157423/281474976710656), (-402770617129023/1125899906842624)), (1897679/281474976710656), by norm_num⟩
  | 1 => ⟨((-1050675193/8589934592), (4945635233/8589934592)), (95/8589934592), by norm_num⟩
  | 2 => ⟨((845498245/8589934592), (-3979846423/8589934592)), (39/4294967296), by norm_num⟩
  | 3 => ⟨((-226796155/4294967296), (4270210479/17179869184)), (43/8589934592), by norm_num⟩
  | 4 => ⟨((1460057321/68719476736), (-6872638639/68719476736)), (35/17179869184), by norm_num⟩
  | 5 => ⟨((-939948643/137438953472), (2212217037/68719476736)), (23/34359738368), by norm_num⟩
  | 6 => ⟨((252131497/137438953472), (-4747234627/549755813888)), (101/549755813888), by norm_num⟩
  | 7 => ⟨((-463759989/1099511627776), (4365931079/2199023255552)), (95/2199023255552), by norm_num⟩
  | 8 => ⟨((1492785817/17592186044416), (-3513347501/8796093022208)), (155/17592186044416), by norm_num⟩
  | 9 => ⟨((-533899131/35184372088832), (1256558815/17592186044416)), (113/70368744177664), by norm_num⟩
  | 10 => ⟨((1374844005/562949953421312), (-1617882717/140737488355328)), (37/140737488355328), by norm_num⟩
  | 11 => ⟨((-201156915/562949953421312), (3787464411/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 12 => ⟨((431666087/9007199254740992), (-4063792543/18014398509481984)), (3/562949953421312), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197833183968175/1267650600228229401496703205376), (-1773458364237/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780415691477561/633825300114114700748351602688), (-1051248794923/316912650057057350374175801344)), (361/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1891594295548463/39614081257132168796771975168), (-295636752993/4951760157141521099596496896)), (12997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59108897909953/77371252455336267181195264), (-2512654061625/2475880078570760549798248448)), (13811/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443287629355679/38685626227668133590597632), (-2512363440813/154742504910672534362390528)), (6907/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96961891990695/604462909807314587353088), (-2355031959839/9671406556917033397649408)), (12953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630197715109739/302231454903657293676544), (-2060344219955/604462909807314587353088)), (1417/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472600520513451/18889465931478580854784), (-1673740252707/37778931862957161709568)), (18425/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649748085306869/2361183241434822606848), (-2510103928253/4722366482869645213696)), (6911/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812068641907291/295147905179352825856), (-3450570002655/590295810358705651712)), (4753/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826834104217469/73786976294838206464), (-4311978302137/73786976294838206464)), (23773/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913216793082105/4611686018427387904), (-4849278802099/9223372036854775808)), (26757/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798839338756447/576460752303423488), (-4847158175873/1152921504606846976)), (26773/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197808138665483/144115188075855872), (-1059719548213/36028797018963968)), (5861/36028797018963968), by norm_num⟩
  | 4 => ⟨((374117698710735/9007199254740992), (-3176774051169/18014398509481984)), (17601/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495286015849343/9007199254740992), (-7933591833853/9007199254740992)), (1377/281474976710656), by norm_num⟩
  | 2 => ⟨((1119982299228351/2251799813685248), (-7921082468941/2251799813685248)), (22079/1125899906842624), by norm_num⟩
  | 1 => ⟨((34906693133933/35184372088832), (-5925184926445/562949953421312)), (33235/562949953421312), by norm_num⟩
  | 0 => ⟨((1108091516934925/1125899906842624), (-23575842034013/1125899906842624)), (133877/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1108091516934925/1125899906842624), (-23575842034013/1125899906842624)), (510700230125045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2129045185941/2199023255552), (-23202942289735/562949953421312)), (269127/1125899906842624), by norm_num⟩
  | 2 => ⟨((263367455327961/281474976710656), (-5616142582497/70368744177664)), (33957/70368744177664), by norm_num⟩
  | 3 => ⟨((122315952221567/140737488355328), (-168155245400071/1125899906842624)), (1103445/1125899906842624), by norm_num⟩
  | 4 => ⟨((825331014365137/1125899906842624), (-292289839793525/1125899906842624)), (4495255/2251799813685248), by norm_num⟩
  | 5 => ⟨((264560787866613/562949953421312), (-857041975043463/2251799813685248)), (8924401/2251799813685248), by norm_num⟩
  | 6 => ⟨((21391645157423/281474976710656), (-402770617129023/1125899906842624)), (1897679/281474976710656), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/268435456), (-5425354245/268435456)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-75151839/67108864), (-1509988327/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-641520490843019/2251799813685248), (716721799085343/4503599627370496)), (16269189/2251799813685248), by norm_num⟩
  | 1 => ⟨((548100669/1073741824), (-2449403897/8589934592)), (113/8589934592), by norm_num⟩
  | 2 => ⟨((-3928258255/8589934592), (2194371313/8589934592)), (103/8589934592), by norm_num⟩
  | 3 => ⟨((1173082321/4294967296), (-1310595193/8589934592)), (125/17179869184), by norm_num⟩
  | 4 => ⟨((-2101881357/17179869184), (2348271347/34359738368)), (57/17179869184), by norm_num⟩
  | 5 => ⟨((753213165/17179869184), (-1683014969/68719476736)), (83/68719476736), by norm_num⟩
  | 6 => ⟨((-1799435761/137438953472), (2010372005/274877906944)), (101/274877906944), by norm_num⟩
  | 7 => ⟨((921187447/274877906944), (-2058344615/1099511627776)), (105/1099511627776), by norm_num⟩
  | 8 => ⟨((-1650546331/2199023255552), (461007307/1099511627776)), (3/137438953472), by norm_num⟩
  | 9 => ⟨((164299001/1099511627776), (-2936939405/35184372088832)), (155/35184372088832), by norm_num⟩
  | 10 => ⟨((-3768118923/140737488355328), (526228899/35184372088832)), (113/140737488355328), by norm_num⟩
  | 11 => ⟨((4910227463/1125899906842624), (-1371455437/562949953421312)), (149/1125899906842624), by norm_num⟩
  | 12 => ⟨((-2932648851/4503599627370496), (1638212177/4503599627370496)), (91/4503599627370496), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (428585573031/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780233278979595/633825300114114700748351602688), (2032031851497/316912650057057350374175801344)), (1447/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236423589846109/4951760157141521099596496896), (2285796305349/19807040628566084398385987584)), (6513/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891265854237217/2475880078570760549798248448), (4856759351673/2475880078570760549798248448)), (3461/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443232782114297/38685626227668133590597632), (1214032918191/38685626227668133590597632)), (1731/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551184052931043/9671406556917033397649408), (568994555039/1208925819614629174706176)), (12987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260214447123899/604462909807314587353088), (995573694143/151115727451828646838272)), (1421/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1890106969611857/75557863725914323419136), (1617494489645/18889465931478580854784)), (18481/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299273948711447/4722366482869645213696), (4851388573035/4722366482869645213696)), (3467/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811915143645227/295147905179352825856), (3334439831173/295147905179352825856)), (2385/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1826448198014379/73786976294838206464), (8333429406369/73786976294838206464)), (5967/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825996473475241/9223372036854775808), (9371435407333/9223372036854775808)), (6719/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399309464593851/288230376151711744), (4683421392401/576460752303423488)), (13453/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197418257411029/144115188075855872), (4095409148699/72057594037927936)), (23577/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495877657057625/36028797018963968), (12275883091553/36028797018963968)), (17717/18014398509481984), by norm_num⟩
  | 3 => ⟨((747265035148615/4503599627370496), (15326737632103/9007199254740992)), (44413/9007199254740992), by norm_num⟩
  | 2 => ⟨((34975144616385/70368744177664), (7649768103571/1125899906842624)), (44595/2251799813685248), by norm_num⟩
  | 1 => ⟨((557896782390567/562949953421312), (5720301660769/281474976710656)), (67345/1125899906842624), by norm_num⟩
  | 0 => ⟨((552717546474255/562949953421312), (45489463277129/1125899906842624)), (34127/281474976710656), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((552717546474255/562949953421312), (45489463277129/1125899906842624)), (130184174657726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((135438044496543/140737488355328), (89325256641947/1125899906842624)), (279085/1125899906842624), by norm_num⟩
  | 2 => ⟨((1035618424737889/1125899906842624), (171923461546969/1125899906842624)), (145359/281474976710656), by norm_num⟩
  | 3 => ⟨((926323768825105/1125899906842624), (316275191676775/1125899906842624)), (311799/281474976710656), by norm_num⟩
  | 4 => ⟨((336639928297873/562949953421312), (260212498250845/562949953421312)), (344117/140737488355328), by norm_num⟩
  | 5 => ⟨((162060221521369/1125899906842624), (622420634168285/1125899906842624)), (1459363/281474976710656), by norm_num⟩
  | 6 => ⟨((-641520490843019/2251799813685248), (716721799085343/4503599627370496)), (16269189/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-1509988327/67108864)), (1/134217728), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-326469549/268435456), (-6559589411/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((15998881878621/70368744177664), (428051188978979/2251799813685248)), (4431645/1125899906842624), by norm_num⟩
  | 1 => ⟨((-950085041/2147483648), (-397181107/1073741824)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((3697560247/8589934592), (772878747/2147483648)), (17/2147483648), by norm_num⟩
  | 3 => ⟨((-2398373337/8589934592), (-1002635065/4294967296)), (23/4294967296), by norm_num⟩
  | 4 => ⟨((2333509509/17179869184), (3902075497/34359738368)), (23/8589934592), by norm_num⟩
  | 5 => ⟨((-3632639869/68719476736), (-3037235325/68719476736)), (73/68719476736), by norm_num⟩
  | 6 => ⟨((589065899/34359738368), (492515587/34359738368)), (49/137438953472), by norm_num⟩
  | 7 => ⟨((-655011035/137438953472), (-2190608181/549755813888)), (7/68719476736), by norm_num⟩
  | 8 => ⟨((2549185241/2199023255552), (1065681673/1099511627776)), (7/274877906944), by norm_num⟩
  | 9 => ⟨((-68895631/274877906944), (-1843307363/8796093022208)), (99/17592186044416), by norm_num⟩
  | 10 => ⟨((1716028257/35184372088832), (717382101/17592186044416)), (79/70368744177664), by norm_num⟩
  | 11 => ⟨((-2428535855/281474976710656), (-2030488889/281474976710656)), (29/140737488355328), by norm_num⟩
  | 12 => ⟨((3150475045/2251799813685248), (2634099291/2251799813685248)), (19/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769417651/5070602400912917605986812821504), (226773757509/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780092731628047/633825300114114700748351602688), (268755163511/158456325028528675187087900672)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472807776491061/9903520314283042199192993792), (1209266986581/39614081257132168796771975168)), (6491/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891099016812585/2475880078570760549798248448), (160585834731/309485009821345068724781056)), (13795/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772764995272263/154742504910672534362390528), (1284507276075/154742504910672534362390528)), (3449/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551029051072303/9671406556917033397649408), (602017494279/4835703278458516698824704)), (12935/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315019892053925/151115727451828646838272), (1053340067799/604462909807314587353088)), (11319/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889889192754317/75557863725914323419136), (855660204885/37778931862957161709568)), (18395/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324777960415551/1180591620717411303424), (160397229067/590295810358705651712)), (13799/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811804690278307/295147905179352825856), (1763861889843/590295810358705651712)), (593/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1826175048305739/73786976294838206464), (2204066165271/73786976294838206464)), (5931/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456423319858891/2305843009213693952), (1239264096285/4611686018427387904)), (3337/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399234945934677/288230376151711744), (619305247997/288230376151711744)), (1669/72057594037927936), by norm_num⟩
  | 5 => ⟨((299290798699447/36028797018963968), (541524649237/36028797018963968)), (1461/9007199254740992), by norm_num⟩
  | 4 => ⟨((1495506551939803/36028797018963968), (811552606573/9007199254740992)), (35081/36028797018963968), by norm_num⟩
  | 3 => ⟨((747043128493597/4503599627370496), (4052627123055/9007199254740992)), (21941/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237581683832885/4503599627370496), (4044932573237/2251799813685248)), (21965/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115247693643221/1125899906842624), (6048195054011/1125899906842624)), (132029/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209282028086599/2251799813685248), (24039540059027/2251799813685248)), (265019/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2209282028086599/2251799813685248), (24039540059027/2251799813685248)), (1010967263228606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((270913801400107/281474976710656), (47171265840863/2251799813685248)), (525689/2251799813685248), by norm_num⟩
  | 2 => ⟨((2085002965914115/2251799813685248), (90802721400985/2251799813685248)), (1033955/2251799813685248), by norm_num⟩
  | 3 => ⟨((481724908147555/562949953421312), (168153440890719/2251799813685248)), (1998123/2251799813685248), by norm_num⟩
  | 4 => ⟨((204540085668333/281474976710656), (287782956106415/2251799813685248)), (1859035/1125899906842624), by norm_num⟩
  | 5 => ⟨((576144988488465/1125899906842624), (209123919944049/1125899906842624)), (6353987/2251799813685248), by norm_num⟩
  | 6 => ⟨((15998881878621/70368744177664), (428051188978979/2251799813685248)), (4431645/1125899906842624), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-326469549/268435456), (-6559589411/268435456)), (1/134217728), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-348872399/268435456), (-3504859339/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((683408104726033/4503599627370496), (-510012861599629/2251799813685248)), (9606083/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2710546881/8589934592), (4045646405/8589934592)), (79/8589934592), by norm_num⟩
  | 2 => ⟨((2818211893/8589934592), (-4206342599/8589934592)), (85/8589934592), by norm_num⟩
  | 3 => ⟨((-488358907/2147483648), (2915614513/8589934592)), (61/8589934592), by norm_num⟩
  | 4 => ⟨((2031027597/17179869184), (-3031424969/17179869184)), (65/17179869184), by norm_num⟩
  | 5 => ⟨((-1689361263/34359738368), (5042936809/68719476736)), (111/68719476736), by norm_num⟩
  | 6 => ⟨((2341951993/137438953472), (-3495497431/137438953472)), (79/137438953472), by norm_num⟩
  | 7 => ⟨((-2782829865/549755813888), (129797903/17179869184)), (97/549755813888), by norm_num⟩
  | 8 => ⟨((2893366013/2199023255552), (-4318514425/2199023255552)), (13/274877906944), by norm_num⟩
  | 9 => ⟨((-334254749/1099511627776), (3991154797/8796093022208)), (99/8796093022208), by norm_num⟩
  | 10 => ⟨((1112101137/17592186044416), (-1659874617/17592186044416)), (21/8796093022208), by norm_num⟩
  | 11 => ⟨((-3363708077/281474976710656), (1255131721/70368744177664)), (129/281474976710656), by norm_num⟩
  | 12 => ⟨((1165772385/562949953421312), (-3479964055/1125899906842624)), (91/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582282826618775/10141204801825835211973625643008), (-1277205196911/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889981648442941/316912650057057350374175801344), (-1513439138197/633825300114114700748351602688)), (1443/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((59096421020591/1237940039285380274899124224), (-851210702275/19807040628566084398385987584)), (12989/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890944256507439/2475880078570760549798248448), (-1808582743331/2475880078570760549798248448)), (6901/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886305103477061/77371252455336267181195264), (-1808312787741/154742504910672534362390528)), (3451/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550883907278357/9671406556917033397649408), (-1695006456987/9671406556917033397649408)), (6471/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259952537670693/604462909807314587353088), (-741421960207/302231454903657293676544)), (5663/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944841356213515/37778931862957161709568), (-2409083863593/75557863725914323419136)), (2301/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298956932729823/4722366482869645213696), (-903171344809/2361183241434822606848)), (13809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811698150869729/295147905179352825856), (-2482957317475/590295810358705651712)), (18991/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825908581373449/73786976294838206464), (-3102551188547/73786976294838206464)), (23745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228174167694023/1152921504606846976), (-3488795671413/9223372036854775808)), (13361/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596639642969903/1152921504606846976), (-3486828535723/1152921504606846976)), (13367/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196900343853289/144115188075855872), (-3048763156123/144115188075855872)), (23405/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495111821163925/36028797018963968), (-1142181036313/9007199254740992)), (35133/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493592051050317/9007199254740992), (-712896997425/1125899906842624)), (43961/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118295452592939/2251799813685248), (-5691595824839/2251799813685248)), (88055/4503599627370496), by norm_num⟩
  | 1 => ⟨((2229003339499583/2251799813685248), (-8508491084143/1125899906842624)), (132419/2251799813685248), by norm_num⟩
  | 0 => ⟨((2206274635303801/2251799813685248), (-33803315317207/2251799813685248)), (133095/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2206274635303801/2251799813685248), (-33803315317207/2251799813685248)), (507717136863326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2161162405593269/2251799813685248), (-33119905561887/1125899906842624)), (529609/2251799813685248), by norm_num⟩
  | 2 => ⟨((1036112358304025/1125899906842624), (-127147172394525/2251799813685248)), (1047743/2251799813685248), by norm_num⟩
  | 3 => ⟨((474947733661123/562949953421312), (-14625940085875/140737488355328)), (1023349/1125899906842624), by norm_num⟩
  | 4 => ⟨((394622396512125/562949953421312), (-394866054674009/2251799813685248)), (484863/281474976710656), by norm_num⟩
  | 5 => ⟨((1037263684779853/2251799813685248), (-276797231884887/1125899906842624)), (1699631/562949953421312), by norm_num⟩
  | 6 => ⟨((683408104726033/4503599627370496), (-510012861599629/2251799813685248)), (9606083/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-348872399/268435456), (-3504859339/134217728)), (1/134217728), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile031Terms0
