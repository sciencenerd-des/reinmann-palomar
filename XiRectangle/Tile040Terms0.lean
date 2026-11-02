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
namespace Reinmann.XiRectangle.Tile040Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((19/32), (7191/512))
  have he : value ((19/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-27619065/67108864), (-1306636157/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1420770187430437/2251799813685248), (455769870354387/2251799813685248)), (7938057/281474976710656), by norm_num⟩
  | 1 => ⟨((7337353/16777216), (-150640297/1073741824)), (11/536870912), by norm_num⟩
  | 2 => ⟨((-325495395/2147483648), (417663589/8589934592)), (1/134217728), by norm_num⟩
  | 3 => ⟨((601643241/17179869184), (-386003119/34359738368)), (61/34359738368), by norm_num⟩
  | 4 => ⟨((-104256829/17179869184), (133778487/68719476736)), (11/34359738368), by norm_num⟩
  | 5 => ⟨((924996187/1099511627776), (-296730179/1099511627776)), (51/1099511627776), by norm_num⟩
  | 6 => ⟨((-854877999/8796093022208), (68559229/2199023255552)), (49/8796093022208), by norm_num⟩
  | 7 => ⟨((677207171/70368744177664), (-108620883/35184372088832)), (5/8796093022208), by norm_num⟩
  | 8 => ⟨((-938808483/1125899906842624), (301161035/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | 9 => ⟨((578428847/9007199254740992), (-371109195/18014398509481984)), (9/2251799813685248), by norm_num⟩
  | 10 => ⟨((-641498119/144115188075855872), (102893317/72057594037927936)), (41/144115188075855872), by norm_num⟩
  | 11 => ⟨((1293534873/4611686018427387904), (-103738491/1152921504606846976)), (85/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-1195480067/73786976294838206464), (191749447/36893488147419103232)), (81/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791719834641543/5070602400912917605986812821504), (3687918434113/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890663070436601/316912650057057350374175801344), (4376438715755/633825300114114700748351602688)), (11579/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892618000755523/39614081257132168796771975168), (4923281874593/39614081257132168796771975168)), (6515/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892571759490291/2475880078570760549798248448), (1307690929927/618970019642690137449562112)), (1731/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((27722450012683/2417851639229258349412352), (5230512290953/154742504910672534362390528)), (27705/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552407873171509/9671406556917033397649408), (2451668942829/4835703278458516698824704)), (25983/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39415157565257/18889465931478580854784), (4290152988503/604462909807314587353088)), (22745/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945923110788797/37778931862957161709568), (1742749039573/18889465931478580854784)), (18489/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300577980613759/4722366482869645213696), (326737930879/295147905179352825856)), (27749/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812811334525707/295147905179352825856), (7187518022209/590295810358705651712)), (9545/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828687680987399/73786976294838206464), (1122915116463/9223372036854775808)), (11941/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828514523017831/9223372036854775808), (5052376312827/4611686018427387904)), (53787/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599754194311859/1152921504606846976), (10102893695575/1152921504606846976)), (53853/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74976132498435/9007199254740992), (8837934294883/144115188075855872)), (47195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499173579227693/36028797018963968), (1656586261983/4503599627370496)), (17735/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498643177570929/9007199254740992), (2069807108315/1125899906842624)), (44467/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123307501958165/2251799813685248), (8273638262837/1125899906842624)), (22331/562949953421312), by norm_num⟩
  | 1 => ⟨((70120134658503/70368744177664), (12396356661687/562949953421312)), (134961/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117588556813383/1125899906842624), (96623281481/2199023255552)), (273829/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117588556813383/1125899906842624), (96623281481/2199023255552)), (1044574741843795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107164840336651/1125899906842624), (24552963101297/281474976710656)), (4435/8796093022208), by norm_num⟩
  | 2 => ⟨((1080174541567679/1125899906842624), (193155198302287/1125899906842624)), (607753/562949953421312), by norm_num⟩
  | 3 => ⟨((1003169200703757/1125899906842624), (185310724789633/562949953421312)), (2749339/1125899906842624), by norm_num⟩
  | 4 => ⟨((771816554092533/1125899906842624), (660442408918449/1125899906842624)), (3354665/562949953421312), by norm_num⟩
  | 5 => ⟨((283358434801905/2251799813685248), (905480817841935/1125899906842624)), (8534949/562949953421312), by norm_num⟩
  | 6 => ⟨((-1420770187430437/2251799813685248), (455769870354387/2251799813685248)), (7938057/281474976710656), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-27619065/67108864), (-1306636157/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-21887591/33554432), (-64717791/4194304)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-1127798225061973/2251799813685248), (-321910723507963/2251799813685248)), (99576765/2251799813685248), by norm_num⟩
  | 1 => ⟨((590807433/1073741824), (84317941/536870912)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((-1298136613/4294967296), (-370530905/4294967296)), (15/536870912), by norm_num⟩
  | 3 => ⟨((950765891/8589934592), (135689935/4294967296)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((-261130773/8589934592), (-74535315/8589934592)), (101/34359738368), by norm_num⟩
  | 5 => ⟨((229505181/34359738368), (131016661/68719476736)), (91/137438953472), by norm_num⟩
  | 6 => ⟨((-1344731799/1099511627776), (-23989419/68719476736)), (17/137438953472), by norm_num⟩
  | 7 => ⟨((422096823/2199023255552), (240960645/4398046511104)), (11/549755813888), by norm_num⟩
  | 8 => ⟨((-463720757/17592186044416), (-132361163/17592186044416)), (99/35184372088832), by norm_num⟩
  | 9 => ⟨((226421921/70368744177664), (258513067/281474976710656)), (49/140737488355328), by norm_num⟩
  | 10 => ⟨((-1591999391/4503599627370496), (-113602253/1125899906842624)), (175/4503599627370496), by norm_num⟩
  | 11 => ⟨((317998199/9007199254740992), (45383575/4503599627370496)), (71/18014398509481984), by norm_num⟩
  | 12 => ⟨((-931617945/288230376151711744), (-265914417/288230376151711744)), (53/144115188075855872), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791563036083365/5070602400912917605986812821504), (-233131106641/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222619229441385/79228162514264337593543950336), (-1106184696669/158456325028528675187087900672)), (23159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892199170329417/39614081257132168796771975168), (-1244377372819/9903520314283042199192993792)), (52121/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892126759844803/2475880078570760549798248448), (-2644124060539/1237940039285380274899124224)), (55395/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773791809877311/154742504910672534362390528), (-5287847685137/154742504910672534362390528)), (55413/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551990703494313/9671406556917033397649408), (-4956931514697/9671406556917033397649408)), (25985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260920028021197/604462909807314587353088), (-2168444565079/302231454903657293676544)), (11373/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472813272876905/18889465931478580854784), (-3523322823723/37778931862957161709568)), (73961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650066574394767/2361183241434822606848), (-2642142201813/2361183241434822606848)), (55503/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812505525578453/295147905179352825856), (-7264752813273/590295810358705651712)), (76367/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456980799487299/18446744073709551616), (-9079231879339/73786976294838206464)), (5971/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1827654534546255/9223372036854775808), (-5105891459443/4611686018427387904)), (107585/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399723568956061/288230376151711744), (-2552209354643/288230376151711744)), (53859/576460752303423488), by norm_num⟩
  | 5 => ⟨((74929110738625/9007199254740992), (-8929413121621/144115188075855872)), (94403/144115188075855872), by norm_num⟩
  | 4 => ⟨((2925869575191/70368744177664), (-6693732816319/18014398509481984)), (141903/36028797018963968), by norm_num⟩
  | 3 => ⟨((748616515666567/4503599627370496), (-16722654181991/9007199254740992)), (11119/562949953421312), by norm_num⟩
  | 2 => ⟨((1121897825289653/2251799813685248), (-16705070980643/2251799813685248)), (44673/562949953421312), by norm_num⟩
  | 1 => ⟨((1119808883556297/1125899906842624), (-25013416608131/1125899906842624)), (270011/1125899906842624), by norm_num⟩
  | 0 => ⟨((1113367410731047/1125899906842624), (-24924343653295/562949953421312)), (547933/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1113367410731047/1125899906842624), (-24924343653295/562949953421312)), (2090198521140670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((274691846969103/281474976710656), (-98587633905253/1125899906842624)), (283047/281474976710656), by norm_num⟩
  | 2 => ⟨((531828026551703/562949953421312), (-192423636105927/1125899906842624)), (1204043/562949953421312), by norm_num⟩
  | 3 => ⟨((971966812431981/1125899906842624), (-363571511215775/1125899906842624)), (5373033/1125899906842624), by norm_num⟩
  | 4 => ⟨((721676266036887/1125899906842624), (-313863995102781/562949953421312)), (12746945/1125899906842624), by norm_num⟩
  | 5 => ⟨((112598111522137/1125899906842624), (-1609437532786691/2251799813685248)), (30554727/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1127798225061973/2251799813685248), (-321910723507963/2251799813685248)), (99576765/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21887591/33554432), (-64717791/4194304)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-27619065/33554432), (-1306636157/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((804184164046355/2251799813685248), (-143783705858997/562949953421312)), (49706697/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1063190433/2147483648), (380185205/1073741824)), (17/536870912), by norm_num⟩
  | 2 => ⟨((736947451/2147483648), (-263524303/1073741824)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-21283877/134217728), (121774085/1073741824)), (47/4294967296), by norm_num⟩
  | 4 => ⟨((944182997/17179869184), (-337629455/8589934592)), (17/4294967296), by norm_num⟩
  | 5 => ⟨((-261783113/17179869184), (748886095/68719476736)), (39/34359738368), by norm_num⟩
  | 6 => ⟨((241938969/68719476736), (-346058857/137438953472)), (37/137438953472), by norm_num⟩
  | 7 => ⟨((-766625437/1099511627776), (34267103/68719476736)), (61/1099511627776), by norm_num⟩
  | 8 => ⟨((132846065/1099511627776), (-760068667/8796093022208)), (87/8796093022208), by norm_num⟩
  | 9 => ⟨((-654804447/35184372088832), (468301737/35184372088832)), (7/4398046511104), by norm_num⟩
  | 10 => ⟨((363100685/140737488355328), (-259681623/140737488355328)), (1/4398046511104), by norm_num⟩
  | 11 => ⟨((-732166447/2251799813685248), (261814669/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 12 => ⟨((338332739/9007199254740992), (-241968133/9007199254740992)), (63/18014398509481984), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582903571460791/10141204801825835211973625643008), (-202178378915/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890349938602157/316912650057057350374175801344), (-959047178703/633825300114114700748351602688)), (11537/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891914089441025/39614081257132168796771975168), (-539424044397/19807040628566084398385987584)), (51919/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891824620533879/2475880078570760549798248448), (-286544939761/618970019642690137449562112)), (55167/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110843157780999/9671406556917033397649408), (-1146071392435/154742504910672534362390528)), (13793/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551709155570783/9671406556917033397649408), (-537163401327/4835703278458516698824704)), (3233/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260674580508637/604462909807314587353088), (-939920837807/604462909807314587353088)), (22633/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236356992418565/9444732965739290427392), (-190894443731/9444732965739290427392)), (18391/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299836771785513/4722366482869645213696), (-286294463843/1180591620717411303424)), (55181/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812302974268447/295147905179352825856), (-787156396235/295147905179352825856)), (18971/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1827420441910767/73786976294838206464), (-491857736213/18446744073709551616)), (94871/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913546956147381/4611686018427387904), (-1106363699991/4611686018427387904)), (106753/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49948121031531/36028797018963968), (-276492138573/144115188075855872)), (53391/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198387661501325/144115188075855872), (-241819525157/18014398509481984)), (46733/72057594037927936), by norm_num⟩
  | 4 => ⟨((46791938421981/1125899906842624), (-2900057536851/36028797018963968)), (17533/4503599627370496), by norm_num⟩
  | 3 => ⟨((748189232655723/4503599627370496), (-452745539975/1125899906842624)), (175443/9007199254740992), by norm_num⟩
  | 2 => ⟨((1121079843757875/2251799813685248), (-1808653195831/1125899906842624)), (351227/4503599627370496), by norm_num⟩
  | 1 => ⟨((139834148165769/140737488355328), (-676790864917/140737488355328)), (527691/2251799813685248), by norm_num⟩
  | 0 => ⟨((2222919967861443/2251799813685248), (-5391098015703/562949953421312)), (529397/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2222919967861443/2251799813685248), (-5391098015703/562949953421312)), (2019489292625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((137137750058971/140737488355328), (-5321955954953/281474976710656)), (1055355/1125899906842624), by norm_num⟩
  | 2 => ⟨((2137276361218049/2251799813685248), (-82973322784619/2251799813685248)), (4193263/2251799813685248), by norm_num⟩
  | 3 => ⟨((506380012580137/562949953421312), (-157506826602899/2251799813685248)), (8269023/2251799813685248), by norm_num⟩
  | 4 => ⟨((113185102230241/140737488355328), (-283358434801903/2251799813685248)), (8016477/1125899906842624), by norm_num⟩
  | 5 => ⟨((1420770187430415/2251799813685248), (-113942467588595/562949953421312)), (14911689/1125899906842624), by norm_num⟩
  | 6 => ⟨((804184164046355/2251799813685248), (-143783705858997/562949953421312)), (49706697/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-27619065/33554432), (-1306636157/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-64129483/67108864), (-758478801/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-708181028305399/2251799813685248), (498427790547585/2251799813685248)), (19278057/562949953421312), by norm_num⟩
  | 1 => ⟨((543486307/1073741824), (-95628331/268435456)), (121/2147483648), by norm_num⟩
  | 2 => ⟨((-218676867/536870912), (307815723/1073741824)), (99/2147483648), by norm_num⟩
  | 3 => ⟨((234631227/1073741824), (-165136765/1073741824)), (27/1073741824), by norm_num⟩
  | 4 => ⟨((-47203049/536870912), (531554741/8589934592)), (89/8589934592), by norm_num⟩
  | 5 => ⟨((972420821/34359738368), (-342201741/17179869184)), (117/34359738368), by norm_num⟩
  | 6 => ⟨((-1043367291/137438953472), (22948019/4294967296)), (127/137438953472), by norm_num⟩
  | 7 => ⟨((479781393/274877906944), (-84419227/68719476736)), (119/549755813888), by norm_num⟩
  | 8 => ⟨((-193044591/549755813888), (271735009/1099511627776)), (97/2199023255552), by norm_num⟩
  | 9 => ⟨((1104687231/17592186044416), (-388747223/8796093022208)), (141/17592186044416), by norm_num⟩
  | 10 => ⟨((-177792551/17592186044416), (500531615/70368744177664)), (93/70368744177664), by norm_num⟩
  | 11 => ⟨((832424937/562949953421312), (-292936203/281474976710656)), (111/562949953421312), by norm_num⟩
  | 12 => ⟨((-446578751/2251799813685248), (628616841/4503599627370496)), (121/4503599627370496), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582730986509759/10141204801825835211973625643008), (3293407986345/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780487591071225/633825300114114700748351602688), (3904775122327/633825300114114700748351602688)), (46293/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891674829889069/39614081257132168796771975168), (274529772553/2475880078570760549798248448)), (52091/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891569865040923/2475880078570760549798248448), (2333274275575/1237940039285380274899124224)), (55361/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886617579581681/77371252455336267181195264), (2333016810611/77371252455336267181195264)), (55377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775734551406881/4835703278458516698824704), (2186929650973/4835703278458516698824704)), (51933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9847374115703/4722366482869645213696), (239161222081/37778931862957161709568)), (22729/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890512348428289/75557863725914323419136), (3108582634423/37778931862957161709568)), (36951/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299578017113509/4722366482869645213696), (4661975509347/4722366482869645213696)), (55455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624248436837357/590295810358705651712), (3204377944035/295147905179352825856)), (76295/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826970967792475/73786976294838206464), (8008753385245/73786976294838206464)), (95437/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826584702742563/9223372036854775808), (140731764871/144115188075855872)), (26865/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399456557065197/288230376151711744), (9003062703797/1152921504606846976)), (53789/576460752303423488), by norm_num⟩
  | 5 => ⟨((299483309482327/36028797018963968), (3936717803413/72057594037927936)), (94263/144115188075855872), by norm_num⟩
  | 4 => ⟨((374162609564583/9007199254740992), (11801658084139/36028797018963968)), (70829/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495496582591071/9007199254740992), (14737190513089/9007199254740992)), (1387/70368744177664), by norm_num⟩
  | 2 => ⟨((1120171928832931/2251799813685248), (14714836949169/2251799813685248)), (22279/281474976710656), by norm_num⟩
  | 1 => ⟨((279311609128511/281474976710656), (11008132775031/562949953421312)), (269089/1125899906842624), by norm_num⟩
  | 0 => ⟨((554174102825069/562949953421312), (21903970015253/562949953421312)), (68145/140737488355328), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((554174102825069/562949953421312), (21903970015253/562949953421312)), (259952545702886537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((544682791917845/562949953421312), (86250032406881/1125899906842624)), (1115747/1125899906842624), by norm_num⟩
  | 2 => ⟨((523704771617999/562949953421312), (10431413167563/70368744177664)), (1165015/562949953421312), by norm_num⟩
  | 3 => ⟨((949649487766729/1125899906842624), (310534508717613/1125899906842624)), (1256499/281474976710656), by norm_num⟩
  | 4 => ⟨((178835272926197/281474976710656), (261922871958097/562949953421312)), (2812719/281474976710656), by norm_num⟩
  | 5 => ⟨((105381709608515/562949953421312), (1331302663977557/2251799813685248)), (49531713/2251799813685248), by norm_num⟩
  | 6 => ⟨((-708181028305399/2251799813685248), (498427790547585/2251799813685248)), (19278057/562949953421312), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64129483/67108864), (-758478801/33554432)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-71394247/67108864), (-844401367/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((776738364625535/2251799813685248), (-25159998003515/2251799813685248)), (24316709/2251799813685248), by norm_num⟩
  | 1 => ⟨((-663627777/1073741824), (2687017/134217728)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((594530677/1073741824), (-38515905/2147483648)), (5/268435456), by norm_num⟩
  | 3 => ⟨((-710170647/2147483648), (11501873/1073741824)), (49/4294967296), by norm_num⟩
  | 4 => ⟨((636227491/4294967296), (-10304295/2147483648)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((-1823946611/34359738368), (29540509/17179869184)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((1089357871/68719476736), (-8821581/17179869184)), (21/34359738368), by norm_num⟩
  | 7 => ⟨((-278838183/68719476736), (18064173/137438953472)), (11/68719476736), by norm_num⟩
  | 8 => ⟨((1998443819/2199023255552), (-32366653/1099511627776)), (81/2199023255552), by norm_num⟩
  | 9 => ⟨((-1591435839/8796093022208), (25774781/4398046511104)), (33/4398046511104), by norm_num⟩
  | 10 => ⟨((570294047/17592186044416), (-18472883/17592186044416)), (49/35184372088832), by norm_num⟩
  | 11 => ⟨((-1486297831/281474976710656), (24071973/140737488355328)), (33/140737488355328), by norm_num⟩
  | 12 => ⟨((887696071/1125899906842624), (-57508247/2251799813685248)), (81/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582589974344435/10141204801825835211973625643008), (-21089631219/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222541068436021/79228162514264337593543950336), (-50000232131/633825300114114700748351602688)), (46103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472874102051967/9903520314283042199192993792), (-56244920059/39614081257132168796771975168)), (25933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236422614144961/309485009821345068724781056), (-3734608735/154742504910672534362390528)), (13777/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886523452953407/77371252455336267181195264), (-29873221113/77371252455336267181195264)), (13777/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551293357459207/9671406556917033397649408), (-14001134305/2417851639229258349412352)), (51665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260310851456177/604462909807314587353088), (-48996219119/604462909807314587353088)), (45207/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890265056397943/75557863725914323419136), (-79604326059/75557863725914323419136)), (73461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649696882096765/2361183241434822606848), (-7461316725/590295810358705651712)), (6887/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405999266068733/147573952589676412928), (-41026917335/295147905179352825856)), (75757/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456664928301333/18446744073709551616), (-102536329269/73786976294838206464)), (94697/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456559652530827/2305843009213693952), (-115310810897/9223372036854775808)), (13317/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399371304378929/288230376151711744), (-115257635571/1152921504606846976)), (106537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598820282488653/72057594037927936), (-1574853781/2251799813685248)), (46611/72057594037927936), by norm_num⟩
  | 4 => ⟨((374055709395597/9007199254740992), (-151066467399/36028797018963968)), (139835/36028797018963968), by norm_num⟩
  | 3 => ⟨((186872751903197/1125899906842624), (-188624152939/9007199254740992)), (174801/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119687198003187/2251799813685248), (-94155563763/1125899906842624)), (87405/1125899906842624), by norm_num⟩
  | 1 => ⟨((2233187417345129/2251799813685248), (-140842713327/562949953421312)), (262239/1125899906842624), by norm_num⟩
  | 0 => ⟨((553669442808555/562949953421312), (-560253575823/1125899906842624)), (262289/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((553669442808555/562949953421312), (-560253575823/1125899906842624)), (1000553133250999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1089083573294113/1125899906842624), (-551017516339/562949953421312)), (2064765/2251799813685248), by norm_num⟩
  | 2 => ⟨((1053470035772595/1125899906842624), (-4263996271747/2251799813685248)), (3998539/2251799813685248), by norm_num⟩
  | 3 => ⟨((1971391176266943/2251799813685248), (-3989690626699/1125899906842624)), (7497765/2251799813685248), by norm_num⟩
  | 4 => ⟨((431468138921473/562949953421312), (-13971474461821/2251799813685248)), (823833/140737488355328), by norm_num⟩
  | 5 => ⟨((1322693455372777/2251799813685248), (-2677079040239/281474976710656)), (20369001/2251799813685248), by norm_num⟩
  | 6 => ⟨((776738364625535/2251799813685248), (-25159998003515/2251799813685248)), (24316709/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-71394247/67108864), (-844401367/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-38768259/33554432), (-458523931/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-415866047085169/2251799813685248), (-1148883319254543/4503599627370496)), (126299089/4503599627370496), by norm_num⟩
  | 1 => ⟨((192937365/536870912), (1066028457/2147483648)), (119/2147483648), by norm_num⟩
  | 2 => ⟨((-750877553/2147483648), (-1037197797/2147483648)), (59/1073741824), by norm_num⟩
  | 3 => ⟨((243523375/1073741824), (672764573/2147483648)), (39/1073741824), by norm_num⟩
  | 4 => ⟨((-473874607/4294967296), (-654569705/4294967296)), (77/4294967296), by norm_num⟩
  | 5 => ⟨((368846963/8589934592), (509493533/8589934592)), (61/8589934592), by norm_num⟩
  | 6 => ⟨((-239247683/17179869184), (-660952425/34359738368)), (81/34359738368), by norm_num⟩
  | 7 => ⟨((532062279/137438953472), (734945161/137438953472)), (23/34359738368), by norm_num⟩
  | 8 => ⟨((-258836347/274877906944), (-44691789/34359738368)), (91/549755813888), by norm_num⟩
  | 9 => ⟨((895417377/4398046511104), (1236852705/4398046511104)), (159/4398046511104), by norm_num⟩
  | 10 => ⟨((-696960705/17592186044416), (-962721693/17592186044416)), (63/8796093022208), by norm_num⟩
  | 11 => ⟨((493171967/70368744177664), (681225423/70368744177664)), (45/35184372088832), by norm_num⟩
  | 12 => ⟨((-639778891/562949953421312), (-883735643/562949953421312)), (59/281474976710656), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791235375123311/5070602400912917605986812821504), (-1431189059527/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780181086177477/633825300114114700748351602688), (-1696307373111/316912650057057350374175801344)), (46267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891330166932097/39614081257132168796771975168), (-3816285636069/39614081257132168796771975168)), (26031/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945601923862913/1237940039285380274899124224), (-2027161925639/1237940039285380274899124224)), (55327/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772869352310739/154742504910672534362390528), (-4053784201595/154742504910672534362390528)), (27671/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387781595619781/2417851639229258349412352), (-949962322855/2417851639229258349412352)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260164230076909/604462909807314587353088), (-3324294710137/604462909807314587353088)), (45425/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236253228168473/9444732965739290427392), (-5400903694549/75557863725914323419136)), (73843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649606745730589/2361183241434822606848), (-4049736915639/4722366482869645213696)), (55407/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623747809764807/590295810358705651712), (-1391714820341/147573952589676412928)), (1191/9223372036854775808), by norm_num⟩
  | 8 => ⟨((913173038645313/36893488147419103232), (-6956280482269/73786976294838206464)), (95339/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912941464463223/4611686018427387904), (-1955665392143/2305843009213693952)), (107337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798562994463885/576460752303423488), (-3909359366271/576460752303423488)), (107439/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197322254096171/144115188075855872), (-3418471348729/72057594037927936)), (94125/144115188075855872), by norm_num⟩
  | 4 => ⟨((747868705946573/18014398509481984), (-10246540413031/36028797018963968)), (17677/4503599627370496), by norm_num⟩
  | 3 => ⟨((1494361332030441/9007199254740992), (-12792643885627/9007199254740992)), (177173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119045718768115/2251799813685248), (-12769340972111/2251799813685248)), (177777/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115579694116665/1125899906842624), (-19095735387435/1125899906842624)), (268179/1125899906842624), by norm_num⟩
  | 0 => ⟨((1105104838847591/1125899906842624), (-37958256560517/1125899906842624)), (542425/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1105104838847591/1125899906842624), (-37958256560517/1125899906842624)), (2069187168601607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((67713383544901/70368744177664), (-37257177786683/562949953421312)), (1101389/1125899906842624), by norm_num⟩
  | 2 => ⟨((518800026252285/562949953421312), (-71702560526041/562949953421312)), (1132721/562949953421312), by norm_num⟩
  | 3 => ⟨((468979895013499/562949953421312), (-66079213715515/281474976710656)), (4752641/1125899906842624), by norm_num⟩
  | 4 => ⟨((719340292170861/1125899906842624), (-220195934097069/562949953421312)), (10150085/1125899906842624), by norm_num⟩
  | 5 => ⟨((287330566778487/1125899906842624), (-1125469904424543/2251799813685248)), (5227543/281474976710656), by norm_num⟩
  | 6 => ⟨((-415866047085169/2251799813685248), (-1148883319254543/4503599627370496)), (126299089/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-38768259/33554432), (-458523931/16777216)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-82857195/67108864), (-489988559/16777216)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-48873780175601/281474976710656), (262824724126329/1125899906842624)), (43846261/1125899906842624), by norm_num⟩
  | 1 => ⟨((387688327/1073741824), (-1042420673/2147483648)), (177/2147483648), by norm_num⟩
  | 2 => ⟨((-201543803/536870912), (541913213/1073741824)), (187/2147483648), by norm_num⟩
  | 3 => ⟨((558798075/2147483648), (-751251231/2147483648)), (33/536870912), by norm_num⟩
  | 4 => ⟨((-580993965/4294967296), (781091509/4294967296)), (139/4294967296), by norm_num⟩
  | 5 => ⟨((483257195/8589934592), (-649693653/8589934592)), (59/4294967296), by norm_num⟩
  | 6 => ⟨((-167484181/8589934592), (112583331/4294967296)), (83/17179869184), by norm_num⟩
  | 7 => ⟨((199013465/34359738368), (-1070219225/137438953472)), (25/17179869184), by norm_num⟩
  | 8 => ⟨((-827673733/549755813888), (556364579/274877906944)), (211/549755813888), by norm_num⟩
  | 9 => ⟨((764932953/2199023255552), (-1028380105/2199023255552)), (99/1099511627776), by norm_num⟩
  | 10 => ⟨((-19882917/274877906944), (213845631/2199023255552)), (167/8796093022208), by norm_num⟩
  | 11 => ⟨((481109685/35184372088832), (-646806529/35184372088832)), (1/274877906944), by norm_num⟩
  | 12 => ⟨((-666959643/281474976710656), (224166061/70368744177664)), (45/70368744177664), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582367473638495/10141204801825835211973625643008), (719801227187/2535301200456458802993406410752)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780058613826699/633825300114114700748351602688), (3412112736615/633825300114114700748351602688)), (34701/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118199524833933/2475880078570760549798248448), (1919096013873/19807040628566084398385987584)), (78093/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472764370051141/618970019642690137449562112), (31855966087/19342813113834066795298816)), (82993/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772722999055603/154742504910672534362390528), (2038491909483/77371252455336267181195264)), (41507/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550989191471801/9671406556917033397649408), (1910778121635/4835703278458516698824704)), (9731/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630022101563961/302231454903657293676544), (3343245618133/604462909807314587353088)), (68139/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944915405025219/37778931862957161709568), (5431618935605/75557863725914323419136)), (6923/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1299067254948777/4722366482869645213696), (2036351695501/2361183241434822606848)), (83113/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623546775173125/590295810358705651712), (5598324565467/590295810358705651712)), (28585/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826094845061017/73786976294838206464), (6995441759731/73786976294838206464)), (71507/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912800188352033/4611686018427387904), (7866483970339/9223372036854775808)), (161013/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199605442746345/144115188075855872), (1965562209477/288230376151711744)), (161167/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197075231734931/144115188075855872), (859337880885/18014398509481984)), (141195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495367116558499/36028797018963968), (643907800305/2251799813685248)), (106069/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493898881418995/9007199254740992), (3215369515669/2251799813685248)), (66445/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118583899369589/2251799813685248), (802278720063/140737488355328)), (66673/562949953421312), by norm_num⟩
  | 1 => ⟨((139361069353009/140737488355328), (599754299841/35184372088832)), (402323/1125899906842624), by norm_num⟩
  | 0 => ⟨((551864494865203/562949953421312), (38134039326291/1125899906842624)), (813803/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((551864494865203/562949953421312), (38134039326291/1125899906842624)), (3104412083152389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080703062875411/1125899906842624), (74766228230677/1125899906842624)), (1650683/1125899906842624), by norm_num⟩
  | 2 => ⟨((516177821030285/562949953421312), (143529795779313/1125899906842624)), (1694035/562949953421312), by norm_num⟩
  | 3 => ⟨((464143110353739/562949953421312), (263209533238351/1125899906842624)), (7076975/1125899906842624), by norm_num⟩
  | 4 => ⟨((703824597863287/1125899906842624), (434023986287017/1125899906842624)), (3744643/281474976710656), by norm_num⟩
  | 5 => ⟨((136331943016963/562949953421312), (271317863830483/562949953421312)), (60550133/2251799813685248), by norm_num⟩
  | 6 => ⟨((-48873780175601/281474976710656), (262824724126329/1125899906842624)), (43846261/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-82857195/67108864), (-489988559/16777216)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile040Terms0
