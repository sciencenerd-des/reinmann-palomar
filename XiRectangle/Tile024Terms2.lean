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
namespace Reinmann.XiRectangle.Tile024Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6909/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6909/640))
  have he : value ((3/4), (6909/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-279097919/134217728), (-4017265675/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((96519045528713/9007199254740992), (560877588801975/4503599627370496)), (22040889/4503599627370496), by norm_num⟩
  | 1 => ⟨((-510421023/17179869184), (-185380325/536870912)), (235/17179869184), by norm_num⟩
  | 2 => ⟨((353796893/8589934592), (1027966797/2147483648)), (165/8589934592), by norm_num⟩
  | 3 => ⟨((-653955517/17179869184), (-1900086099/4294967296)), (307/17179869184), by norm_num⟩
  | 4 => ⟨((453287423/17179869184), (2634078645/8589934592)), (215/17179869184), by norm_num⟩
  | 5 => ⟨((-502711839/34359738368), (-1460643349/8589934592)), (15/2147483648), by norm_num⟩
  | 6 => ⟨((58075549/8589934592), (5399684369/68719476736)), (7/2147483648), by norm_num⟩
  | 7 => ⟨((-92011207/34359738368), (-2138729141/68719476736)), (179/137438953472), by norm_num⟩
  | 8 => ⟨((255109235/274877906944), (5929816297/549755813888)), (125/274877906944), by norm_num⟩
  | 9 => ⟨((-19647583/68719476736), (-913385655/274877906944)), (155/1099511627776), by norm_num⟩
  | 10 => ⟨((348637869/4398046511104), (2025954213/2199023255552)), (173/4398046511104), by norm_num⟩
  | 11 => ⟨((-351501609/17592186044416), (-2042595565/8796093022208)), (177/17592186044416), by norm_num⟩
  | 12 => ⟨((649712931/140737488355328), (7551036571/140737488355328)), (165/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98829191395547/633825300114114700748351602688), (967166253935/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889379423278553/316912650057057350374175801344), (2289163737141/633825300114114700748351602688)), (23107/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889730580638907/39614081257132168796771975168), (160927378711/2475880078570760549798248448)), (25999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236188101943885/309485009821345068724781056), (1367592409011/1237940039285380274899124224)), (6907/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442792728588073/38685626227668133590597632), (683632951349/38685626227668133590597632)), (27633/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774767364063479/4835703278458516698824704), (640732481291/2417851639229258349412352)), (25911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629386081808373/302231454903657293676544), (2241870248545/604462909807314587353088)), (22677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887764900369871/75557863725914323419136), (1820869699983/37778931862957161709568)), (36859/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297518832581157/4722366482869645213696), (2730167703703/4722366482869645213696)), (27653/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405354833724897/147573952589676412928), (3752134039151/590295810358705651712)), (9509/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823438004402443/73786976294838206464), (1171849789079/18446744073709551616)), (11891/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822614811337935/9223372036854775808), (5269519846005/9223372036854775808)), (53537/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796931099768687/576460752303423488), (2632384045361/576460752303423488)), (13393/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194471304416907/144115188075855872), (4601331165447/144115188075855872)), (23457/72057594037927936), by norm_num⟩
  | 4 => ⟨((745735355739427/18014398509481984), (1722831734689/9007199254740992)), (35225/18014398509481984), by norm_num⟩
  | 3 => ⟨((744522477873017/4503599627370496), (4297756762643/4503599627370496)), (44099/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113754805392501/2251799813685248), (4283799890835/1125899906842624)), (88403/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107706855341633/1125899906842624), (6390901988809/562949953421312)), (66559/562949953421312), by norm_num⟩
  | 0 => ⟨((2179225058102735/2251799813685248), (25286355072845/1125899906842624)), (536597/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2179225058102735/2251799813685248), (25286355072845/1125899906842624)), (2046955117232512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2107853560518519/2251799813685248), (24471384297987/562949953421312)), (1062709/2251799813685248), by norm_num⟩
  | 2 => ⟨((984426996408603/1125899906842624), (183256412794211/2251799813685248)), (2081943/2251799813685248), by norm_num⟩
  | 3 => ⟨((1706547406588955/2251799813685248), (320459321336167/2251799813685248)), (994887/562949953421312), by norm_num⟩
  | 4 => ⟨((1247717429066709/2251799813685248), (242863073537821/1125899906842624)), (7164555/2251799813685248), by norm_num⟩
  | 5 => ⟨((293291811469285/1125899906842624), (1076559249674777/4503599627370496)), (22061201/4503599627370496), by norm_num⟩
  | 6 => ⟨((96519045528713/9007199254740992), (560877588801975/4503599627370496)), (22040889/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/134217728), (-4017265675/134217728)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-142600297/67108864), (-4105106043/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((362833920062927/4503599627370496), (794271126077541/9007199254740992)), (7858407/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3921455017/17179869184), (-2146091035/8589934592)), (43/4294967296), by norm_num⟩
  | 2 => ⟨((2777579671/8589934592), (3040166879/8589934592)), (31/2147483648), by norm_num⟩
  | 3 => ⟨((-655789649/2147483648), (-2871147123/8589934592)), (119/8589934592), by norm_num⟩
  | 4 => ⟨((3715983969/17179869184), (4067286171/17179869184)), (85/8589934592), by norm_num⟩
  | 5 => ⟨((-1052817537/8589934592), (-2304697891/17179869184)), (49/8589934592), by norm_num⟩
  | 6 => ⟨((994285565/17179869184), (4353133879/68719476736)), (47/17179869184), by norm_num⟩
  | 7 => ⟨((-3219455007/137438953472), (-880954071/34359738368)), (155/137438953472), by norm_num⟩
  | 8 => ⟨((1140175361/137438953472), (1247965415/137438953472)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((-2871431153/1099511627776), (-392861363/137438953472)), (143/1099511627776), by norm_num⟩
  | 10 => ⟨((406768853/549755813888), (3561792179/4398046511104)), (41/1099511627776), by norm_num⟩
  | 11 => ⟨((-3352619469/17592186044416), (-1834784933/8796093022208)), (171/17592186044416), by norm_num⟩
  | 12 => ⟨((3166228739/70368744177664), (433194763/8796093022208)), (163/70368744177664), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834567463/10141204801825835211973625643008), (540911509301/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778690684462381/633825300114114700748351602688), (1280175036615/633825300114114700748351602688)), (23083/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944827010793057/19807040628566084398385987584), (1439929567433/39614081257132168796771975168)), (12985/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472355907793345/618970019642690137449562112), (382398390849/618970019642690137449562112)), (27595/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771089909404929/154742504910672534362390528), (382305161387/38685626227668133590597632)), (13799/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193682372064979/1208925819614629174706176), (1433248252215/9671406556917033397649408)), (6469/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258706071363575/604462909807314587353088), (626848127613/302231454903657293676544)), (5661/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887657857192449/75557863725914323419136), (1018257135813/37778931862957161709568)), (36801/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648719431034363/2361183241434822606848), (763368310245/2361183241434822606848)), (13803/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25332966901967/9223372036854775808), (2098208640153/590295810358705651712)), (37965/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911650973233409/36893488147419103232), (1310590218883/36893488147419103232)), (47467/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455615696924131/2305843009213693952), (2946656548435/9223372036854775808)), (6677/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796855737825773/576460752303423488), (1471972286513/576460752303423488)), (13359/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194340880269287/144115188075855872), (321612966183/18014398509481984)), (23389/72057594037927936), by norm_num⟩
  | 4 => ⟨((745638993171209/18014398509481984), (3853268042713/36028797018963968)), (70211/36028797018963968), by norm_num⟩
  | 3 => ⟨((744404563530327/4503599627370496), (2402974898743/4503599627370496)), (2745/281474976710656), by norm_num⟩
  | 2 => ⟨((2227053120121941/4503599627370496), (9580065545793/4503599627370496)), (175909/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214766659418677/2251799813685248), (14290763679429/2251799813685248)), (264441/2251799813685248), by norm_num⟩
  | 0 => ⟨((2178080307869901/2251799813685248), (28265687462397/2251799813685248)), (531205/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2178080307869901/2251799813685248), (28265687462397/2251799813685248)), (2026386269576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2106419429300975/2251799813685248), (27340324337933/1125899906842624)), (520483/1125899906842624), by norm_num⟩
  | 2 => ⟨((1969097258046407/2251799813685248), (102300728579529/2251799813685248)), (1998075/2251799813685248), by norm_num⟩
  | 3 => ⟨((1717239049882291/2251799813685248), (178914735597591/2251799813685248)), (3676001/2251799813685248), by norm_num⟩
  | 4 => ⟨((647681790827787/1125899906842624), (136441689310173/1125899906842624)), (3095419/1125899906842624), by norm_num⟩
  | 5 => ⟨((1424195401924335/4503599627370496), (627912283419941/4503599627370496)), (4311557/1125899906842624), by norm_num⟩
  | 6 => ⟨((362833920062927/4503599627370496), (794271126077541/9007199254740992)), (7858407/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142600297/67108864), (-4105106043/134217728)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-72738587/33554432), (-261745259/8388608)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1007314204814989/9007199254740992), (218347935481439/9007199254740992)), (1212011/1125899906842624), by norm_num⟩
  | 1 => ⟨((-2776634721/8589934592), (-1203740513/17179869184)), (55/17179869184), by norm_num⟩
  | 2 => ⟨((2006376645/4294967296), (217453599/2147483648)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((-966529065/2147483648), (-209507247/2147483648)), (21/4294967296), by norm_num⟩
  | 4 => ⟨((2793628313/8589934592), (302776915/4294967296)), (63/17179869184), by norm_num⟩
  | 5 => ⟨((-6459699503/34359738368), (-1400220551/34359738368)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((388977771/4294967296), (1349052645/68719476736)), (37/34359738368), by norm_num⟩
  | 7 => ⟨((-1284903273/34359738368), (-1114075333/137438953472)), (63/137438953472), by norm_num⟩
  | 8 => ⟨((928462033/68719476736), (402511485/137438953472)), (47/274877906944), by norm_num⟩
  | 9 => ⟨((-596355653/137438953472), (-258535073/274877906944)), (31/549755813888), by norm_num⟩
  | 10 => ⟨((5515806519/4398046511104), (597809979/2199023255552)), (37/2199023255552), by norm_num⟩
  | 11 => ⟨((-5797356867/17592186044416), (-1256649513/17592186044416)), (5/1099511627776), by norm_num⟩
  | 12 => ⟨((349094095/4398046511104), (1210728087/70368744177664)), (79/70368744177664), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996579415/5070602400912917605986812821504), (278055700759/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778625426318291/633825300114114700748351602688), (329013872661/633825300114114700748351602688)), (5765/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118098791636847/2475880078570760549798248448), (370070753539/39614081257132168796771975168)), (12971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889345768549955/2475880078570760549798248448), (393113255317/2475880078570760549798248448)), (13783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771012133885805/154742504910672534362390528), (196507754447/77371252455336267181195264)), (6891/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774693077232737/4835703278458516698824704), (368348218317/9671406556917033397649408)), (6461/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258642444500611/604462909807314587353088), (161100454179/302231454903657293676544)), (11307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943777318363555/37778931862957161709568), (261690982785/37778931862957161709568)), (9187/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297361598130519/4722366482869645213696), (49045794929/590295810358705651712)), (13781/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621203889613947/590295810358705651712), (539227461331/590295810358705651712)), (9475/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823169824612861/73786976294838206464), (673620170917/73786976294838206464)), (23689/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455578664081095/2305843009213693952), (378626832127/4611686018427387904)), (6663/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199195496925387/144115188075855872), (756543032845/1152921504606846976)), (13327/576460752303423488), by norm_num⟩
  | 5 => ⟨((74638282885495/9007199254740992), (82647073903/18014398509481984)), (23325/144115188075855872), by norm_num⟩
  | 4 => ⟨((745543434466505/18014398509481984), (247542500903/9007199254740992)), (34993/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488572696513569/9007199254740992), (1234926495407/9007199254740992)), (5469/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113293813206491/2251799813685248), (2461515072033/4503599627370496)), (87533/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214086728275995/2251799813685248), (229468626383/140737488355328)), (131377/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088396515957175/1125899906842624), (3630158809485/1125899906842624)), (131535/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1088396515957175/1125899906842624), (3630158809485/1125899906842624)), (501766209128951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104261294801431/2251799813685248), (14036957198779/2251799813685248)), (63789/281474976710656), by norm_num⟩
  | 2 => ⟨((1966302037029519/2251799813685248), (26234504107037/2251799813685248)), (240029/562949953421312), by norm_num⟩
  | 3 => ⟨((1716695875062821/2251799813685248), (11454161811503/562949953421312)), (1699145/2251799813685248), by norm_num⟩
  | 4 => ⟨((1307818547810075/2251799813685248), (69858118699917/2251799813685248)), (1329943/1125899906842624), by norm_num⟩
  | 5 => ⟨((757398231797773/2251799813685248), (162291057660847/4503599627370496)), (3254697/2251799813685248), by norm_num⟩
  | 6 => ⟨((1007314204814989/9007199254740992), (218347935481439/9007199254740992)), (1212011/1125899906842624), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72738587/33554432), (-261745259/8388608)), (1/134217728), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-74099233/33554432), (-4266263347/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((230673240429943/2251799813685248), (-358104068047849/9007199254740992)), (21210385/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2590954897/8589934592), (502784527/4294967296)), (121/17179869184), by norm_num⟩
  | 2 => ⟨((476806787/1073741824), (-1480418359/8589934592)), (91/8589934592), by norm_num⟩
  | 3 => ⟨((-467976163/1073741824), (1453000507/8589934592)), (91/8589934592), by norm_num⟩
  | 4 => ⟨((2755854511/8589934592), (-2139135665/17179869184)), (17/2147483648), by norm_num⟩
  | 5 => ⟨((-3245778177/17179869184), (1259710887/17179869184)), (41/8589934592), by norm_num⟩
  | 6 => ⟨((3185665261/34359738368), (-1236380613/34359738368)), (41/17179869184), by norm_num⟩
  | 7 => ⟨((-1339999567/34359738368), (2080255583/137438953472)), (35/34359738368), by norm_num⟩
  | 8 => ⟨((3945546957/274877906944), (-765648203/137438953472)), (105/274877906944), by norm_num⟩
  | 9 => ⟨((-5163298779/1099511627776), (1001957517/549755813888)), (35/274877906944), by norm_num⟩
  | 10 => ⟨((3040603637/2199023255552), (-2360162215/4398046511104)), (167/4398046511104), by norm_num⟩
  | 11 => ⟨((-1627794885/4398046511104), (157939855/1099511627776)), (91/8796093022208), by norm_num⟩
  | 12 => ⟨((798823785/8796093022208), (-1240118041/35184372088832)), (91/35184372088832), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171721355/10141204801825835211973625643008), (-482242957589/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444640702552681/158456325028528675187087900672), (-570583529287/633825300114114700748351602688)), (23065/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889510229939209/39614081257132168796771975168), (-320891568467/19807040628566084398385987584)), (25949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472317734538265/618970019642690137449562112), (-681741023639/2475880078570760549798248448)), (6893/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885468656312165/77371252455336267181195264), (-681568339117/154742504910672534362390528)), (27573/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193664502404941/1208925819614629174706176), (-319393450987/4835703278458516698824704)), (25851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314645271471235/151115727451828646838272), (-558755192325/604462909807314587353088)), (22621/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471863736794515/18889465931478580854784), (-907633558745/75557863725914323419136)), (36761/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81080427930981/295147905179352825856), (-340212320229/2361183241434822606848)), (27573/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810550566274365/295147905179352825856), (-935095796345/590295810358705651712)), (9479/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911520708553839/36893488147419103232), (-1168138099407/73786976294838206464)), (47399/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911085125635517/4611686018427387904), (-1313150128621/9223372036854775808)), (53331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593419637092815/1152921504606846976), (-163986844525/144115188075855872)), (13335/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194086305239949/144115188075855872), (-143312152945/18014398509481984)), (23341/72057594037927936), by norm_num⟩
  | 4 => ⟨((745448843873361/18014398509481984), (-429232117205/9007199254740992)), (70043/36028797018963968), by norm_num⟩
  | 3 => ⟨((186042060366457/1125899906842624), (-535309800729/2251799813685248)), (21897/2251799813685248), by norm_num⟩
  | 2 => ⟨((556528997027941/1125899906842624), (-2133875111027/2251799813685248)), (10955/281474976710656), by norm_num⟩
  | 1 => ⟨((1106690621760217/1125899906842624), (-6364930449185/2251799813685248)), (263183/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175389956271937/2251799813685248), (-12583832390813/2251799813685248)), (527429/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2175389956271937/2251799813685248), (-12583832390813/2251799813685248)), (2011981972701262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2101502575962391/2251799813685248), (-12156827808589/1125899906842624)), (16015/35184372088832), by norm_num⟩
  | 2 => ⟨((490243614917573/562949953421312), (-45381662792609/2251799813685248)), (15119/17592186044416), by norm_num⟩
  | 3 => ⟨((213349412368023/281474976710656), (-39520512051217/1125899906842624)), (3448589/2251799813685248), by norm_num⟩
  | 4 => ⟨((645462063576919/1125899906842624), (-14977668923085/281474976710656)), (5469951/2251799813685248), by norm_num⟩
  | 5 => ⟨((733692194030521/2251799813685248), (-274767361664383/4503599627370496)), (13707629/4503599627370496), by norm_num⟩
  | 6 => ⟨((230673240429943/2251799813685248), (-358104068047849/9007199254740992)), (21210385/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-74099233/33554432), (-4266263347/134217728)), (1/67108864), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-301560285/134217728), (-2170291673/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35874422220695/562949953421312), (-759994433822931/9007199254740992)), (14683551/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3279729139/17179869184), (2171268323/8589934592)), (85/8589934592), by norm_num⟩
  | 2 => ⟨((2456297607/8589934592), (-3252269295/8589934592)), (129/8589934592), by norm_num⟩
  | 3 => ⟨((-1226401669/4294967296), (405955337/1073741824)), (131/8589934592), by norm_num⟩
  | 4 => ⟨((918492765/4294967296), (-4864534019/17179869184)), (199/17179869184), by norm_num⟩
  | 5 => ⟨((-2201246735/17179869184), (2914568311/17179869184)), (121/17179869184), by norm_num⟩
  | 6 => ⟨((2198115295/34359738368), (-2910422117/34359738368)), (123/34359738368), by norm_num⟩
  | 7 => ⟨((-1881418551/68719476736), (155693669/4294967296)), (107/68719476736), by norm_num⟩
  | 8 => ⟨((2818113137/274877906944), (-466416549/34359738368)), (81/137438953472), by norm_num⟩
  | 9 => ⟨((-1876069439/549755813888), (2484016193/549755813888)), (109/549755813888), by norm_num⟩
  | 10 => ⟨((1124040353/1099511627776), (-2976578991/2199023255552)), (33/549755813888), by norm_num⟩
  | 11 => ⟨((-1224481441/4398046511104), (1621278863/4398046511104)), (73/4398046511104), by norm_num⟩
  | 12 => ⟨((2445479047/35184372088832), (-3237944943/35184372088832)), (37/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060280235/10141204801825835211973625643008), (-1203534384669/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778502609312125/633825300114114700748351602688), (-1423915636281/633825300114114700748351602688)), (11543/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889442465889287/39614081257132168796771975168), (-1601591402999/39614081257132168796771975168)), (12987/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236149861001837/309485009821345068724781056), (-1701300891465/2475880078570760549798248448)), (1725/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770865205359889/154742504910672534362390528), (-425215584579/38685626227668133590597632)), (27603/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193656044753911/1208925819614629174706176), (-398523157639/2417851639229258349412352)), (25881/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629260910867329/302231454903657293676544), (-1394365410143/604462909807314587353088)), (22649/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887358529438113/75557863725914323419136), (-1132485537323/37778931862957161709568)), (36809/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297214434398143/4722366482869645213696), (-848982519869/2361183241434822606848)), (27613/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621001404394277/590295810358705651712), (-2333462298491/590295810358705651712)), (37975/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822916515839627/73786976294838206464), (-2914969609569/73786976294838206464)), (47481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911014703241971/4611686018427387904), (-409598452469/1152921504606846976)), (26717/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593278379655149/1152921504606846976), (-409199876343/144115188075855872)), (53455/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193962242020039/144115188075855872), (-715203976307/36028797018963968)), (23399/72057594037927936), by norm_num⟩
  | 4 => ⟨((372677667540415/9007199254740992), (-4284067278285/36028797018963968)), (70245/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488101103241417/9007199254740992), (-5342582280387/9007199254740992)), (87891/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225640433970923/4503599627370496), (-1330968467871/562949953421312)), (88019/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212656024311907/2251799813685248), (-15878389106215/2251799813685248)), (66175/562949953421312), by norm_num⟩
  | 0 => ⟨((1086946278133851/1125899906842624), (-15692849964683/1125899906842624)), (265993/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1086946278133851/1125899906842624), (-15692849964683/1125899906842624)), (1014682774070357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131140203808335/140737488355328), (-30299824626967/1125899906842624)), (130249/281474976710656), by norm_num⟩
  | 2 => ⟨((1953527324155573/2251799813685248), (-112934377993305/2251799813685248)), (499489/562949953421312), by norm_num⟩
  | 3 => ⟨((1689099896613343/2251799813685248), (-195950272227239/2251799813685248)), (3667023/2251799813685248), by norm_num⟩
  | 4 => ⟨((624980501030165/1125899906842624), (-293968924367847/2251799813685248)), (3069777/1125899906842624), by norm_num⟩
  | 5 => ⟨((163867228472911/562949953421312), (-40795110764761/281474976710656)), (16838161/4503599627370496), by norm_num⟩
  | 6 => ⟨((35874422220695/562949953421312), (-759994433822931/9007199254740992)), (14683551/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-301560285/134217728), (-2170291673/67108864)), (1/67108864), by norm_num⟩, -5, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-306471663/134217728), (-551409563/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((110055030012659/9007199254740992), (-1823110075014855/18014398509481984)), (35654279/9007199254740992), by norm_num⟩
  | 1 => ⟨((-639085785/17179869184), (5293368845/17179869184)), (209/17179869184), by norm_num⟩
  | 2 => ⟨((486427753/8589934592), (-4028945055/8589934592)), (5/268435456), by norm_num⟩
  | 3 => ⟨((-30852921/536870912), (4088737873/8589934592)), (41/2147483648), by norm_num⟩
  | 4 => ⟨((375729641/8589934592), (-3112063549/8589934592)), (251/17179869184), by norm_num⟩
  | 5 => ⟨((-457566929/17179869184), (3789898921/17179869184)), (77/8589934592), by norm_num⟩
  | 6 => ⟨((232178797/17179869184), (-3846144101/34359738368)), (79/17179869184), by norm_num⟩
  | 7 => ⟨((-403927747/68719476736), (6691241151/137438953472)), (277/137438953472), by norm_num⟩
  | 8 => ⟨((76860443/34359738368), (-5092908455/274877906944)), (213/274877906944), by norm_num⟩
  | 9 => ⟨((-832011887/1099511627776), (3445660903/549755813888)), (291/1099511627776), by norm_num⟩
  | 10 => ⟨((126653943/549755813888), (-4196156773/2199023255552)), (179/2199023255552), by norm_num⟩
  | 11 => ⟨((-560873849/8796093022208), (2322780627/4398046511104)), (25/1099511627776), by norm_num⟩
  | 12 => ⟨((569197673/35184372088832), (-2357252579/17592186044416)), (205/35184372088832), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288773/1267650600228229401496703205376), (-1889626547003/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778444625848081/633825300114114700748351602688), (-139719016451/39614081257132168796771975168)), (11553/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889377158294355/39614081257132168796771975168), (-1257219993815/19807040628566084398385987584)), (25997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944564698739751/1237940039285380274899124224), (-2670970025491/2475880078570760549798248448)), (13813/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885397800537605/77371252455336267181195264), (-83445937311/4835703278458516698824704)), (27631/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774591491623909/4835703278458516698824704), (-2502634560931/9671406556917033397649408)), (25909/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314616124534093/151115727451828646838272), (-2189061935641/604462909807314587353088)), (5669/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887265152568743/75557863725914323419136), (-3555832486147/75557863725914323419136)), (4607/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297144204197071/4722366482869645213696), (-2665655887987/4722366482869645213696)), (13825/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620904517263399/590295810358705651712), (-57239028583/9223372036854775808)), (2377/36893488147419103232), by norm_num⟩
  | 8 => ⟨((14240585365165/576460752303423488), (-4576155524531/73786976294838206464)), (5945/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455472989916335/2305843009213693952), (-2572049265177/4611686018427387904)), (53531/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398285027684503/288230376151711744), (-2569503639471/576460752303423488)), (53565/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193840334266077/144115188075855872), (-140340925261/4503599627370496)), (11727/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490525969640253/36028797018963968), (-840616952581/4503599627370496)), (70437/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487867023029253/9007199254740992), (-8386202245195/9007199254740992)), (22045/2251799813685248), by norm_num⟩
  | 2 => ⟨((2225162713706481/4503599627370496), (-2089079360953/562949953421312)), (22095/562949953421312), by norm_num⟩
  | 1 => ⟨((2211915732082905/2251799813685248), (-24919990344643/2251799813685248)), (133073/1125899906842624), by norm_num⟩
  | 0 => ⟨((2172318245695317/2251799813685248), (-49246898335829/2251799813685248)), (536333/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172318245695317/2251799813685248), (-49246898335829/2251799813685248)), (2045948037154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094565100734283/2251799813685248), (-23754317579355/562949953421312)), (132283/281474976710656), by norm_num⟩
  | 2 => ⟨((121518758376833/140737488355328), (-44191285824869/562949953421312)), (2058049/2251799813685248), by norm_num⟩
  | 3 => ⟨((832457901567447/1125899906842624), (-19078321800641/140737488355328)), (484641/281474976710656), by norm_num⟩
  | 4 => ⟨((1189610697358449/2251799813685248), (-451390739374065/2251799813685248)), (3392219/1125899906842624), by norm_num⟩
  | 5 => ⟨((134494638945547/562949953421312), (-476933383673319/2251799813685248)), (9888333/2251799813685248), by norm_num⟩
  | 6 => ⟨((110055030012659/9007199254740992), (-1823110075014855/18014398509481984)), (35654279/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-306471663/134217728), (-551409563/16777216)), (1/67108864), by norm_num⟩, -5, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile024Terms2
