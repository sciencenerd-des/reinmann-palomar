/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile009Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2679/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2679/640))
  have he : value ((3/4), (2679/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-55294967/33554432), (-19751362213/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-13194035551297/70368744177664), (-390682132357297/9007199254740992)), (577745/4503599627370496), by norm_num⟩
  | 1 => ⟨((7077699997/17179869184), (6549197259/68719476736)), (41/137438953472), by norm_num⟩
  | 2 => ⟨((-31102592769/68719476736), (-14390057179/137438953472)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((91119175001/274877906944), (21078791535/274877906944)), (71/274877906944), by norm_num⟩
  | 4 => ⟨((-100104645389/549755813888), (-23157419411/549755813888)), (81/549755813888), by norm_num⟩
  | 5 => ⟨((43990477431/549755813888), (20352820431/1099511627776)), (73/1099511627776), by norm_num⟩
  | 6 => ⟨((-8054746515/274877906944), (-14906572423/2199023255552)), (55/2199023255552), by norm_num⟩
  | 7 => ⟨((80905540603/8796093022208), (18716049881/8796093022208)), (71/8796093022208), by norm_num⟩
  | 8 => ⟨((-11110477641/4398046511104), (-20561682395/35184372088832)), (81/35184372088832), by norm_num⟩
  | 9 => ⟨((86798985027/140737488355328), (20079392849/140737488355328)), (41/70368744177664), by norm_num⟩
  | 10 => ⟨((-19071686319/140737488355328), (-8823787093/281474976710656)), (37/281474976710656), by norm_num⟩
  | 11 => ⟨((60952404235/2251799813685248), (7050124315/1125899906842624)), (61/2251799813685248), by norm_num⟩
  | 12 => ⟨((-44642040211/9007199254740992), (-2581784403/2251799813685248)), (23/4503599627370496), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-3796148308485/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889708152001157/316912650057057350374175801344), (-4495707868725/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472617408288721/9903520314283042199192993792), (-5056906459211/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((29535770600039/38685626227668133590597632), (-5372056267905/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771954584547159/154742504910672534362390528), (-5371035930845/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550268534614081/9671406556917033397649408), (-1258565517229/2417851639229258349412352)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314853340099031/151115727451828646838272), (-4403895184705/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888805188730043/75557863725914323419136), (-3577148460127/37778931862957161709568)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298297600395915/4722366482869645213696), (-5363944010785/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405621947148107/147573952589676412928), (-1843133156627/147573952589676412928)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824770046392453/73786976294838206464), (-9211330142865/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456027129081355/2305843009213693952), (-2589196203897/2305843009213693952)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595349858904539/1152921504606846976), (-5174666347133/576460752303423488)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149470776866109/18014398509481984), (-1130910288447/18014398509481984)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((373349879772721/9007199254740992), (-13554155488227/36028797018963968)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491432294067713/9007199254740992), (-8456674832021/4503599627370496)), (1391/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116106748022579/2251799813685248), (-16869331374549/2251799813685248)), (1397/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111146668627543/1125899906842624), (-25193948063827/1125899906842624)), (2111/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096142082184877/1125899906842624), (-49947689135085/1125899906842624)), (4285/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096142082184877/1125899906842624), (-49947689135085/1125899906842624)), (16345982078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((532477481079613/562949953421312), (-97255117681625/1125899906842624)), (2181/281474976710656), by norm_num⟩
  | 2 => ⟨((249727019843669/281474976710656), (-183981399307289/1125899906842624)), (4503/281474976710656), by norm_num⟩
  | 3 => ⟨((856175748741471/1125899906842624), (-163229879588575/562949953421312)), (4731/140737488355328), by norm_num⟩
  | 4 => ⟨((1112818172492453/2251799813685248), (-496504044540303/1125899906842624)), (79511/1125899906842624), by norm_num⟩
  | 5 => ⟨((112043361277759/2251799813685248), (-1962940826702391/4503599627370496)), (594855/4503599627370496), by norm_num⟩
  | 6 => ⟨((-13194035551297/70368744177664), (-390682132357297/9007199254740992)), (577745/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-19751362213/2147483648)), (1/4294967296), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-7417145753/4294967296), (-20698472367/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-391324301907481/2251799813685248), (21230605409165/562949953421312)), (1066013/9007199254740992), by norm_num⟩
  | 1 => ⟨((109992371105/274877906944), (-11934881721/137438953472)), (39/137438953472), by norm_num⟩
  | 2 => ⟨((-3957293657/8589934592), (13740540369/137438953472)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((97194724087/274877906944), (-21092508949/274877906944)), (37/137438953472), by norm_num⟩
  | 4 => ⟨((-13987445175/68719476736), (6070912085/137438953472)), (11/68719476736), by norm_num⟩
  | 5 => ⟨((25765826199/274877906944), (-5591516667/274877906944)), (21/274877906944), by norm_num⟩
  | 6 => ⟨((-9888001219/274877906944), (8583295283/1099511627776)), (67/2199023255552), by norm_num⟩
  | 7 => ⟨((52041061043/4398046511104), (-22587163163/8796093022208)), (91/8796093022208), by norm_num⟩
  | 8 => ⟨((-29957242845/8796093022208), (6501108149/8796093022208)), (27/8796093022208), by norm_num⟩
  | 9 => ⟨((15328689067/17592186044416), (-13306093077/70368744177664)), (57/70368744177664), by norm_num⟩
  | 10 => ⟨((-56472977505/281474976710656), (6127682313/140737488355328)), (27/140737488355328), by norm_num⟩
  | 11 => ⟨((94570062661/2251799813685248), (-20522923561/2251799813685248)), (93/2251799813685248), by norm_num⟩
  | 12 => ⟨((-72585205509/9007199254740992), (246123843/140737488355328)), (73/9007199254740992), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (3813907958935/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889647154565309/316912650057057350374175801344), (4516151666647/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945166202984605/19807040628566084398385987584), (2539933992285/19807040628566084398385987584)), (409/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945071766216467/1237940039285380274899124224), (5396405288421/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221476102345379/19342813113834066795298816), (5395331419159/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775065950329151/4835703278458516698824704), (5056982235607/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629646913586975/302231454903657293676544), (2211859252155/302231454903657293676544)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944305493791727/37778931862957161709568), (7186403323529/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298151984880249/4722366482869645213696), (5387930691687/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405571906195333/147573952589676412928), (7405363099265/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824519928067623/73786976294838206464), (9252141604443/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823827252314473/9223372036854775808), (5201193202349/4611686018427387904)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595068744149613/1152921504606846976), (1299318202171/144115188075855872)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195520407946231/144115188075855872), (2271601751555/36028797018963968)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((746515573378057/18014398509481984), (850748182445/2251799813685248)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490972423269701/9007199254740992), (16984097226785/9007199254740992)), (1391/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115647774882297/2251799813685248), (16937803560445/2251799813685248)), (699/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110460472986221/1125899906842624), (12645496579949/562949953421312)), (33/17592186044416), by norm_num⟩
  | 0 => ⟨((1094778865769345/1125899906842624), (50119278288659/1125899906842624)), (4287/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1094778865769345/1125899906842624), (50119278288659/1125899906842624)), (16353611472701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132785873727563/140737488355328), (48733929459065/562949953421312)), (545/70368744177664), by norm_num⟩
  | 2 => ⟨((993830498092605/1125899906842624), (183921923832013/1125899906842624)), (17965/1125899906842624), by norm_num⟩
  | 3 => ⟨((423604167242487/562949953421312), (162347661689317/562949953421312)), (18793/562949953421312), by norm_num⟩
  | 4 => ⟨((1087725303600081/2251799813685248), (488648382441199/1125899906842624)), (19561/281474976710656), by norm_num⟩
  | 5 => ⟨((12658616901489/281474976710656), (472080339392759/1125899906842624)), (574033/4503599627370496), by norm_num⟩
  | 6 => ⟨((-391324301907481/2251799813685248), (21230605409165/562949953421312)), (1066013/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-20698472367/2147483648)), (1/4294967296), by norm_num⟩, -2, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1931040333/1073741824), (-86220950867/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1220007239891559/9007199254740992), (428764399265039/4503599627370496)), (262955/2251799813685248), by norm_num⟩
  | 1 => ⟨((44638818257/137438953472), (-15688051241/68719476736)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((-53519605641/137438953472), (18809151955/68719476736)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((5347267057/17179869184), (-30068251039/137438953472)), (21/68719476736), by norm_num⟩
  | 4 => ⟨((-51288745593/274877906944), (18025129257/137438953472)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((24597008121/274877906944), (-34577897789/549755813888)), (13/137438953472), by norm_num⟩
  | 6 => ⟨((-78641399331/2199023255552), (27638059217/1099511627776)), (43/1099511627776), by norm_num⟩
  | 7 => ⟨((53878239915/4398046511104), (-9467595935/1099511627776)), (61/4398046511104), by norm_num⟩
  | 8 => ⟨((-64597188399/17592186044416), (22702303537/8796093022208)), (19/4398046511104), by norm_num⟩
  | 9 => ⟨((68843241199/70368744177664), (-48389107851/70368744177664)), (83/70368744177664), by norm_num⟩
  | 10 => ⟨((-33015776527/140737488355328), (11603201297/70368744177664)), (41/140737488355328), by norm_num⟩
  | 11 => ⟨((7197124951/140737488355328), (-40470198603/1125899906842624)), (37/562949953421312), by norm_num⟩
  | 12 => ⟨((-46021205061/4503599627370496), (32347765973/4503599627370496)), (61/4503599627370496), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (3294214816015/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222398353262117/79228162514264337593543950336), (3900309026437/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890211667544201/39614081257132168796771975168), (2193567426893/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945007737773215/1237940039285380274899124224), (4660473360589/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885840508963717/77371252455336267181195264), (2329754388383/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387503089826729/2417851639229258349412352), (4367264706217/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314797375071583/151115727451828646838272), (3820331956313/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888441965714971/75557863725914323419136), (3103059211621/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40563301995183/147573952589676412928), (4652908172439/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622114656533903/590295810358705651712), (1598754532571/147573952589676412928)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912152400782151/36893488147419103232), (7989677526027/73786976294838206464)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911793361838685/4611686018427387904), (4491378831275/4611686018427387904)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594830074030265/1152921504606846976), (8975722611847/1152921504606846976)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195313659218841/144115188075855872), (980730682623/18014398509481984)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((373181297726321/9007199254740992), (11477491289/35184372088832)), (277/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490597253094929/9007199254740992), (14663523663095/9007199254740992)), (347/2251799813685248), by norm_num⟩
  | 2 => ⟨((278820870150279/562949953421312), (1827756940407/281474976710656)), (1393/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109941095068395/1125899906842624), (21829517231191/1125899906842624)), (263/140737488355328), by norm_num⟩
  | 0 => ⟨((273461901637395/281474976710656), (43245400439459/1125899906842624)), (4261/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((273461901637395/281474976710656), (43245400439459/1125899906842624)), (16254429343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((530523368211833/562949953421312), (10503570849747/140737488355328)), (269/35184372088832), by norm_num⟩
  | 2 => ⟨((993657935343953/1125899906842624), (79188421657639/562949953421312)), (8755/562949953421312), by norm_num⟩
  | 3 => ⟨((427334997598503/562949953421312), (279549551747053/1125899906842624)), (17917/562949953421312), by norm_num⟩
  | 4 => ⟨((72421274400555/140737488355328), (212205909776645/562949953421312)), (36099/562949953421312), by norm_num⟩
  | 5 => ⟨((138151206487699/1125899906842624), (873582304243077/2251799813685248)), (128735/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1220007239891559/9007199254740992), (428764399265039/4503599627370496)), (262955/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-86220950867/8589934592)), (1/4294967296), by norm_num⟩, -2, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2001111149/1073741824), (-89349612801/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-781783007240503/9007199254740992), (578897897630573/4503599627370496)), (61291/562949953421312), by norm_num⟩
  | 1 => ⟨((14821302745/68719476736), (-43899756939/137438953472)), (39/137438953472), by norm_num⟩
  | 2 => ⟨((-18414776875/68719476736), (54543398971/137438953472)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((1906625063/8589934592), (-45178418269/137438953472)), (11/34359738368), by norm_num⟩
  | 4 => ⟨((-18951141191/137438953472), (7016509499/34359738368)), (57/274877906944), by norm_num⟩
  | 5 => ⟨((37673453413/549755813888), (-6974148445/68719476736)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((-31205004969/1099511627776), (46213620927/1099511627776)), (25/549755813888), by norm_num⟩
  | 7 => ⟨((5538680311/549755813888), (-256331549/17179869184)), (37/2199023255552), by norm_num⟩
  | 8 => ⟨((-860193971/274877906944), (81530876245/17592186044416)), (47/8796093022208), by norm_num⟩
  | 9 => ⟨((30400024443/35184372088832), (-45021470343/35184372088832)), (27/17592186044416), by norm_num⟩
  | 10 => ⟨((-30216489157/140737488355328), (174803361/549755813888)), (55/140737488355328), by norm_num⟩
  | 11 => ⟨((27303692669/562949953421312), (-80871802723/1125899906842624)), (51/562949953421312), by norm_num⟩
  | 12 => ⟨((-22615709159/2251799813685248), (4186643341/281474976710656)), (87/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (1409886073997/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779088359524621/633825300114114700748351602688), (1669107727597/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890101036433839/39614081257132168796771975168), (938716577091/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889898112575257/2475880078570760549798248448), (3988785624741/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771563860265555/154742504910672534362390528), (3987930916361/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387475685509227/2417851639229258349412352), (1868888625105/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314773450774297/151115727451828646838272), (1634823635819/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472071716535087/18889465931478580854784), (5311474993055/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297909696231723/4722366482869645213696), (1991058746445/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405488945209145/147573952589676412928), (1368248243801/147573952589676412928)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824107075793383/73786976294838206464), (3418807240335/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823365475543131/9223372036854775808), (3843665679581/4611686018427387904)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594610315626639/1152921504606846976), (1920275736587/288230376151711744)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((298780760964773/36028797018963968), (839245237401/18014398509481984)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492442607596801/36028797018963968), (10056945961071/36028797018963968)), (553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490249853297033/9007199254740992), (12546709221679/9007199254740992)), (1385/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114944794447661/2251799813685248), (6255021033001/1125899906842624)), (695/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109454743779077/1125899906842624), (18673544804125/1125899906842624)), (131/70368744177664), by norm_num⟩
  | 0 => ⟨((546480489748237/562949953421312), (36981915450617/1125899906842624)), (4237/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((546480489748237/562949953421312), (36981915450617/1125899906842624)), (16162876609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66235685860033/70368744177664), (71799971363195/1125899906842624)), (8505/1125899906842624), by norm_num⟩
  | 2 => ⟨((496473653716115/562949953421312), (135165701862319/1125899906842624)), (17097/1125899906842624), by norm_num⟩
  | 3 => ⟨((859467686688637/1125899906842624), (476818299409051/2251799813685248)), (68523/2251799813685248), by norm_num⟩
  | 4 => ⟨((1211201417915011/2251799813685248), (727968655603041/2251799813685248)), (33409/562949953421312), by norm_num⟩
  | 5 => ⟨((208071451450483/1125899906842624), (783121716686785/2251799813685248)), (115083/1125899906842624), by norm_num⟩
  | 6 => ⟨((-781783007240503/9007199254740992), (578897897630573/4503599627370496)), (61291/562949953421312), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-89349612801/8589934592)), (1/4294967296), by norm_num⟩, -2, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-16524560409/8589934592), (-92227702785/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-336767743942685/9007199254740992), (4967941860935/35184372088832)), (55019/562949953421312), by norm_num⟩
  | 1 => ⟨((26360846205/274877906944), (-24887732977/68719476736)), (71/274877906944), by norm_num⟩
  | 2 => ⟨((-4225889721/34359738368), (15958943677/34359738368)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((3613064375/34359738368), (-27289254887/68719476736)), (21/68719476736), by norm_num⟩
  | 4 => ⟨((-9267327147/137438953472), (17498889197/68719476736)), (7/34359738368), by norm_num⟩
  | 5 => ⟨((19016179849/549755813888), (-17953505841/137438953472)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((-8129256381/549755813888), (61399777695/1099511627776)), (13/274877906944), by norm_num⟩
  | 7 => ⟨((23829863921/4398046511104), (-89992754485/4398046511104)), (79/4398046511104), by norm_num⟩
  | 8 => ⟨((-7640299269/4398046511104), (3606669653/549755813888)), (53/8796093022208), by norm_num⟩
  | 9 => ⟨((17419538401/35184372088832), (-16446088905/8796093022208)), (31/17592186044416), by norm_num⟩
  | 10 => ⟨((-4468023383/35184372088832), (4218338517/8796093022208)), (33/70368744177664), by norm_num⟩
  | 11 => ⟨((16669459935/562949953421312), (-15737926791/140737488355328)), (63/562949953421312), by norm_num⟩
  | 12 => ⟨((-7126053425/1125899906842624), (107645293895/4503599627370496)), (55/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418293/10141204801825835211973625643008), (1191663600681/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778997490583497/633825300114114700748351602688), (1410623147703/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472499731001647/9903520314283042199192993792), (3173360035125/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889789764790349/2475880078570760549798248448), (3371032623609/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771455677394167/154742504910672534362390528), (1685143775719/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549801495729241/9671406556917033397649408), (1579426551871/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629502693807573/302231454903657293676544), (2763205173823/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888143518970453/75557863725914323419136), (2244362562783/37778931862957161709568)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324450618159495/1180591620717411303424), (1682623181501/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810904407016095/295147905179352825856), (4625106074331/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823924065067371/73786976294838206464), (2889111180903/36893488147419103232)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823160546825135/9223372036854775808), (1624039230205/2305843009213693952)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594406583198533/1152921504606846976), (6490730997547/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298736530387205/36028797018963968), (2836644875667/72057594037927936)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((746089952805079/18014398509481984), (4248872806315/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((23280096182845/140737488355328), (10600875375323/9007199254740992)), (691/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229256182636315/4503599627370496), (21137927343731/4503599627370496)), (2771/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217994173214759/2251799813685248), (246466173349/17592186044416)), (261/140737488355328), by norm_num⟩
  | 0 => ⟨((2184229449096599/2251799813685248), (62460482318541/2251799813685248)), (4215/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184229449096599/2251799813685248), (62460482318541/2251799813685248)), (16078953269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2116954156172465/2251799813685248), (121172427545111/2251799813685248)), (16823/2251799813685248), by norm_num⟩
  | 2 => ⟨((30994735542985/35184372088832), (113916198298871/1125899906842624)), (16721/1125899906842624), by norm_num⟩
  | 3 => ⟨((431100887564737/562949953421312), (12543930126923/70368744177664)), (8211/281474976710656), by norm_num⟩
  | 4 => ⟨((312243677216699/562949953421312), (614784245415939/2251799813685248)), (62013/1125899906842624), by norm_num⟩
  | 5 => ⟨((524903744903883/2251799813685248), (340993888207859/1125899906842624)), (205307/2251799813685248), by norm_num⟩
  | 6 => ⟨((-336767743942685/9007199254740992), (4967941860935/35184372088832)), (55019/562949953421312), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-16524560409/8589934592), (-92227702785/8589934592)), (1/4294967296), by norm_num⟩, -2, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2125249673/1073741824), (-47446198951/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((63882731519161/9007199254740992), (1242855981584811/9007199254740992)), (768843/9007199254740992), by norm_num⟩
  | 1 => ⟨((-160780135/8589934592), (-100096685421/274877906944)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((1697231975/68719476736), (66040222833/137438953472)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((-373257707/17179869184), (-29047322353/68719476736)), (5/17179869184), by norm_num⟩
  | 4 => ⟨((1970096975/137438953472), (38328774481/137438953472)), (55/274877906944), by norm_num⟩
  | 5 => ⟨((-2079679545/274877906944), (-10115183323/68719476736)), (15/137438953472), by norm_num⟩
  | 6 => ⟨((3658929031/1099511627776), (71185463171/1099511627776)), (27/549755813888), by norm_num⟩
  | 7 => ⟨((-1379446211/1099511627776), (-53675005241/2199023255552)), (21/1099511627776), by norm_num⟩
  | 8 => ⟨((1820218817/4398046511104), (70825707999/8796093022208)), (57/8796093022208), by norm_num⟩
  | 9 => ⟨((-4269921609/35184372088832), (-83072490587/35184372088832)), (69/35184372088832), by norm_num⟩
  | 10 => ⟨((140857099/4398046511104), (87693226069/140737488355328)), (75/140737488355328), by norm_num⟩
  | 11 => ⟨((-540698123/70368744177664), (-84155436733/562949953421312)), (37/281474976710656), by norm_num⟩
  | 12 => ⟨((1902577793/1125899906842624), (74030340713/2251799813685248)), (67/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (494810574059/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444728278157049/158456325028528675187087900672), (2342698858779/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889904090895085/39614081257132168796771975168), (2635075831861/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889689122227351/2475880078570760549798248448), (1399601200591/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885677583536373/77371252455336267181195264), (2798566183507/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387426851934515/2417851639229258349412352), (2622979980599/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629461600488783/302231454903657293676544), (143401990749/37778931862957161709568)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472002557169643/18889465931478580854784), (931796336291/18889465931478580854784)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648851367434087/2361183241434822606848), (2794281290149/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621672047945895/590295810358705651712), (3840337469203/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823753666920419/73786976294838206464), (599715521349/9223372036854775808)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822969617259389/9223372036854775808), (337108281225/576460752303423488)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594216612707025/1152921504606846976), (5389101654361/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597390487227605/72057594037927936), (4710258569559/144115188075855872)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491934334467621/36028797018963968), (881873487409/4503599627370496)), (551/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489622942890365/9007199254740992), (4400279618807/4503599627370496)), (1379/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114330484206501/2251799813685248), (8773344309561/2251799813685248)), (691/1125899906842624), by norm_num⟩
  | 1 => ⟨((554282308468207/562949953421312), (3273037198351/281474976710656)), (4163/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182610221861313/2251799813685248), (51827686488947/2251799813685248)), (4195/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2182610221861313/2251799813685248), (51827686488947/2251799813685248)), (16002659324264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057176850835327/1125899906842624), (50235210793925/1125899906842624)), (4163/562949953421312), by norm_num⟩
  | 2 => ⟨((1980814299320225/2251799813685248), (188675748618189/2251799813685248)), (32759/2251799813685248), by norm_num⟩
  | 3 => ⟨((431657681851365/562949953421312), (331940360352207/2251799813685248)), (15781/562949953421312), by norm_num⟩
  | 4 => ⟨((637505440879139/1125899906842624), (254524590670507/1125899906842624)), (115415/2251799813685248), by norm_num⟩
  | 5 => ⟨((606857532926803/2251799813685248), (1125910554997/4398046511104)), (182883/2251799813685248), by norm_num⟩
  | 6 => ⟨((63882731519161/9007199254740992), (1242855981584811/9007199254740992)), (768843/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-47446198951/4294967296)), (1/4294967296), by norm_num⟩, -2, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-8723240287/4294967296), (-48686584853/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((394266717399345/9007199254740992), (557014196406447/4503599627370496)), (2567/35184372088832), by norm_num⟩
  | 1 => ⟨((-509116203/4294967296), (-92066797277/274877906944)), (57/274877906944), by norm_num⟩
  | 2 => ⟨((22059395775/137438953472), (15582594305/34359738368)), (5/17179869184), by norm_num⟩
  | 3 => ⟨((-4978162597/34359738368), (-56264596855/137438953472)), (19/68719476736), by norm_num⟩
  | 4 => ⟨((6740557111/68719476736), (38091838207/137438953472)), (53/274877906944), by norm_num⟩
  | 5 => ⟨((-28521511/536870912), (-82523688093/549755813888)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((13181898001/549755813888), (37246381689/549755813888)), (55/1099511627776), by norm_num⟩
  | 7 => ⟨((-20398423733/2199023255552), (-28818591835/1099511627776)), (11/549755813888), by norm_num⟩
  | 8 => ⟨((13809988873/4398046511104), (39021096707/4398046511104)), (61/8796093022208), by norm_num⟩
  | 9 => ⟨((-16621396953/17592186044416), (-93929856697/35184372088832)), (19/8796093022208), by norm_num⟩
  | 10 => ⟨((562644717/2199023255552), (50873353463/70368744177664)), (43/70368744177664), by norm_num⟩
  | 11 => ⟨((-35459959599/562949953421312), (-100194614601/562949953421312)), (87/562949953421312), by norm_num⟩
  | 12 => ⟨((8002279227/562949953421312), (45222007703/1125899906842624)), (81/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (1603048249621/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778834345632729/633825300114114700748351602688), (1897260711755/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889815551326493/39614081257132168796771975168), (2134037461867/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889595142737977/2475880078570760549798248448), (1133472441873/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771261293043799/154742504910672534362390528), (1133208191881/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549619512829253/9671406556917033397649408), (2124203981813/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258846404860021/604462909807314587353088), (929058639269/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943942822356219/37778931862957161709568), (3018388683495/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648804740131713/2361183241434822606848), (141429466963/295147905179352825856)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810772060289565/295147905179352825856), (3109953892487/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455898550956809/18446744073709551616), (1942600997503/36893488147419103232)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822790833946219/9223372036854775808), (4367773684551/9223372036854775808)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594038594115433/1152921504606846976), (4363928407661/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597313033486169/72057594037927936), (1907057718199/72057594037927936)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491703687000265/36028797018963968), (5712539346097/36028797018963968)), (1101/36028797018963968), by norm_num⟩
  | 3 => ⟨((744668812033035/4503599627370496), (7125587566989/9007199254740992)), (1377/9007199254740992), by norm_num⟩
  | 2 => ⟨((557024817025675/1125899906842624), (3551501342261/1125899906842624)), (1379/2251799813685248), by norm_num⟩
  | 1 => ⟨((138519306711709/140737488355328), (2649549801383/281474976710656)), (2075/1125899906842624), by norm_num⟩
  | 0 => ⟨((2181057751045257/2251799813685248), (41944242739007/2251799813685248)), (8353/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2181057751045257/2251799813685248), (41944242739007/2251799813685248)), (31864174849700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((527939202787447/562949953421312), (40626531355785/1125899906842624)), (16493/2251799813685248), by norm_num⟩
  | 2 => ⟨((247186425175045/281474976710656), (152399611692945/2251799813685248)), (16063/1125899906842624), by norm_num⟩
  | 3 => ⟨((1726284271516309/2251799813685248), (267669372621839/2251799813685248)), (60775/2251799813685248), by norm_num⟩
  | 4 => ⟨((1291593717775907/2251799813685248), (102600911749677/562949953421312)), (107633/2251799813685248), by norm_num⟩
  | 5 => ⟨((166509381652563/562949953421312), (470800973509579/2251799813685248)), (162707/2251799813685248), by norm_num⟩
  | 6 => ⟨((394266717399345/9007199254740992), (557014196406447/4503599627370496)), (2567/35184372088832), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-48686584853/4294967296)), (1/4294967296), by norm_num⟩, -2, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile009Terms1
