/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile017Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/128))
  have he : value ((3/4), (987/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1116391677/2147483648), (-22955803857/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((791444437515579/2251799813685248), (1079974246640079/2251799813685248)), (316387/562949953421312), by norm_num⟩
  | 1 => ⟨((-4185390323/17179869184), (-2855610291/8589934592)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((1450545751/17179869184), (989679111/8589934592)), (3/17179869184), by norm_num⟩
  | 3 => ⟨((-10724711441/549755813888), (-14634523423/549755813888)), (3/68719476736), by norm_num⟩
  | 4 => ⟨((3716901749/1099511627776), (5071939325/1099511627776)), (9/1099511627776), by norm_num⟩
  | 5 => ⟨((-8244351897/17592186044416), (-5624960709/8796093022208)), (21/17592186044416), by norm_num⟩
  | 6 => ⟨((7619399031/140737488355328), (10397135083/140737488355328)), (21/140737488355328), by norm_num⟩
  | 7 => ⟨((-188620177/35184372088832), (-4118139925/562949953421312)), (35/2251799813685248), by norm_num⟩
  | 8 => ⟨((8367458809/18014398509481984), (11417908313/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 9 => ⟨((-10310898635/288230376151711744), (-14069850587/288230376151711744)), (17/144115188075855872), by norm_num⟩
  | 10 => ⟨((11435152509/4611686018427387904), (15603963625/4611686018427387904)), (5/576460752303423488), by norm_num⟩
  | 11 => ⟨((-720567611/4611686018427387904), (-3933033961/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | 12 => ⟨((10655134037/1180591620717411303424), (7269790403/590295810358705651712)), (41/1180591620717411303424), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455309/5070602400912917605986812821504), (1222332631865/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781167814930169/633825300114114700748351602688), (181284862759/79228162514264337593543950336)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892440448682527/39614081257132168796771975168), (407871528713/9903520314283042199192993792)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892383792165129/2475880078570760549798248448), (1733361875545/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1774049600439237/154742504910672534362390528), (433314559221/38685626227668133590597632)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((388058296902191/2417851639229258349412352), (1624819480281/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630566503446969/302231454903657293676544), (177700865955/75557863725914323419136)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945800345828949/37778931862957161709568), (1154952392595/37778931862957161709568)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300395169294789/4722366482869645213696), (433061980997/1180591620717411303424)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1625373474231051/590295810358705651712), (1190773655911/295147905179352825856)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((57136857586961/2305843009213693952), (2976493758727/73786976294838206464)), (1485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((57130382181603/288230376151711744), (3347949945633/9223372036854775808)), (1671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799708746315047/576460752303423488), (836798254015/288230376151711744)), (1671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149916224224003/18014398509481984), (2927942324977/144115188075855872)), (1463/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498753658820515/36028797018963968), (4390210313935/36028797018963968)), (549/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498140257432421/9007199254740992), (685597779711/1125899906842624)), (687/2251799813685248), by norm_num⟩
  | 2 => ⟨((140354690244613/281474976710656), (5480311056109/2251799813685248)), (43/35184372088832), by norm_num⟩
  | 1 => ⟨((560649713927589/562949953421312), (8209287943845/1125899906842624)), (2069/562949953421312), by norm_num⟩
  | 0 => ⟨((1116671430151901/1125899906842624), (16373857302601/1125899906842624)), (8313/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116671430151901/1125899906842624), (16373857302601/1125899906842624)), (31711582664107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553640235751785/562949953421312), (16239648427073/562949953421312)), (16733/1125899906842624), by norm_num⟩
  | 2 => ⟨((1088032009243481/1125899906842624), (63884348717315/1125899906842624)), (33879/1125899906842624), by norm_num⟩
  | 3 => ⟨((261953224251459/281474976710656), (123471395408557/1125899906842624)), (17331/281474976710656), by norm_num⟩
  | 4 => ⟨((961601182367767/1125899906842624), (14363501557079/70368744177664)), (72119/562949953421312), by norm_num⟩
  | 5 => ⟨((387184252936447/562949953421312), (24534969754037/70368744177664)), (305263/1125899906842624), by norm_num⟩
  | 6 => ⟨((791444437515579/2251799813685248), (1079974246640079/2251799813685248)), (316387/562949953421312), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/2147483648), (-22955803857/4294967296)), (1/2147483648), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-55294967/67108864), (-18192044143/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-285919694048567/1125899906842624), (-3146502199939/8796093022208)), (10675/8796093022208), by norm_num⟩
  | 1 => ⟨((9586025679/34359738368), (13503070247/34359738368)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((-5265662805/34359738368), (-3708659727/17179869184)), (55/68719476736), by norm_num⟩
  | 3 => ⟨((3856614577/68719476736), (2716252767/34359738368)), (21/68719476736), by norm_num⟩
  | 4 => ⟨((-4236924167/274877906944), (-2984108669/137438953472)), (3/34359738368), by norm_num⟩
  | 5 => ⟨((3723789565/1099511627776), (5245405527/1099511627776)), (11/549755813888), by norm_num⟩
  | 6 => ⟨((-10909335937/17592186044416), (-7683555961/8796093022208)), (67/17592186044416), by norm_num⟩
  | 7 => ⟨((1712161503/17592186044416), (19294283427/140737488355328)), (87/140737488355328), by norm_num⟩
  | 8 => ⟨((-7524006669/562949953421312), (-10598468437/562949953421312)), (25/281474976710656), by norm_num⟩
  | 9 => ⟨((7347525499/4503599627370496), (10349873481/4503599627370496)), (51/4503599627370496), by norm_num⟩
  | 10 => ⟨((-12915330887/72057594037927936), (-4548199277/18014398509481984)), (23/18014398509481984), by norm_num⟩
  | 11 => ⟨((10319229981/576460752303423488), (454246147/18014398509481984)), (19/144115188075855872), by norm_num⟩
  | 12 => ⟨((-3778944289/2305843009213693952), (-5323097591/2305843009213693952)), (29/2305843009213693952), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (-1425151837271/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780692968504963/633825300114114700748351602688), (-845037158271/158456325028528675187087900672)), (1447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891905980759019/39614081257132168796771975168), (-3802373047315/39614081257132168796771975168)), (407/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891815591232805/2475880078570760549798248448), (-1009920005985/618970019642690137449562112)), (865/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773481029740183/154742504910672534362390528), (-1009823981401/38685626227668133590597632)), (865/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551699759817189/9671406556917033397649408), (-3786431757249/9671406556917033397649408)), (1623/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315166466236365/151115727451828646838272), (-3312719537533/604462909807314587353088)), (1421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472710212521453/18889465931478580854784), (-5382403616011/75557863725914323419136)), (2309/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299824644475199/4722366482869645213696), (-4036132620113/4722366482869645213696)), (433/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624587957207785/590295810358705651712), (-5548593147105/590295810358705651712)), (2383/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827395979318425/73786976294838206464), (-6934107090269/73786976294838206464)), (745/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827063680011907/9223372036854775808), (-7798622385361/9223372036854775808)), (3355/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598306253294993/1152921504606846976), (-1948952742561/288230376151711744)), (1679/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198354436694697/144115188075855872), (-3409084985543/72057594037927936)), (1471/72057594037927936), by norm_num⟩
  | 4 => ⟨((1497284585439031/36028797018963968), (-5110460622867/18014398509481984)), (1105/9007199254740992), by norm_num⟩
  | 3 => ⟨((374073341705807/2251799813685248), (-12765057565259/9007199254740992)), (5537/9007199254740992), by norm_num⟩
  | 2 => ⟨((560487421171363/1125899906842624), (-6374198323625/1125899906842624)), (1389/562949953421312), by norm_num⟩
  | 1 => ⟨((1118466056076191/1125899906842624), (-19080873215131/1125899906842624)), (2095/281474976710656), by norm_num⟩
  | 0 => ⟨((34713999950195/35184372088832), (-9498611250035/281474976710656)), (4237/281474976710656), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((34713999950195/35184372088832), (-9498611250035/281474976710656)), (16162873388194949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((273678790232941/281474976710656), (-74973011228539/1125899906842624)), (34587/1125899906842624), by norm_num⟩
  | 2 => ⟨((264850437395033/281474976710656), (-72896437377591/562949953421312)), (71865/1125899906842624), by norm_num⟩
  | 3 => ⟨((488976194949615/562949953421312), (-274364045424059/1125899906842624)), (153853/1125899906842624), by norm_num⟩
  | 4 => ⟨((782587548087719/1125899906842624), (-476623139044959/1125899906842624)), (21391/70368744177664), by norm_num⟩
  | 5 => ⟨((684383489877543/2251799813685248), (-331289958796669/562949953421312)), (1531123/2251799813685248), by norm_num⟩
  | 6 => ⟨((-285919694048567/1125899906842624), (-3146502199939/8796093022208)), (10675/8796093022208), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-18192044143/2147483648)), (1/1073741824), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1116391677/1073741824), (-22955803857/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-119895221691107/1125899906842624), (759161276209999/2251799813685248)), (4241003/4503599627370496), by norm_num⟩
  | 1 => ⟨((5072328789/34359738368), (-16058669989/34359738368)), (23/17179869184), by norm_num⟩
  | 2 => ⟨((-3515870399/34359738368), (22262043653/68719476736)), (33/34359738368), by norm_num⟩
  | 3 => ⟨((1624677103/34359738368), (-642953033/4294967296)), (63/137438953472), by norm_num⟩
  | 4 => ⟨((-4504561413/274877906944), (7130577313/137438953472)), (45/274877906944), by norm_num⟩
  | 5 => ⟨((4995718469/1099511627776), (-15816126593/1099511627776)), (51/1099511627776), by norm_num⟩
  | 6 => ⟨((-4617024229/4398046511104), (14617204741/4398046511104)), (49/4398046511104), by norm_num⟩
  | 7 => ⟨((1828729901/8796093022208), (-5789642431/8796093022208)), (5/2199023255552), by norm_num⟩
  | 8 => ⟨((-1267578975/35184372088832), (8026148655/70368744177664)), (57/140737488355328), by norm_num⟩
  | 9 => ⟨((6247955859/1125899906842624), (-19780630439/1125899906842624)), (9/140737488355328), by norm_num⟩
  | 10 => ⟨((-6929204781/9007199254740992), (10968710575/4503599627370496)), (41/4503599627370496), by norm_num⟩
  | 11 => ⟨((6986121829/72057594037927936), (-22117616901/72057594037927936)), (85/72057594037927936), by norm_num⟩
  | 12 => ⟨((-1614136883/144115188075855872), (20441018395/576460752303423488)), (81/576460752303423488), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357927/5070602400912917605986812821504), (1222332631865/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780361339202577/633825300114114700748351602688), (362259450951/79228162514264337593543950336)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472883257161699/9903520314283042199192993792), (3260024133293/39614081257132168796771975168)), (1627/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472854871712859/618970019642690137449562112), (3463407132353/2475880078570760549798248448)), (1729/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773085102252705/154742504910672534362390528), (3462992532625/154742504910672534362390528)), (1729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775664382865365/4835703278458516698824704), (1623057490833/4835703278458516698824704)), (811/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260341433034089/604462909807314587353088), (1419955042569/302231454903657293676544)), (355/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890314000529167/75557863725914323419136), (4614027893199/75557863725914323419136)), (2307/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299429815529627/4722366482869645213696), (3459798161243/4722366482869645213696)), (1731/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25375712003017/9223372036854775808), (4756047964897/590295810358705651712)), (2381/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913359372048247/36893488147419103232), (5943298154293/73786976294838206464)), (2977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826302822861493/9223372036854775808), (3341893939583/4611686018427387904)), (419/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1597546686414645/1152921504606846976), (6680759599547/1152921504606846976)), (1677/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197691266783035/144115188075855872), (91285276575/2251799813685248)), (1469/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496292731671695/36028797018963968), (8756572324097/36028797018963968)), (4413/36028797018963968), by norm_num⟩
  | 3 => ⟨((373764656003581/2251799813685248), (5466894891527/4503599627370496)), (5527/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119747706055601/2251799813685248), (5457949971223/1125899906842624)), (5543/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116644350046341/1125899906842624), (8164560286781/562949953421312)), (4177/562949953421312), by norm_num⟩
  | 0 => ⟨((553640235751785/562949953421312), (32479296854147/1125899906842624)), (4217/281474976710656), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((553640235751785/562949953421312), (32479296854147/1125899906842624)), (16086579442882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1088032009243481/1125899906842624), (63884348717317/1125899906842624)), (4269/140737488355328), by norm_num⟩
  | 2 => ⟨((261953224251459/281474976710656), (123471395408561/1125899906842624)), (69883/1125899906842624), by norm_num⟩
  | 3 => ⟨((961601182367767/1125899906842624), (28727003114159/140737488355328)), (145401/1125899906842624), by norm_num⟩
  | 4 => ⟨((774368505872891/1125899906842624), (196279758032303/562949953421312)), (307725/1125899906842624), by norm_num⟩
  | 5 => ⟨((791444437515551/2251799813685248), (1079974246640113/2251799813685248)), (1275755/2251799813685248), by norm_num⟩
  | 6 => ⟨((-119895221691107/1125899906842624), (759161276209999/2251799813685248)), (4241003/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/1073741824), (-22955803857/2147483648)), (1/1073741824), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-162011325/134217728), (-13325431479/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((1330514706784749/4503599627370496), (52347683299561/1125899906842624)), (185355/562949953421312), by norm_num⟩
  | 1 => ⟨((-16337439057/34359738368), (-321389565/4294967296)), (5/8589934592), by norm_num⟩
  | 2 => ⟨((13147046905/34359738368), (4138052405/68719476736)), (17/34359738368), by norm_num⟩
  | 3 => ⟨((-7053118575/34359738368), (-4439958949/137438953472)), (39/137438953472), by norm_num⟩
  | 4 => ⟨((22703112871/274877906944), (3572919131/274877906944)), (33/274877906944), by norm_num⟩
  | 5 => ⟨((-29231400467/1099511627776), (-2300156603/549755813888)), (45/1099511627776), by norm_num⟩
  | 6 => ⟨((15682041381/2199023255552), (616993207/549755813888)), (13/1099511627776), by norm_num⟩
  | 7 => ⟨((-7211220555/4398046511104), (-4539484613/17592186044416)), (25/8796093022208), by norm_num⟩
  | 8 => ⟨((2901502939/8796093022208), (3653009319/70368744177664)), (21/35184372088832), by norm_num⟩
  | 9 => ⟨((-4150923407/70368744177664), (-1306509265/140737488355328)), (1/8796093022208), by norm_num⟩
  | 10 => ⟨((21378091209/2251799813685248), (1682196435/1125899906842624)), (43/2251799813685248), by norm_num⟩
  | 11 => ⟨((-6255765543/4503599627370496), (-3938022863/18014398509481984)), (53/18014398509481984), by norm_num⟩
  | 12 => ⟨((26848709963/144115188075855872), (2112667765/72057594037927936)), (59/144115188075855872), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (3177058855/158456325028528675187087900672)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222513423697763/79228162514264337593543950336), (60244275769/158456325028528675187087900672)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891247628984813/39614081257132168796771975168), (135535061615/19807040628566084398385987584)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945558306834411/1237940039285380274899124224), (287976531747/2475880078570760549798248448)), (1723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772782638398497/154742504910672534362390528), (143968315553/77371252455336267181195264)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775522820323111/4835703278458516698824704), (269898205017/9671406556917033397649408)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260094133214807/604462909807314587353088), (118059275753/302231454903657293676544)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889912952936557/75557863725914323419136), (191806603139/37778931862957161709568)), (2297/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649564871152667/2361183241434822606848), (143820206693/2361183241434822606848)), (1723/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811817062339869/295147905179352825856), (98848169971/147573952589676412928)), (1185/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826206174420673/73786976294838206464), (61758947261/9223372036854775808)), (2961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825728565522219/9223372036854775808), (8681216809/144115188075855872)), (3331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399243851494053/288230376151711744), (34706700775/72057594037927936)), (833/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197194741932993/144115188075855872), (121391754687/36028797018963968)), (2915/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495554626767805/36028797018963968), (45481090879/2251799813685248)), (2187/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494147667478063/9007199254740992), (908480084853/9007199254740992)), (1367/2251799813685248), by norm_num⟩
  | 2 => ⟨((2237708444645955/4503599627370496), (226692444285/562949953421312)), (5469/2251799813685248), by norm_num⟩
  | 1 => ⟨((557673834883061/562949953421312), (2711773811147/2251799813685248)), (4103/562949953421312), by norm_num⟩
  | 0 => ⟨((138107559122971/140737488355328), (673687685053/281474976710656)), (32851/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((138107559122971/140737488355328), (673687685053/281474976710656)), (125316628462981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2168415497082001/2251799813685248), (5288789099829/1125899906842624)), (64633/2251799813685248), by norm_num⟩
  | 2 => ⟨((1044034610503355/1125899906842624), (20371779365411/2251799813685248)), (3909/70368744177664), by norm_num⟩
  | 3 => ⟨((1936059340544219/2251799813685248), (18890527129247/1125899906842624)), (117125/1125899906842624), by norm_num⟩
  | 4 => ⟨((1663957132990227/2251799813685248), (32483510544863/1125899906842624)), (205335/1125899906842624), by norm_num⟩
  | 5 => ⟨((153462388718927/281474976710656), (48007081932589/1125899906842624)), (630623/2251799813685248), by norm_num⟩
  | 6 => ⟨((1330514706784749/4503599627370496), (52347683299561/1125899906842624)), (185355/562949953421312), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-13325431479/1073741824)), (1/1073741824), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-3708743259/268435456)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((370676894189099/4503599627370496), (-278684612804937/1125899906842624)), (2605001/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1266791983/8589934592), (7619259551/17179869184)), (37/34359738368), by norm_num⟩
  | 2 => ⟨((2269786531/17179869184), (-13651880449/34359738368)), (35/34359738368), by norm_num⟩
  | 3 => ⟨((-677818585/8589934592), (8153628689/34359738368)), (11/17179869184), by norm_num⟩
  | 4 => ⟨((303621967/8589934592), (-3652335353/34359738368)), (41/137438953472), by norm_num⟩
  | 5 => ⟨((-6963424441/549755813888), (5235285163/137438953472)), (61/549755813888), by norm_num⟩
  | 6 => ⟨((4158927227/1099511627776), (-25014324707/2199023255552)), (75/2199023255552), by norm_num⟩
  | 7 => ⟨((-1064542463/1099511627776), (12805615189/4398046511104)), (79/8796093022208), by norm_num⟩
  | 8 => ⟨((3814808077/17592186044416), (-22944582275/35184372088832)), (73/35184372088832), by norm_num⟩
  | 9 => ⟨((-3037874887/70368744177664), (18271632249/140737488355328)), (15/35184372088832), by norm_num⟩
  | 10 => ⟨((1088628219/140737488355328), (-1636918505/70368744177664)), (45/562949953421312), by norm_num⟩
  | 11 => ⟨((-5674356131/4503599627370496), (8532259583/2251799813685248)), (61/4503599627370496), by norm_num⟩
  | 12 => ⟨((1694513555/9007199254740992), (-20383675869/36028797018963968)), (75/36028797018963968), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-406992760745/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889947179563637/316912650057057350374175801344), (-964471381575/316912650057057350374175801344)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891007882093781/39614081257132168796771975168), (-271224942681/4951760157141521099596496896)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890861771208135/2475880078570760549798248448), (-2305095633443/2475880078570760549798248448)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772527670693957/154742504910672534362390528), (-1152369877647/77371252455336267181195264)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550806475415087/9671406556917033397649408), (-2160315455555/9671406556917033397649408)), (1619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629942365350415/302231454903657293676544), (-944949010499/302231454903657293676544)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889572424746627/75557863725914323419136), (-3070375661859/75557863725914323419136)), (2303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649437064173929/2361183241434822606848), (-2302161834543/4722366482869645213696)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1623282301822903/590295810358705651712), (-3164465414401/590295810358705651712)), (2377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57055183307769/2305843009213693952), (-988517885245/18446744073709551616)), (743/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825232490434271/9223372036854775808), (-2223127314231/4611686018427387904)), (209/576460752303423488), by norm_num⟩
  | 6 => ⟨((399119605541869/288230376151711744), (-4443660869943/1152921504606846976)), (1673/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196758860451371/144115188075855872), (-1942643370371/72057594037927936)), (1465/72057594037927936), by norm_num⟩
  | 4 => ⟨((186862345924747/4503599627370496), (-5822100714341/36028797018963968)), (4399/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493324287585039/9007199254740992), (-7267432646383/9007199254740992)), (5505/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236051055068745/4503599627370496), (-14504318336775/4503599627370496)), (11031/4503599627370496), by norm_num⟩
  | 1 => ⟨((139261425675473/140737488355328), (-1355014051473/140737488355328)), (16599/2251799813685248), by norm_num⟩
  | 0 => ⟨((1102295444861231/1125899906842624), (-43056126894685/2251799813685248)), (16707/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1102295444861231/1125899906842624), (-43056126894685/2251799813685248)), (63732151511764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2157548433682923/2251799813685248), (-21076728162485/562949953421312)), (33353/1125899906842624), by norm_num⟩
  | 2 => ⟨((258010701035653/281474976710656), (-80778160754367/1125899906842624)), (16603/281474976710656), by norm_num⟩
  | 3 => ⟨((1880428680905211/2251799813685248), (-296177374318133/2251799813685248)), (65641/562949953421312), by norm_num⟩
  | 4 => ⟨((1531348819711255/2251799813685248), (-247331235182731/1125899906842624)), (507593/2251799813685248), by norm_num⟩
  | 5 => ⟨((932737552991277/2251799813685248), (-672795854716671/2251799813685248)), (456697/1125899906842624), by norm_num⟩
  | 6 => ⟨((370676894189099/4503599627370496), (-278684612804937/1125899906842624)), (2605001/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-3708743259/268435456)), (1/1073741824), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1567053835/1073741824), (-16111272237/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-399129768999371/2251799813685248), (-5286753377711/35184372088832)), (2945495/4503599627370496), by norm_num⟩
  | 1 => ⟨((11851053899/34359738368), (10046432669/34359738368)), (23/17179869184), by norm_num⟩
  | 2 => ⟨((-5765271515/17179869184), (-4887363823/17179869184)), (47/34359738368), by norm_num⟩
  | 3 => ⟨((7479133569/34359738368), (12680494487/68719476736)), (63/68719476736), by norm_num⟩
  | 4 => ⟨((-7276860959/68719476736), (-12337551459/137438953472)), (63/137438953472), by norm_num⟩
  | 5 => ⟨((11328094075/274877906944), (600194165/17179869184)), (51/274877906944), by norm_num⟩
  | 6 => ⟨((-14695635487/1099511627776), (-3114463779/274877906944)), (17/274877906944), by norm_num⟩
  | 7 => ⟨((8170396069/2199023255552), (13852495261/4398046511104)), (39/2199023255552), by norm_num⟩
  | 8 => ⟨((-15898856633/17592186044416), (-13477855559/17592186044416)), (39/8796093022208), by norm_num⟩
  | 9 => ⟨((13750109547/70368744177664), (5828154649/35184372088832)), (69/70368744177664), by norm_num⟩
  | 10 => ⟨((-10702591087/281474976710656), (-4536426113/140737488355328)), (7/35184372088832), by norm_num⟩
  | 11 => ⟨((946649119/140737488355328), (6419983719/1125899906842624)), (81/2251799813685248), by norm_num⟩
  | 12 => ⟨((-9824502017/9007199254740992), (-8328474317/9007199254740992)), (27/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197759336647691/1267650600228229401496703205376), (-49629929795/158456325028528675187087900672)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779710358504959/633825300114114700748351602688), (-235176295135/39614081257132168796771975168)), (1447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890800582283959/39614081257132168796771975168), (-2116304392895/19807040628566084398385987584)), (407/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472660283696839/618970019642690137449562112), (-4496475096617/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772306606566829/154742504910672534362390528), (-2247859669787/77371252455336267181195264)), (1731/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775299386788447/4835703278458516698824704), (-4213933903175/9671406556917033397649408)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259702537619605/604462909807314587353088), (-3686389203461/604462909807314587353088)), (1421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944637755156851/37778931862957161709568), (-1497219234037/18889465931478580854784)), (1155/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649325349352339/2361183241434822606848), (-2245170203377/2361183241434822606848)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405743469584695/147573952589676412928), (-6172077518969/590295810358705651712)), (2385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114086157913833/4611686018427387904), (-7711886202433/73786976294838206464)), (2983/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824794248015323/9223372036854775808), (-4335728728979/4611686018427387904)), (1679/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596037076690405/1152921504606846976), (-4332969796593/576460752303423488)), (1681/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196369197959467/144115188075855872), (-947061242967/18014398509481984)), (1473/72057594037927936), by norm_num⟩
  | 4 => ⟨((747153658802653/18014398509481984), (-1419040190771/4503599627370496)), (2213/18014398509481984), by norm_num⟩
  | 3 => ⟨((373143208624995/2251799813685248), (-14168680798703/9007199254740992)), (2773/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117255927629879/2251799813685248), (-220876623413/35184372088832)), (5567/2251799813685248), by norm_num⟩
  | 1 => ⟨((556445931903807/562949953421312), (-21122730799181/1125899906842624)), (8403/1125899906842624), by norm_num⟩
  | 0 => ⟨((1099717144519929/1125899906842624), (-1309995901661/35184372088832)), (17015/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1099717144519929/1125899906842624), (-1309995901661/35184372088832)), (64907078269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536291243656351/562949953421312), (-1279531993521/17592186044416)), (34507/1125899906842624), by norm_num⟩
  | 2 => ⟨((253958456974151/281474976710656), (-78012113147391/562949953421312)), (35383/562949953421312), by norm_num⟩
  | 3 => ⟨((223726549887933/281474976710656), (-281543121335009/1125899906842624)), (73655/562949953421312), by norm_num⟩
  | 4 => ⟨((160225294548747/281474976710656), (-55945178428517/140737488355328)), (38481/140737488355328), by norm_num⟩
  | 5 => ⟨((373822020254645/2251799813685248), (-509534896326121/1125899906842624)), (74403/140737488355328), by norm_num⟩
  | 6 => ⟨((-399129768999371/2251799813685248), (-5286753377711/35184372088832)), (2945495/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1567053835/1073741824), (-16111272237/1073741824)), (1/1073741824), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1674587515/1073741824), (-17216852893/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-896754173432183/4503599627370496), (37954802210549/562949953421312)), (2571975/2251799813685248), by norm_num⟩
  | 1 => ⟨((14226897285/34359738368), (-2408593519/17179869184)), (21/8589934592), by norm_num⟩
  | 2 => ⟨((-3698000153/8589934592), (1252132355/8589934592)), (45/17179869184), by norm_num⟩
  | 3 => ⟨((10253033519/34359738368), (-1735824023/17179869184)), (127/68719476736), by norm_num⟩
  | 4 => ⟨((-5330145957/34359738368), (7219089165/137438953472)), (67/68719476736), by norm_num⟩
  | 5 => ⟨((8866981541/137438953472), (-6004669561/274877906944)), (113/274877906944), by norm_num⟩
  | 6 => ⟨((-24584493021/1099511627776), (8324239553/1099511627776)), (159/1099511627776), by norm_num⟩
  | 7 => ⟨((14606290305/2199023255552), (-4945648437/2199023255552)), (97/2199023255552), by norm_num⟩
  | 8 => ⟨((-15186463415/8796093022208), (5142093405/8796093022208)), (103/8796093022208), by norm_num⟩
  | 9 => ⟨((7017636199/17592186044416), (-2376151697/17592186044416)), (49/17592186044416), by norm_num⟩
  | 10 => ⟨((-23348422779/281474976710656), (7905709677/281474976710656)), (83/140737488355328), by norm_num⟩
  | 11 => ⟨((8827578229/562949953421312), (-5977985861/1125899906842624)), (1/8796093022208), by norm_num⟩
  | 12 => ⟨((-24475243843/9007199254740992), (4143624045/4503599627370496)), (45/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49435757453803/316912650057057350374175801344), (916749473823/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779553310811499/633825300114114700748351602688), (4343390116253/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1890623783200411/39614081257132168796771975168), (4885613566899/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472613282266035/618970019642690137449562112), (5190135242477/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886059212336143/77371252455336267181195264), (2594601148191/77371252455336267181195264)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775211082993969/4835703278458516698824704), (4863885880273/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259547819050403/604462909807314587353088), (4254908852975/604462909807314587353088)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944511871215871/37778931862957161709568), (864046021459/9444732965739290427392)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298461566646639/4722366482869645213696), (5182649712681/4722366482869645213696)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101419582800265/36893488147419103232), (3561750176487/295147905179352825856)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825052090204339/73786976294838206464), (8900410807475/73786976294838206464)), (5971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824425984876509/9223372036854775808), (10007510578069/9223372036854775808)), (1681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398916884528241/288230376151711744), (1250086974441/144115188075855872)), (1683/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196044419960587/144115188075855872), (8742941778679/144115188075855872)), (1475/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493817294928141/36028797018963968), (13099077583739/36028797018963968)), (2217/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491955326274223/9007199254740992), (8173504208793/4503599627370496)), (11117/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116630984676859/2251799813685248), (16306746455397/2251799813685248)), (11165/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111935985264539/1125899906842624), (3044931413071/140737488355328)), (16869/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097732266268969/1125899906842624), (48316155786225/1125899906842624)), (2139/70368744177664), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1097732266268969/1125899906842624), (48316155786225/1125899906842624)), (8159637719607331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((66762244482657/70368744177664), (94214774983601/1125899906842624)), (34837/562949953421312), by norm_num⟩
  | 2 => ⟨((502782740772413/562949953421312), (178772263590579/1125899906842624)), (143867/1125899906842624), by norm_num⟩
  | 3 => ⟨((217426613479161/281474976710656), (319330725994005/1125899906842624)), (302669/1125899906842624), by norm_num⟩
  | 4 => ⟨((581239237558511/1125899906842624), (493336915018847/1125899906842624)), (159821/281474976710656), by norm_num⟩
  | 5 => ⟨((167790651696873/2251799813685248), (1018729180462055/2251799813685248)), (2440571/2251799813685248), by norm_num⟩
  | 6 => ⟨((-896754173432183/4503599627370496), (37954802210549/562949953421312)), (2571975/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1674587515/1073741824), (-17216852893/1073741824)), (1/536870912), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile017Terms0
