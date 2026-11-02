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
namespace Reinmann.XiRectangle.Tile008Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2397/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2397/640))
  have he : value ((3/4), (2397/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-17862266831/8589934592), (-89199694987/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-161562183859759/2251799813685248), (460980794650729/4503599627370496)), (99259/1125899906842624), by norm_num⟩
  | 1 => ⟨((27340422907/137438953472), (-78009652857/274877906944)), (35/137438953472), by norm_num⟩
  | 2 => ⟨((-37901874107/137438953472), (27036085467/68719476736)), (51/137438953472), by norm_num⟩
  | 3 => ⟨((35028769567/137438953472), (-24986648553/68719476736)), (49/137438953472), by norm_num⟩
  | 4 => ⟨((-379376451/2147483648), (4329856249/17179869184)), (71/274877906944), by norm_num⟩
  | 5 => ⟨((6731871165/68719476736), (-76831427871/549755813888)), (81/549755813888), by norm_num⟩
  | 6 => ⟨((-49772560191/1099511627776), (71007316809/1099511627776)), (77/1099511627776), by norm_num⟩
  | 7 => ⟨((9857059933/549755813888), (-28124869397/1099511627776)), (63/2199023255552), by norm_num⟩
  | 8 => ⟨((-54659146409/8796093022208), (9747336963/1099511627776)), (45/4398046511104), by norm_num⟩
  | 9 => ⟨((33677185089/17592186044416), (-48045078285/17592186044416)), (57/17592186044416), by norm_num⟩
  | 10 => ⟨((-18674596715/35184372088832), (53283696885/70368744177664)), (65/70368744177664), by norm_num⟩
  | 11 => ⟨((37655982723/281474976710656), (-53721373477/281474976710656)), (67/281474976710656), by norm_num⟩
  | 12 => ⟨((-17400758837/562949953421312), (49649091415/1125899906842624)), (1/17592186044416), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (1421253139081/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((111172224639017/39614081257132168796771975168), (1681965811997/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889726738307401/39614081257132168796771975168), (945930949413/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889500494107811/2475880078570760549798248448), (4019352502373/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771166324282253/154742504910672534362390528), (1004597970069/38685626227668133590597632)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549530139702751/9671406556917033397649408), (3766221933681/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258767863717175/604462909807314587353088), (3294423970447/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887757379040597/75557863725914323419136), (1337881632707/18889465931478580854784)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648756362388159/2361183241434822606848), (2005986011929/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621410178921251/590295810358705651712), (689218004863/73786976294838206464)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823425424236745/73786976294838206464), (3444052714893/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822599100078907/9223372036854775808), (1935879660907/2305843009213693952)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593844543535549/1152921504606846976), (7736522642039/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((74653354521863/9007199254740992), (6761592248207/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((93214994322311/2251799813685248), (5063335921459/18014398509481984)), (553/18014398509481984), by norm_num⟩
  | 3 => ⟨((372249714927673/2251799813685248), (6315433239129/4503599627370496)), (1385/9007199254740992), by norm_num⟩
  | 2 => ⟨((278424343264735/562949953421312), (6294858853609/1125899906842624)), (1389/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107592552518847/1125899906842624), (9390959479423/562949953421312)), (131/70368744177664), by norm_num⟩
  | 0 => ⟨((1089272420807119/1125899906842624), (37154493978017/1125899906842624)), (2119/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089272420807119/1125899906842624), (37154493978017/1125899906842624)), (8083345653343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2105220798235477/2251799813685248), (71891587082181/1125899906842624)), (16961/2251799813685248), by norm_num⟩
  | 2 => ⟨((489750574334029/562949953421312), (33605932335493/281474976710656)), (33881/2251799813685248), by norm_num⟩
  | 3 => ⟨((418044603925623/562949953421312), (467779405606115/2251799813685248)), (33521/1125899906842624), by norm_num⟩
  | 4 => ⟨((1144579134418715/2251799813685248), (347371298554527/1125899906842624)), (127425/2251799813685248), by norm_num⟩
  | 5 => ⟨((367436800412007/2251799813685248), (706268715016459/2251799813685248)), (26021/281474976710656), by norm_num⟩
  | 6 => ⟨((-161562183859759/2251799813685248), (460980794650729/4503599627370496)), (99259/1125899906842624), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-89199694987/8589934592)), (1/4294967296), by norm_num⟩, -2, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-18252837983/8589934592), (-91150109677/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-403353411506613/9007199254740992), (249344950599647/2251799813685248)), (738913/9007199254740992), by norm_num⟩
  | 1 => ⟨((34875069209/274877906944), (-86236259925/274877906944)), (33/137438953472), by norm_num⟩
  | 2 => ⟨((-3087765983/17179869184), (30540715295/68719476736)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((11664399715/68719476736), (-14421393685/34359738368)), (3/8589934592), by norm_num⟩
  | 4 => ⟨((-33047732923/274877906944), (10214721257/34359738368)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((37452511163/549755813888), (-92609550627/549755813888)), (81/549755813888), by norm_num⟩
  | 6 => ⟨((-8842579533/274877906944), (87460871541/1099511627776)), (79/1099511627776), by norm_num⟩
  | 7 => ⟨((14315951045/1099511627776), (-70798659523/2199023255552)), (33/1099511627776), by norm_num⟩
  | 8 => ⟨((-20280071767/4398046511104), (50146926725/4398046511104)), (49/4398046511104), by norm_num⟩
  | 9 => ⟨((6384196661/4398046511104), (-31572653769/8796093022208)), (1/274877906944), by norm_num⟩
  | 10 => ⟨((-28940465873/70368744177664), (17890412793/17592186044416)), (75/70368744177664), by norm_num⟩
  | 11 => ⟨((29816186943/281474976710656), (-18431765911/70368744177664)), (5/17592186044416), by norm_num⟩
  | 12 => ⟨((-7039634893/281474976710656), (17407041711/281474976710656)), (39/562949953421312), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (636684420405/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444671674859097/158456325028528675187087900672), (3013681488355/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889649314175485/39614081257132168796771975168), (847438673919/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472354584200175/618970019642690137449562112), (3600832846419/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771084285964191/154742504910672534362390528), (3599953836427/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774726677568663/4835703278458516698824704), (1687011496201/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258700803503611/604462909807314587353088), (2951336635185/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235956080351013/9444732965739290427392), (1198543068527/18889465931478580854784)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324357844869269/1180591620717411303424), (3594098690089/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810649332501065/295147905179352825856), (1234849897839/147573952589676412928)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823286535105825/73786976294838206464), (6170522042959/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822443540934447/9223372036854775808), (216772338945/288230376151711744)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796844923501651/576460752303423488), (1732578990015/288230376151711744)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194319281540147/144115188075855872), (3028416731419/72057594037927936)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((1491240255802305/36028797018963968), (4535439273887/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((186094083189567/1125899906842624), (11313480097987/9007199254740992)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226912435265909/4503599627370496), (11275867530079/2251799813685248)), (2773/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214486693010177/2251799813685248), (33639991441163/2251799813685248)), (4181/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177247399210661/2251799813685248), (66532246455479/2251799813685248)), (4223/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2177247399210661/2251799813685248), (66532246455479/2251799813685248)), (16109470847701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131449842609465/140737488355328), (128659003947393/2251799813685248)), (16833/2251799813685248), by norm_num⟩
  | 2 => ⟨((244631343401739/281474976710656), (240336899809895/2251799813685248)), (33369/2251799813685248), by norm_num⟩
  | 3 => ⟨((1675231421032341/2251799813685248), (417756060283407/2251799813685248)), (65127/2251799813685248), by norm_num⟩
  | 4 => ⟨((292197398289509/562949953421312), (621581078620043/2251799813685248)), (30267/562949953421312), by norm_num⟩
  | 5 => ⟨((435076897076701/2251799813685248), (1290518795817969/4503599627370496)), (192519/2251799813685248), by norm_num⟩
  | 6 => ⟨((-403353411506613/9007199254740992), (249344950599647/2251799813685248)), (738913/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-91150109677/8589934592)), (1/4294967296), by norm_num⟩, -2, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4655269565/2147483648), (-46494504781/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-174609933084493/9007199254740992), (126976197473403/1125899906842624)), (339415/4503599627370496), by norm_num⟩
  | 1 => ⟨((15401843849/274877906944), (-22400415961/68719476736)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((-2782315905/34359738368), (64745529659/137438953472)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((10722569751/137438953472), (-31189775063/68719476736)), (23/68719476736), by norm_num⟩
  | 4 => ⟨((-7748053195/137438953472), (45075022489/137438953472)), (69/274877906944), by norm_num⟩
  | 5 => ⟨((17915803307/549755813888), (-104226857591/549755813888)), (41/274877906944), by norm_num⟩
  | 6 => ⟨((-17261110633/1099511627776), (50209060933/549755813888)), (81/1099511627776), by norm_num⟩
  | 7 => ⟨((14254579053/2199023255552), (-82927343835/2199023255552)), (69/2199023255552), by norm_num⟩
  | 8 => ⟨((-10300258179/4398046511104), (59922713145/4398046511104)), (51/4398046511104), by norm_num⟩
  | 9 => ⟨((6615905631/8796093022208), (-38488648385/8796093022208)), (67/17592186044416), by norm_num⟩
  | 10 => ⟨((-15297941431/70368744177664), (44498600917/35184372088832)), (79/70368744177664), by norm_num⟩
  | 11 => ⟨((8039406885/140737488355328), (-23384999883/70368744177664)), (85/281474976710656), by norm_num⟩
  | 12 => ⟨((-3872812435/281474976710656), (90121790961/1125899906842624)), (21/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (2267879631097/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222327703548645/79228162514264337593543950336), (670876247207/158456325028528675187087900672)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889576180268911/39614081257132168796771975168), (188647932373/2475880078570760549798248448)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944670361652811/1237940039285380274899124224), (400788144727/309485009821345068724781056)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771006775092591/154742504910672534362390528), (100172092791/4835703278458516698824704)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549380797672593/9671406556917033397649408), (3004314929821/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314659356157955/151115727451828646838272), (2627927958643/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887545856203949/75557863725914323419136), (1067198550611/18889465931478580854784)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297354467935253/4722366482869645213696), (3200206041585/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202649150160219/73786976294838206464), (4398026181789/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823155139459815/73786976294838206464), (2747074386675/36893488147419103232)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822296316825647/9223372036854775808), (3088133625269/4611686018427387904)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593543366741891/1152921504606846976), (6170458825181/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194191946568523/144115188075855872), (5392622798765/144115188075855872)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491050919935711/36028797018963968), (8075891356565/36028797018963968)), (1103/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488518903402375/9007199254740992), (5036035918269/4503599627370496)), (1381/9007199254740992), by norm_num⟩
  | 2 => ⟨((556613399749701/1125899906842624), (20075896937129/4503599627370496)), (2769/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213820035612297/2251799813685248), (7485921063249/562949953421312)), (1043/562949953421312), by norm_num⟩
  | 0 => ⟨((2175999737309953/2251799813685248), (29604726973391/1125899906842624)), (4209/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2175999737309953/2251799813685248), (29604726973391/1125899906842624)), (16056065085982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1050597186433035/1125899906842624), (114432691086875/2251799813685248)), (16713/2251799813685248), by norm_num⟩
  | 2 => ⟨((1954846485474461/2251799813685248), (106779175094679/1125899906842624)), (16445/1125899906842624), by norm_num⟩
  | 3 => ⟨((1676799860222401/2251799813685248), (11587225354531/70368744177664)), (63345/2251799813685248), by norm_num⟩
  | 4 => ⟨((1187570774532877/2251799813685248), (276109202770315/1125899906842624)), (57601/1125899906842624), by norm_num⟩
  | 5 => ⟨((490886965346063/2251799813685248), (1164932043414517/4503599627370496)), (356031/4503599627370496), by norm_num⟩
  | 6 => ⟨((-174609933084493/9007199254740992), (126976197473403/1125899906842624)), (339415/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-46494504781/4294967296)), (1/4294967296), by norm_num⟩, -2, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-18969403681/8589934592), (-5920528727/536870912)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((63866897592185/18014398509481984), (1978465134876933/18014398509481984)), (308663/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2869448589/274877906944), (-88889615815/274877906944)), (57/274877906944), by norm_num⟩
  | 2 => ⟨((4224458137/274877906944), (130865024825/274877906944)), (43/137438953472), by norm_num⟩
  | 3 => ⟨((-4146219735/274877906944), (-128441360035/274877906944)), (87/274877906944), by norm_num⟩
  | 4 => ⟨((3052072751/274877906944), (23636734189/68719476736)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((-1797328395/274877906944), (-55677537189/274877906944)), (5/34359738368), by norm_num⟩
  | 6 => ⟨((3528082523/1099511627776), (109292740509/1099511627776)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((-2968063915/2199023255552), (-91944515799/2199023255552)), (69/2199023255552), by norm_num⟩
  | 8 => ⟨((2184820771/4398046511104), (16920313515/1099511627776)), (13/1099511627776), by norm_num⟩
  | 9 => ⟨((-2859142863/17592186044416), (-44285182803/8796093022208)), (35/8796093022208), by norm_num⟩
  | 10 => ⟨((3367428677/70368744177664), (26079003689/17592186044416)), (21/17592186044416), by norm_num⟩
  | 11 => ⟨((-1802761501/140737488355328), (-111691687273/281474976710656)), (23/70368744177664), by norm_num⟩
  | 12 => ⟨((3538747489/1125899906842624), (109623119219/1125899906842624)), (23/281474976710656), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (501025635949/2535301200456458802993406410752)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111159998340891/39614081257132168796771975168), (2371227789827/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889506879644241/39614081257132168796771975168), (2667114452715/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889267170146315/2475880078570760549798248448), (2833170448919/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221366663808863/19342813113834066795298816), (2832452181609/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774656009304121/4835703278458516698824704), (663665244425/2417851639229258349412352)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258577336909661/604462909807314587353088), (2322065656401/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943724194851411/37778931862957161709568), (3771927148097/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((10135011890429/36893488147419103232), (1413847513767/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810546575231479/295147905179352825856), (485756230003/73786976294838206464)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911515225169293/36893488147419103232), (2427258880565/36893488147419103232)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822156555697199/9223372036854775808), (682143624243/1152921504606846976)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199175530909411/144115188075855872), (1362980940755/288230376151711744)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194070937525407/144115188075855872), (2382280290257/72057594037927936)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((93179427744213/2251799813685248), (222972175537/1125899906842624)), (551/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488296316319361/9007199254740992), (8898389181503/9007199254740992)), (345/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226015917807707/4503599627370496), (2216926513413/562949953421312)), (2765/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106591069229237/1125899906842624), (26450147267329/2251799813685248)), (4163/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174797796968251/2251799813685248), (52291074002635/2251799813685248)), (8393/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2174797796968251/2251799813685248), (52291074002635/2251799813685248)), (32016762740325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32800228514357/35184372088832), (12625735184239/281474976710656)), (16603/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952438145993821/2251799813685248), (94161577909471/1125899906842624)), (16223/1125899906842624), by norm_num⟩
  | 3 => ⟨((1677124707073123/2251799813685248), (163286856567009/1125899906842624)), (61693/2251799813685248), by norm_num⟩
  | 4 => ⟨((600874215487261/1125899906842624), (243229810949007/1125899906842624)), (3431/70368744177664), by norm_num⟩
  | 5 => ⟨((134065683844727/562949953421312), (1038461916188989/4503599627370496)), (82313/1125899906842624), by norm_num⟩
  | 6 => ⟨((63866897592185/18014398509481984), (1978465134876933/18014398509481984)), (308663/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-5920528727/536870912)), (1/4294967296), by norm_num⟩, -2, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-9649929107/4294967296), (-96378666955/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((211909120444395/9007199254740992), (116065139108421/1125899906842624)), (556489/9007199254740992), by norm_num⟩
  | 1 => ⟨((-19373260229/274877906944), (-84887715591/274877906944)), (53/274877906944), by norm_num⟩
  | 2 => ⟨((3627318807/34359738368), (31787608653/68719476736)), (41/137438953472), by norm_num⟩
  | 3 => ⟨((-14488634689/137438953472), (-63484776761/137438953472)), (43/137438953472), by norm_num⟩
  | 4 => ⟨((21702035269/274877906944), (95091697311/274877906944)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((-13002697491/274877906944), (-14243463329/68719476736)), (21/137438953472), by norm_num⟩
  | 6 => ⟨((3246050043/137438953472), (56892803709/549755813888)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((-22226964287/2199023255552), (-97391776117/2199023255552)), (39/1099511627776), by norm_num⟩
  | 8 => ⟨((4161627141/1099511627776), (72939921723/4398046511104)), (15/1099511627776), by norm_num⟩
  | 9 => ⟨((-22163770199/17592186044416), (-97114878905/17592186044416)), (41/8796093022208), by norm_num⟩
  | 10 => ⟨((6639672169/17592186044416), (14546508849/8796093022208)), (51/35184372088832), by norm_num⟩
  | 11 => ⟨((-7232974619/70368744177664), (-63385376039/140737488355328)), (57/140737488355328), by norm_num⟩
  | 12 => ⟨((14445370333/562949953421312), (63295205557/562949953421312)), (59/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (876929289781/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889250694584093/316912650057057350374175801344), (129688165077/39614081257132168796771975168)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472360256249899/9903520314283042199192993792), (1166964121689/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944598633741647/1237940039285380274899124224), (619807569893/618970019642690137449562112)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770863484137091/154742504910672534362390528), (2478590959471/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549246637473989/9671406556917033397649408), (1161499976301/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629260104709515/302231454903657293676544), (2031946118035/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887355709298859/75557863725914323419136), (412580013433/9444732965739290427392)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297212144359141/4722366482869645213696), (618591819861/1180591620717411303424)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810498985825863/295147905179352825856), (3400447628333/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113931987473723/4611686018427387904), (1061962518745/18446744073709551616)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822023516795901/9223372036854775808), (4775108442523/9223372036854775808)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796635880749901/576460752303423488), (2385229374781/576460752303423488)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193955633533387/144115188075855872), (1042231472403/36028797018963968)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((745349563517151/18014398509481984), (390184453761/2251799813685248)), (1101/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488083831922833/9007199254740992), (1946363391729/2251799813685248)), (689/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225597407134339/4503599627370496), (15516321423103/4503599627370496)), (2761/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106285211820453/1125899906842624), (5784609983225/562949953421312)), (4155/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086819004810663/1125899906842624), (22867618659991/1125899906842624)), (523/140737488355328), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1086819004810663/1125899906842624), (22867618659991/1125899906842624)), (1995087206792787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((524315089671417/562949953421312), (11036932503235/281474976710656)), (1031/140737488355328), by norm_num⟩
  | 2 => ⟨((1949864680318727/2251799813685248), (164471608034405/2251799813685248)), (16011/1125899906842624), by norm_num⟩
  | 3 => ⟨((1676401844765709/2251799813685248), (142418245828285/1125899906842624)), (60135/2251799813685248), by norm_num⟩
  | 4 => ⟨((1212004416008949/2251799813685248), (212052784251811/1125899906842624)), (6547/140737488355328), by norm_num⟩
  | 5 => ⟨((1144941182919557/4503599627370496), (913079073470825/4503599627370496)), (304443/4503599627370496), by norm_num⟩
  | 6 => ⟨((211909120444395/9007199254740992), (116065139108421/1125899906842624)), (556489/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-96378666955/8589934592)), (1/4294967296), by norm_num⟩, -2, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-19614186453/8589934592), (-6121771475/536870912)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((363560934946313/9007199254740992), (210782491341073/2251799813685248)), (62245/1125899906842624), by norm_num⟩
  | 1 => ⟨((-33778974119/274877906944), (-19584107189/68719476736)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((25710211157/137438953472), (931628965/2147483648)), (19/68719476736), by norm_num⟩
  | 3 => ⟨((-13045885791/68719476736), (-60509126135/137438953472)), (5/17179869184), by norm_num⟩
  | 4 => ⟨((39718492011/274877906944), (92110696103/274877906944)), (63/274877906944), by norm_num⟩
  | 5 => ⟨((-3023096003/34359738368), (-3505413513/17179869184)), (5/34359738368), by norm_num⟩
  | 6 => ⟨((24543689633/549755813888), (56918987167/549755813888)), (43/549755813888), by norm_num⟩
  | 7 => ⟨((-5337415271/274877906944), (-49511752447/1099511627776)), (39/1099511627776), by norm_num⟩
  | 8 => ⟨((2031235069/274877906944), (18842455157/1099511627776)), (61/4398046511104), by norm_num⟩
  | 9 => ⟨((-10994027989/4398046511104), (-50992246673/8796093022208)), (43/8796093022208), by norm_num⟩
  | 10 => ⟨((26777251915/35184372088832), (62098815659/35184372088832)), (27/17592186044416), by norm_num⟩
  | 11 => ⟨((-14822535323/70368744177664), (-68749540957/140737488355328)), (31/70368744177664), by norm_num⟩
  | 12 => ⟨((30085027583/562949953421312), (69769840009/562949953421312)), (65/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (189478325725/1267650600228229401496703205376)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778445580175737/633825300114114700748351602688), (896641943595/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472344571293641/9903520314283042199192993792), (2017042514187/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118070666552895/154742504910672534362390528), (33478257331/38685626227668133590597632)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770796947182009/154742504910672534362390528), (1071023537443/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549184328825597/9671406556917033397649408), (1003786420819/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258465759053653/604462909807314587353088), (878015079775/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887267358050671/75557863725914323419136), (356553977511/9444732965739290427392)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297145995098529/4722366482869645213696), (2138346779311/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810453600887271/295147905179352825856), (734659977375/147573952589676412928)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911399307477095/36893488147419103232), (917730252375/18446744073709551616)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455474141362627/2305843009213693952), (2063258800075/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593145286090403/1152921504606846976), (4122435559313/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596922750966087/72057594037927936), (900635950847/36028797018963968)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490534995785625/36028797018963968), (5394653532279/36028797018963968)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487880527766701/9007199254740992), (3363655543829/4503599627370496)), (1377/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225196355138931/4503599627370496), (6703358205595/2251799813685248)), (2757/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211982654800413/2251799813685248), (19990700414209/2251799813685248)), (4147/2251799813685248), by norm_num⟩
  | 0 => ⟨((135782326294801/140737488355328), (9876559701699/562949953421312)), (1043/281474976710656), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((135782326294801/140737488355328), (9876559701699/562949953421312)), (3978730321788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2095332943333287/2251799813685248), (76230563313753/2251799813685248)), (8197/1125899906842624), by norm_num⟩
  | 2 => ⟨((1947157566133219/2251799813685248), (141867327308063/2251799813685248)), (31621/2251799813685248), by norm_num⟩
  | 3 => ⟨((1674791971236681/2251799813685248), (122674332805325/1125899906842624)), (58671/2251799813685248), by norm_num⟩
  | 4 => ⟨((609452972355911/1125899906842624), (182479798080215/1125899906842624)), (25015/562949953421312), by norm_num⟩
  | 5 => ⟨((1201293460461481/4503599627370496), (790214864813475/4503599627370496)), (281521/4503599627370496), by norm_num⟩
  | 6 => ⟨((363560934946313/9007199254740992), (210782491341073/2251799813685248)), (62245/1125899906842624), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-6121771475/536870912)), (1/4294967296), by norm_num⟩, -2, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile008Terms2
