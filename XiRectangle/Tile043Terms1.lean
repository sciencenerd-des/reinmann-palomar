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
namespace Reinmann.XiRectangle.Tile043Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-64510795/33554432), (-257855983/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1026560957246689/9007199254740992), (412612255732835/4503599627370496)), (139789941/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1075546725/4294967296), (-432301421/2147483648)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((1181608849/4294967296), (949863307/4294967296)), (167/4294967296), by norm_num⟩
  | 3 => ⟨((-865420001/4294967296), (-173921917/1073741824)), (125/4294967296), by norm_num⟩
  | 4 => ⟨((118845131/1073741824), (764291021/8589934592)), (35/2147483648), by norm_num⟩
  | 5 => ⟨((-835614217/17179869184), (-335863803/8589934592)), (125/17179869184), by norm_num⟩
  | 6 => ⟨((306005349/17179869184), (245989401/17179869184)), (47/17179869184), by norm_num⟩
  | 7 => ⟨((-48025891/8589934592), (-154426845/34359738368)), (15/17179869184), by norm_num⟩
  | 8 => ⟨((844189345/549755813888), (678620919/549755813888)), (67/274877906944), by norm_num⟩
  | 9 => ⟨((-824388257/2199023255552), (-662703361/2199023255552)), (133/2199023255552), by norm_num⟩
  | 10 => ⟨((90568307/1099511627776), (582443245/8796093022208)), (119/8796093022208), by norm_num⟩
  | 11 => ⟨((-1157811841/70368744177664), (-930733537/70368744177664)), (193/70368744177664), by norm_num⟩
  | 12 => ⟨((423995439/140737488355328), (170419217/70368744177664)), (9/17592186044416), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403057283/10141204801825835211973625643008), (881995738239/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889501462228679/316912650057057350374175801344), (1044058025333/633825300114114700748351602688)), (92303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945002622885003/19807040628566084398385987584), (587183612745/19807040628566084398385987584)), (12981/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889796751499883/2475880078570760549798248448), (1247520468227/2475880078570760549798248448)), (55173/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221432870930853/19342813113834066795298816), (1247245259835/154742504910672534362390528)), (55177/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549808652265247/9671406556917033397649408), (1169000104621/9671406556917033397649408)), (103467/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629505985740769/302231454903657293676544), (1022582857825/604462909807314587353088)), (45271/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944077410427939/37778931862957161709568), (415287350695/18889465931478580854784)), (36787/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297811476311955/4722366482869645213696), (1245382975505/4722366482869645213696)), (13797/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810911025014505/295147905179352825856), (855811730501/295147905179352825856)), (9487/36893488147419103232), by norm_num⟩
  | 8 => ⟨((911970946245347/36893488147419103232), (2138362776409/73786976294838206464)), (11861/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911591181797033/4611686018427387904), (1202027582973/4611686018427387904)), (53387/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398607649372077/288230376151711744), (1201026520363/576460752303423488)), (213611/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74685600080179/9007199254740992), (2099546179019/144115188075855872)), (186981/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492220047238039/36028797018963968), (3144824198051/36028797018963968)), (140307/18014398509481984), by norm_num⟩
  | 3 => ⟨((372496229588413/2251799813685248), (3923175993135/9007199254740992)), (351017/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229399353301861/4503599627370496), (3911418812375/2251799813685248)), (702785/4503599627370496), by norm_num⟩
  | 1 => ⟨((554568163364827/562949953421312), (1459454950947/281474976710656)), (528031/1125899906842624), by norm_num⟩
  | 0 => ⟨((2185038979977379/2251799813685248), (5779455922959/562949953421312)), (2119699/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185038979977379/2251799813685248), (5779455922959/562949953421312)), (8086009987837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120020119566285/2251799813685248), (2804053983391/140737488355328)), (2078617/1125899906842624), by norm_num⟩
  | 2 => ⟨((124691158825073/140737488355328), (84478569720245/2251799813685248)), (1998387/562949953421312), by norm_num⟩
  | 3 => ⟨((1764420589224327/2251799813685248), (74846658679221/1125899906842624)), (3691021/562949953421312), by norm_num⟩
  | 4 => ⟨((1372578462629257/2251799813685248), (29323429375397/281474976710656)), (25100047/2251799813685248), by norm_num⟩
  | 5 => ⟨((1624425368806759/4503599627370496), (571968536335987/4503599627370496)), (71658129/4503599627370496), by norm_num⟩
  | 6 => ⟨((1026560957246689/9007199254740992), (412612255732835/4503599627370496)), (139789941/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/33554432), (-257855983/8388608)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-67604193/33554432), (-540441199/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((209879955122133/2251799813685248), (-859021613019923/9007199254740992)), (137415117/9007199254740992), by norm_num⟩
  | 1 => ⟨((-460878807/2147483648), (471584883/2147483648)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((1061212671/4294967296), (-542932161/2147483648)), (179/4294967296), by norm_num⟩
  | 3 => ⟨((-407255413/2147483648), (833431667/4294967296)), (35/1073741824), by norm_num⟩
  | 4 => ⟨((937740243/8589934592), (-479761833/4294967296)), (41/2147483648), by norm_num⟩
  | 5 => ⟨((-431845341/8589934592), (220938489/4294967296)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((662907097/34359738368), (-169576557/8589934592)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((-872228571/137438953472), (892490177/137438953472)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((1004190253/549755813888), (-1027517289/549755813888)), (187/549755813888), by norm_num⟩
  | 9 => ⟨((-1027659337/2199023255552), (32860361/68719476736)), (97/1099511627776), by norm_num⟩
  | 10 => ⟨((236627307/2199023255552), (-968496351/8796093022208)), (181/8796093022208), by norm_num⟩
  | 11 => ⟨((-792515651/35184372088832), (810925549/35184372088832)), (77/17592186044416), by norm_num⟩
  | 12 => ⟨((608278241/140737488355328), (-77801045/17592186044416)), (15/17592186044416), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (-1038024068129/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778860556699229/633825300114114700748351602688), (-1228568871137/633825300114114700748351602688)), (92321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472461274253903/9903520314283042199192993792), (-1381896112293/39614081257132168796771975168)), (103869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944813305532877/1237940039285380274899124224), (-366990714727/618970019642690137449562112)), (55185/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221411605854511/19342813113834066795298816), (-733811746395/77371252455336267181195264)), (27595/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549649185256365/9671406556917033397649408), (-687768276665/4835703278458516698824704)), (25873/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258872458913953/604462909807314587353088), (-601617065761/302231454903657293676544)), (90567/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943964076216981/37778931862957161709568), (-488645013571/18889465931478580854784)), (147191/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648820754780775/2361183241434822606848), (-183168038639/590295810358705651712)), (110411/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621588401922935/590295810358705651712), (-2013888957817/590295810358705651712)), (151843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823649916632025/73786976294838206464), (-2515922821383/73786976294838206464)), (189847/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822854006646413/9223372036854775808), (-176777296681/576460752303423488)), (213637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594102385432243/1152921504606846976), (-353246027629/144115188075855872)), (13357/72057594037927936), by norm_num⟩
  | 5 => ⟨((597341289385421/72057594037927936), (-2469947860583/144115188075855872)), (93541/72057594037927936), by norm_num⟩
  | 4 => ⟨((23309216244193/562949953421312), (-3699380015149/36028797018963968)), (280789/36028797018963968), by norm_num⟩
  | 3 => ⟨((93090483112893/562949953421312), (-2307271197219/4503599627370496)), (351281/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228326689842037/4503599627370496), (-9200098751111/4503599627370496)), (175861/1125899906842624), by norm_num⟩
  | 1 => ⟨((554166986226217/562949953421312), (-13727899024339/2251799813685248)), (528691/1125899906842624), by norm_num⟩
  | 0 => ⟨((136365420271543/140737488355328), (-13584047067207/1125899906842624)), (265459/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((136365420271543/140737488355328), (-13584047067207/1125899906842624)), (1012645722509288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((66054342873139/70368744177664), (-52648212184411/2251799813685248)), (1041661/562949953421312), by norm_num⟩
  | 2 => ⟨((247863985295063/281474976710656), (-6177535033357/140737488355328)), (501075/140737488355328), by norm_num⟩
  | 3 => ⟨((1741793410303609/2251799813685248), (-174075973139649/2251799813685248)), (1852943/281474976710656), by norm_num⟩
  | 4 => ⟨((666920261183659/1125899906842624), (-269299589656339/2251799813685248)), (25224245/2251799813685248), by norm_num⟩
  | 5 => ⟨((378943159100597/1125899906842624), (-319036091181349/2251799813685248)), (71832317/4503599627370496), by norm_num⟩
  | 6 => ⟨((209879955122133/2251799813685248), (-859021613019923/9007199254740992)), (137415117/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-540441199/16777216)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-4400157/2097152), (-562811511/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-293232306262879/4503599627370496), (-234138617212187/2251799813685248)), (99302523/4503599627370496), by norm_num⟩
  | 1 => ⟨((670566903/4294967296), (535430797/2147483648)), (229/4294967296), by norm_num⟩
  | 2 => ⟨((-803974603/4294967296), (-1283906977/4294967296)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((642615633/4294967296), (128278103/536870912)), (7/134217728), by norm_num⟩
  | 4 => ⟨((-385231247/4294967296), (-1230389827/8589934592)), (271/8589934592), by norm_num⟩
  | 5 => ⟨((738995349/17179869184), (295034595/4294967296)), (131/8589934592), by norm_num⟩
  | 6 => ⟨((-295338909/17179869184), (-235820687/8589934592)), (53/8589934592), by norm_num⟩
  | 7 => ⟨((809362027/137438953472), (161563803/17179869184)), (293/137438953472), by norm_num⟩
  | 8 => ⟨((-485191345/274877906944), (-774826159/274877906944)), (89/137438953472), by norm_num⟩
  | 9 => ⟨((258541785/549755813888), (825756437/1099511627776)), (3/17179869184), by norm_num⟩
  | 10 => ⟨((-495964899/4398046511104), (-792030983/4398046511104)), (93/2199023255552), by norm_num⟩
  | 11 => ⟨((54057813/2199023255552), (690620855/17592186044416)), (41/4398046511104), by norm_num⟩
  | 12 => ⟨((-172833299/35184372088832), (-552012161/70368744177664)), (33/17592186044416), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681581499/10141204801825835211973625643008), (-2774893226773/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778727026297037/633825300114114700748351602688), (-820953572489/158456325028528675187087900672)), (23131/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889694621679745/39614081257132168796771975168), (-3693603303345/39614081257132168796771975168)), (52055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118091649905861/154742504910672534362390528), (-3923612407991/2475880078570760549798248448)), (110641/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885566130246443/77371252455336267181195264), (-980666586177/38685626227668133590597632)), (27667/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387374559674501/2417851639229258349412352), (-1838247359497/4835703278458516698824704)), (25945/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258739984117907/604462909807314587353088), (-3215928139453/604462909807314587353088)), (22709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887712137991043/75557863725914323419136), (-1305999962173/18889465931478580854784)), (73831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648739424668993/2361183241434822606848), (-3916352439803/4722366482869645213696)), (55397/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810681845032069/295147905179352825856), (-5382308458141/590295810358705651712)), (152419/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823367447846591/73786976294838206464), (-6723873022897/73786976294838206464)), (95319/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822534061624205/9223372036854775808), (-1889710652199/2305843009213693952)), (107313/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593779736007559/1152921504606846976), (-7551953502427/1152921504606846976)), (26853/144115188075855872), by norm_num⟩
  | 5 => ⟨((597198612569109/72057594037927936), (-6600214667871/144115188075855872)), (188195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491355756048269/36028797018963968), (-2471211675893/9007199254740992)), (282739/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488894571972277/9007199254740992), (-6164504049101/4503599627370496)), (177103/4503599627370496), by norm_num⟩
  | 2 => ⟨((69599652256967/140737488355328), (-1536061957573/281474976710656)), (177691/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107441507717479/1125899906842624), (-18331682854071/1125899906842624)), (134005/281474976710656), by norm_num⟩
  | 0 => ⟨((2177967351451925/2251799813685248), (-72520891981451/2251799813685248)), (1083873/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2177967351451925/2251799813685248), (-72520891981451/2251799813685248)), (4134647373679732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104220133343983/2251799813685248), (-70143062484439/1125899906842624)), (541621/281474976710656), by norm_num⟩
  | 2 => ⟨((978786423624675/1125899906842624), (-65545988323273/562949953421312)), (2159467/562949953421312), by norm_num⟩
  | 3 => ⟨((1671263583934893/2251799813685248), (-113963102943659/562949953421312)), (1064369/140737488355328), by norm_num⟩
  | 4 => ⟨((574056479167007/1125899906842624), (-169164579110835/562949953421312)), (32173893/2251799813685248), by norm_num⟩
  | 5 => ⟨((95512141294057/562949953421312), (-1380016423754207/4503599627370496)), (6518119/281474976710656), by norm_num⟩
  | 6 => ⟨((-293232306262879/4503599627370496), (-234138617212187/2251799813685248)), (99302523/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4400157/2097152), (-562811511/16777216)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-72957177/33554432), (-291617003/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1002377152830107/9007199254740992), (209394637817059/9007199254740992)), (175275873/9007199254740992), by norm_num⟩
  | 1 => ⟨((1187712503/4294967296), (-15506927/268435456)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((-368919337/1073741824), (19266633/268435456)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((611153409/2147483648), (-255337517/4294967296)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-759329585/4294967296), (317244947/8589934592)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((377372627/4294967296), (-315329631/17179869184)), (277/17179869184), by norm_num⟩
  | 6 => ⟨((-1250314333/34359738368), (32648529/4294967296)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((1775379657/137438953472), (-370873357/137438953472)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((-1102913179/274877906944), (115198209/137438953472)), (13/17179869184), by norm_num⟩
  | 9 => ⟨((609030287/549755813888), (-254450485/1099511627776)), (29/137438953472), by norm_num⟩
  | 10 => ⟨((-151338341/549755813888), (252914281/4398046511104)), (233/4398046511104), by norm_num⟩
  | 11 => ⟨((1093997527/17592186044416), (-57133489/4398046511104)), (53/4398046511104), by norm_num⟩
  | 12 => ⟨((-14158759/1099511627776), (94647591/35184372088832)), (89/35184372088832), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790571753654357/5070602400912917605986812821504), (3824019830817/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222325560052375/79228162514264337593543950336), (2262392105863/316912650057057350374175801344)), (92645/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236194561511805/4951760157141521099596496896), (2544693786447/19807040628566084398385987584)), (104255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889319285358157/2475880078570760549798248448), (2703135845023/1237940039285380274899124224)), (27701/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770984753434981/154742504910672534362390528), (675614850365/19342813113834066795298816)), (110841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387339883148411/2417851639229258349412352), (2532837063443/4835703278458516698824704)), (103953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258618198381703/604462909807314587353088), (4431027825291/604462909807314587353088)), (90999/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887513453344717/75557863725914323419136), (1799431557909/18889465931478580854784)), (147947/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648664575804483/2361183241434822606848), (2697968947661/2361183241434822606848)), (55513/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25330574143021/9223372036854775808), (926948212611/73786976294838206464)), (76383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455776775823211/18446744073709551616), (72372970897/576460752303423488)), (47779/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822238890678035/9223372036854775808), (10413815215319/9223372036854775808)), (26903/1152921504606846976), by norm_num⟩
  | 6 => ⟨((24898151823625/18014398509481984), (2600988289229/288230376151711744)), (107749/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194133261835511/144115188075855872), (2273092318081/36028797018963968)), (188869/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490953438168803/36028797018963968), (3404096787207/9007199254740992)), (141959/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488380566746295/9007199254740992), (4245430203055/2251799813685248)), (355979/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113063858403601/2251799813685248), (4230908437293/562949953421312)), (357601/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106604521929539/1125899906842624), (3155054449101/140737488355328)), (135117/281474976710656), by norm_num⟩
  | 0 => ⟨((1087147093611139/1125899906842624), (24951017178033/562949953421312)), (548633/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087147093611139/1125899906842624), (24951017178033/562949953421312)), (2092868807079124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((523758187982125/562949953421312), (96368871310447/1125899906842624)), (2216265/1125899906842624), by norm_num⟩
  | 2 => ⟨((483170658396593/562949953421312), (179319618409019/1125899906842624)), (4503337/1125899906842624), by norm_num⟩
  | 3 => ⟨((800834967225257/1125899906842624), (615628281438145/2251799813685248)), (18329507/2251799813685248), by norm_num⟩
  | 4 => ⟨((485466866265989/1125899906842624), (437886753158219/1125899906842624)), (18048667/1125899906842624), by norm_num⟩
  | 5 => ⟨((19510291005297/562949953421312), (377617066211949/1125899906842624)), (118414095/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1002377152830107/9007199254740992), (209394637817059/9007199254740992)), (175275873/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72957177/33554432), (-291617003/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-75307241/33554432), (-1204041761/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-115824873898111/4503599627370496), (231555149400177/2251799813685248)), (163857709/9007199254740992), by norm_num⟩
  | 1 => ⟨((283322273/4294967296), (-566413147/2147483648)), (203/4294967296), by norm_num⟩
  | 2 => ⟨((-363353641/4294967296), (726410519/2147483648)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((310661229/4294967296), (-1242137463/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-49801895/1073741824), (398252461/2147483648)), (293/8589934592), by norm_num⟩
  | 5 => ⟨((102191471/4294967296), (-1634395831/17179869184)), (303/17179869184), by norm_num⟩
  | 6 => ⟨((-349487931/34359738368), (698690423/17179869184)), (131/17179869184), by norm_num⟩
  | 7 => ⟨((128059835/34359738368), (-1024060315/68719476736)), (97/34359738368), by norm_num⟩
  | 8 => ⟨((-20529187/17179869184), (41041607/8589934592)), (251/274877906944), by norm_num⟩
  | 9 => ⟨((187222489/549755813888), (-1497168263/1099511627776)), (289/1099511627776), by norm_num⟩
  | 10 => ⟨((-192086481/2199023255552), (768032155/2199023255552)), (299/4398046511104), by norm_num⟩
  | 11 => ⟨((89580381/4398046511104), (-1432700787/17592186044416)), (141/8796093022208), by norm_num⟩
  | 12 => ⟨((-153179427/35184372088832), (306233747/17592186044416)), (243/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275821141/10141204801825835211973625643008), (1182687434203/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444625826261971/158456325028528675187087900672), (1399257067009/316912650057057350374175801344)), (23119/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236180384237543/4951760157141521099596496896), (1573853508691/19807040628566084398385987584)), (104053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889199304744565/2475880078570760549798248448), (3343672463963/2475880078570760549798248448)), (110577/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770865364380345/154742504910672534362390528), (3342810682097/154742504910672534362390528)), (13825/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774624116742365/4835703278458516698824704), (3132969617711/9671406556917033397649408)), (3241/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258521439339771/604462909807314587353088), (171277080995/37778931862957161709568)), (90773/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943678697919781/37778931862957161709568), (2225744422773/37778931862957161709568)), (147551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648606568233643/2361183241434822606848), (3337116370123/4722366482869645213696)), (6919/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620998893016285/590295810358705651712), (4586098183475/590295810358705651712)), (152283/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911456144001811/36893488147419103232), (2864484710963/36893488147419103232)), (47613/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455505788928243/2305843009213693952), (6440070438353/9223372036854775808)), (214393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796635132196425/576460752303423488), (6433799939395/1152921504606846976)), (107281/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193953048525761/144115188075855872), (2811263549379/72057594037927936)), (187933/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490692706902841/36028797018963968), (8419711100259/36028797018963968)), (282279/36028797018963968), by norm_num⟩
  | 3 => ⟨((744035686960723/4503599627370496), (5250017987673/4503599627370496)), (353517/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112779629724571/2251799813685248), (10463204179371/2251799813685248)), (709041/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212480356074727/2251799813685248), (31205960862869/2251799813685248)), (1068593/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173327883488875/2251799813685248), (61680354259517/2251799813685248)), (2157389/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2173327883488875/2251799813685248), (61680354259517/2251799813685248)), (8229785927779387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2095901062947837/2251799813685248), (119061768245103/2251799813685248)), (1070651/562949953421312), by norm_num⟩
  | 2 => ⟨((1944500365617429/2251799813685248), (27704692609083/281474976710656)), (2106273/562949953421312), by norm_num⟩
  | 3 => ⟨((1657322489184591/2251799813685248), (382782054285829/2251799813685248)), (8104589/1125899906842624), by norm_num⟩
  | 4 => ⟨((4510620578563/8796093022208), (281727222450537/1125899906842624)), (917833/70368744177664), by norm_num⟩
  | 5 => ⟨((902295796208265/4503599627370496), (1155753677382371/4503599627370496)), (700327/35184372088832), by norm_num⟩
  | 6 => ⟨((-115824873898111/4503599627370496), (231555149400177/2251799813685248)), (163857709/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75307241/33554432), (-1204041761/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-77483061/33554432), (-1238829619/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((636686484763457/9007199254740992), (314365974050689/4503599627370496)), (101769751/9007199254740992), by norm_num⟩
  | 1 => ⟨((-801206653/4294967296), (-791196659/4294967296)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((1057215145/4294967296), (1044006671/4294967296)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-465008563/2147483648), (-918397819/4294967296)), (155/4294967296), by norm_num⟩
  | 4 => ⟨((9587377/67108864), (151481531/1073741824)), (13/536870912), by norm_num⟩
  | 5 => ⟨((-647721921/8589934592), (-639629511/8589934592)), (7/536870912), by norm_num⟩
  | 6 => ⟨((569791761/17179869184), (562672983/17179869184)), (25/4294967296), by norm_num⟩
  | 7 => ⟨((-429632321/34359738368), (-848529291/68719476736)), (153/68719476736), by norm_num⟩
  | 8 => ⟨((566912163/137438953472), (559829361/137438953472)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((-332469711/274877906944), (-656631901/549755813888)), (123/549755813888), by norm_num⟩
  | 10 => ⟨((350962651/1099511627776), (173288923/549755813888)), (33/549755813888), by norm_num⟩
  | 11 => ⟨((-673607677/8796093022208), (-332595929/4398046511104)), (129/8796093022208), by norm_num⟩
  | 12 => ⟨((148140773/8796093022208), (73144977/4398046511104)), (115/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (1014880569187/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111150424890235/39614081257132168796771975168), (1200593455199/633825300114114700748351602688)), (92319/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889334717510661/39614081257132168796771975168), (1350396456113/39614081257132168796771975168)), (51933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889084455099089/2475880078570760549798248448), (1434458339681/2475880078570760549798248448)), (110367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770750828363297/154742504910672534362390528), (358519590755/38685626227668133590597632)), (110377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48410662155693/302231454903657293676544), (1344044877269/9671406556917033397649408)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258428108169507/604462909807314587353088), (1175635833867/604462909807314587353088)), (90563/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887206356112533/75557863725914323419136), (1909652119551/75557863725914323419136)), (147185/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324275100412705/1180591620717411303424), (1431577820617/4722366482869645213696)), (55203/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810422383632061/295147905179352825856), (1967345555105/590295810358705651712)), (37959/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455680239011987/18446744073709551616), (76799127977/2305843009213693952)), (189837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821809726706739/9223372036854775808), (2762556808891/9223372036854775808)), (213625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593059105565889/1152921504606846976), (2759794674163/1152921504606846976)), (106849/576460752303423488), by norm_num⟩
  | 5 => ⟨((596885416419439/72057594037927936), (2411716527753/144115188075855872)), (46767/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490424465806687/36028797018963968), (3611376130091/36028797018963968)), (280765/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487744935061411/9007199254740992), (4503392641335/9007199254740992)), (351245/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224932842578843/4503599627370496), (8974383115917/4503599627370496)), (351679/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211606440939019/2251799813685248), (6690424989701/1125899906842624)), (1057215/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171840253564589/2251799813685248), (26440480188031/2251799813685248)), (2123197/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171840253564589/2251799813685248), (26440480188031/2251799813685248)), (8099353798873137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1047204764683879/1125899906842624), (12750800236981/562949953421312)), (2072735/1125899906842624), by norm_num⟩
  | 2 => ⟨((1946864869406335/2251799813685248), (23719157769795/562949953421312)), (246851/70368744177664), by norm_num⟩
  | 3 => ⟨((1679226200136879/2251799813685248), (164057194474481/2251799813685248)), (14324711/2251799813685248), by norm_num⟩
  | 4 => ⟨((77518154899739/140737488355328), (122341754186239/1125899906842624)), (11725955/1125899906842624), by norm_num⟩
  | 5 => ⟨((1313127785644743/4503599627370496), (539086332293815/4503599627370496)), (61862475/4503599627370496), by norm_num⟩
  | 6 => ⟨((636686484763457/9007199254740992), (314365974050689/4503599627370496)), (101769751/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-1238829619/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-79508701/33554432), (-317804085/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((413920208784593/4503599627370496), (-311707574924833/18014398509481984)), (124178967/18014398509481984), by norm_num⟩
  | 1 => ⟨((-33405921/134217728), (100626917/2147483648)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((1447438577/4294967296), (-272502743/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-163322347/536870912), (245983703/4294967296)), (13/536870912), by norm_num⟩
  | 4 => ⟨((884570229/4294967296), (-83267027/2147483648)), (143/8589934592), by norm_num⟩
  | 5 => ⟨((-479092117/4294967296), (180393031/8589934592)), (5/536870912), by norm_num⟩
  | 6 => ⟨((1729874005/34359738368), (-325675589/34359738368)), (147/34359738368), by norm_num⟩
  | 7 => ⟨((-669226521/34359738368), (251984527/68719476736)), (29/17179869184), by norm_num⟩
  | 8 => ⟨((906149507/137438953472), (-170596687/137438953472)), (5/8589934592), by norm_num⟩
  | 9 => ⟨((-1090621491/549755813888), (205326397/549755813888)), (49/274877906944), by norm_num⟩
  | 10 => ⟨((1181383099/2199023255552), (-55603419/549755813888)), (27/549755813888), by norm_num⟩
  | 11 => ⟨((-1163361723/8796093022208), (219020873/8796093022208)), (27/2199023255552), by norm_num⟩
  | 12 => ⟨((262536829/8796093022208), (-98853253/17592186044416)), (99/35184372088832), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171562799/10141204801825835211973625643008), (-242399545067/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778314504142475/633825300114114700748351602688), (-286727630913/633825300114114700748351602688)), (92229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118076934278821/2475880078570760549798248448), (-161251178175/19807040628566084398385987584)), (6485/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944487140223885/1237940039285380274899124224), (-342575966681/2475880078570760549798248448)), (55123/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770640743599263/154742504910672534362390528), (-342482872959/154742504910672534362390528)), (110249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549038079964755/9671406556917033397649408), (-160489408531/4835703278458516698824704)), (103361/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629168991582323/302231454903657293676544), (-280757628819/604462909807314587353088)), (22611/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887060081692427/75557863725914323419136), (-114011478641/18889465931478580854784)), (146975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648495426037365/2361183241434822606848), (-170936221541/2361183241434822606848)), (27559/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810347195116499/295147905179352825856), (-469811530887/590295810358705651712)), (151581/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227816670596479/9223372036854775808), (-586870075909/73786976294838206464)), (94743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455399802080627/2305843009213693952), (-82460884427/1152921504606846976)), (106593/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99553077397531/72057594037927936), (-659010556325/1152921504606846976)), (53301/288230376151711744), by norm_num⟩
  | 5 => ⟨((149198491267165/18014398509481984), (-575874087983/144115188075855872)), (93287/72057594037927936), by norm_num⟩
  | 4 => ⟨((745075785142367/18014398509481984), (-26946661537/1125899906842624)), (139951/18014398509481984), by norm_num⟩
  | 3 => ⟨((371851589958633/2251799813685248), (-537607635665/4503599627370496)), (349949/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224263291732395/4503599627370496), (-2142497908253/4503599627370496)), (175029/1125899906842624), by norm_num⟩
  | 1 => ⟨((138163812429909/140737488355328), (-3193988359927/2251799813685248)), (525365/1125899906842624), by norm_num⟩
  | 0 => ⟨((542486055171435/562949953421312), (-1577344918637/562949953421312)), (1051867/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542486055171435/562949953421312), (-1577344918637/562949953421312)), (4012554172996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522761624279285/562949953421312), (-12160052485741/2251799813685248)), (508289/281474976710656), by norm_num⟩
  | 2 => ⟨((242712937871781/281474976710656), (-22583921537373/2251799813685248)), (1898991/562949953421312), by norm_num⟩
  | 3 => ⟨((1674084186809237/2251799813685248), (-608558752835/35184372088832)), (6626103/1125899906842624), by norm_num⟩
  | 4 => ⟨((38872251757771/70368744177664), (-57910857825927/2251799813685248)), (20162941/2251799813685248), by norm_num⟩
  | 5 => ⟨((42853596677513/140737488355328), (-31990416643423/1125899906842624)), (46626843/4503599627370496), by norm_num⟩
  | 6 => ⟨((413920208784593/4503599627370496), (-311707574924833/18014398509481984)), (124178967/18014398509481984), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-79508701/33554432), (-317804085/8388608)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile043Terms1
