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
namespace Reinmann.XiRectangle.Tile041Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/16), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((11/16), (17907/1280))
  have he : value ((11/16), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15989985/33554432), (-650756047/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1346711956163337/2251799813685248), (375967259896019/2251799813685248)), (59121963/2251799813685248), by norm_num⟩
  | 1 => ⟨((445112989/1073741824), (-248528143/2147483648)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((-1234115253/8589934592), (344533163/8589934592)), (59/8589934592), by norm_num⟩
  | 3 => ⟨((570282339/17179869184), (-159208127/17179869184)), (57/34359738368), by norm_num⟩
  | 4 => ⟨((-790579191/137438953472), (441418657/274877906944)), (41/137438953472), by norm_num⟩
  | 5 => ⟨((219195095/274877906944), (-122387239/549755813888)), (47/1099511627776), by norm_num⟩
  | 6 => ⟨((-810317131/8796093022208), (452439305/17592186044416)), (89/17592186044416), by norm_num⟩
  | 7 => ⟨((1283814937/140737488355328), (-358408033/140737488355328)), (73/140737488355328), by norm_num⟩
  | 8 => ⟨((-13904261/17592186044416), (124214759/562949953421312)), (13/281474976710656), by norm_num⟩
  | 9 => ⟨((548278005/9007199254740992), (-306130169/18014398509481984)), (33/9007199254740992), by norm_num⟩
  | 10 => ⟨((-1216119531/288230376151711744), (169754611/144115188075855872)), (75/288230376151711744), by norm_num⟩
  | 11 => ⟨((1226108835/4611686018427387904), (-171148989/2305843009213693952)), (39/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-141645647/9223372036854775808), (316350505/73786976294838206464)), (37/36893488147419103232), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583355022258513/10141204801825835211973625643008), (1868824278705/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781225419100759/633825300114114700748351602688), (1108744721077/158456325028528675187087900672)), (23159/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473126169581737/9903520314283042199192993792), (2494553451249/19807040628566084398385987584)), (26061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892451339597125/2475880078570760549798248448), (5300664581657/2475880078570760549798248448)), (13849/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774116364271367/154742504910672534362390528), (5300370131691/154742504910672534362390528)), (6927/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552294946248497/9671406556917033397649408), (2484391948373/4835703278458516698824704)), (25985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157648276673495/75557863725914323419136), (2173686264237/302231454903657293676544)), (22747/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945842795955167/37778931862957161709568), (7063892175383/75557863725914323419136)), (18491/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300457479513249/4722366482869645213696), (5297403877607/4722366482869645213696)), (3469/590295810358705651712), by norm_num⟩
  | 9 => ⟨((812728466625867/295147905179352825856), (1820772982943/147573952589676412928)), (38185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914240220612063/36893488147419103232), (9102605369175/73786976294838206464)), (23885/36893488147419103232), by norm_num⟩
  | 7 => ⟨((14283447517853/72057594037927936), (5119348002615/4611686018427387904)), (26897/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599520833985283/1152921504606846976), (5118261237171/576460752303423488)), (13465/288230376151711744), by norm_num⟩
  | 5 => ⟨((599706897851323/72057594037927936), (4477252717089/72057594037927936)), (47203/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498866826237737/36028797018963968), (13426838432343/36028797018963968)), (35477/18014398509481984), by norm_num⟩
  | 3 => ⟨((749129636473683/4503599627370496), (16774901993225/9007199254740992)), (88955/9007199254740992), by norm_num⟩
  | 2 => ⟨((140365363564889/281474976710656), (16761859943361/2251799813685248)), (44675/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121343564264713/1125899906842624), (25109929810653/1125899906842624)), (135013/1125899906842624), by norm_num⟩
  | 0 => ⟨((558212353699125/562949953421312), (25043446455365/562949953421312)), (273989/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((558212353699125/562949953421312), (25043446455365/562949953421312)), (1045185093406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1104801077687349/1125899906842624), (12416344566357/140737488355328)), (567745/1125899906842624), by norm_num⟩
  | 2 => ⟨((1075334330083897/1125899906842624), (194938690723471/1125899906842624)), (1214389/1125899906842624), by norm_num⟩
  | 3 => ⟨((248321991484169/281474976710656), (186183749658891/562949953421312)), (2740219/1125899906842624), by norm_num⟩
  | 4 => ⟨((376571409044875/562949953421312), (657017828548387/1125899906842624)), (6647475/1125899906842624), by norm_num⟩
  | 5 => ⟨((240788149258955/2251799813685248), (6867121578715/8796093022208)), (16651583/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1346711956163337/2251799813685248), (375967259896019/2251799813685248)), (59121963/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15989985/33554432), (-650756047/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-50687053/67108864), (-257855983/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-997998766475503/2251799813685248), (-10981265758023/70368744177664)), (22753685/562949953421312), by norm_num⟩
  | 1 => ⟨((1045621595/2147483648), (368168747/2147483648)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((-574366367/2147483648), (-202237355/2147483648)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((420670633/4294967296), (296240591/8589934592)), (83/8589934592), by norm_num⟩
  | 4 => ⟨((-462153927/17179869184), (-162726777/17179869184)), (93/34359738368), by norm_num⟩
  | 5 => ⟨((406182387/68719476736), (286037819/137438953472)), (21/34359738368), by norm_num⟩
  | 6 => ⟨((-74372827/68719476736), (-104748221/274877906944)), (125/1099511627776), by norm_num⟩
  | 7 => ⟨((373517265/2199023255552), (526069407/8796093022208)), (5/274877906944), by norm_num⟩
  | 8 => ⟨((-820701315/35184372088832), (-144486579/17592186044416)), (45/17592186044416), by norm_num⟩
  | 9 => ⟨((200362789/70368744177664), (141097539/140737488355328)), (45/140737488355328), by norm_num⟩
  | 10 => ⟨((-704387271/2251799813685248), (-496036769/4503599627370496)), (161/4503599627370496), by norm_num⟩
  | 11 => ⟨((281399459/9007199254740992), (396328793/36028797018963968)), (131/36028797018963968), by norm_num⟩
  | 12 => ⟨((-824397077/288230376151711744), (-290274455/288230376151711744)), (49/144115188075855872), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582991909804931/10141204801825835211973625643008), (-456409665353/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445198784580505/158456325028528675187087900672), (-1082626375641/158456325028528675187087900672)), (46313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236502584593537/4951760157141521099596496896), (-4871460645585/39614081257132168796771975168)), (13029/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945968578354969/1237940039285380274899124224), (-5175524569995/2475880078570760549798248448)), (55389/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886801129426419/77371252455336267181195264), (-5175071671007/154742504910672534362390528)), (55407/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551813054794323/9671406556917033397649408), (-1212787072391/2417851639229258349412352)), (51963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260764640814565/604462909807314587353088), (-4244273130099/604462909807314587353088)), (45487/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891000691226145/75557863725914323419136), (-6896040322855/75557863725914323419136)), (36975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299943939559829/4722366482869645213696), (-5171239198147/4722366482869645213696)), (27747/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812375518195921/295147905179352825856), (-7109167571025/590295810358705651712)), (38177/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913799200761531/36893488147419103232), (-8884528435501/73786976294838206464)), (47759/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827289444087925/9223372036854775808), (-9992436828105/9223372036854775808)), (53781/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399632391902707/288230376151711744), (-4994555503997/576460752303423488)), (107693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299636770656997/36028797018963968), (-8736725444657/144115188075855872)), (47189/72057594037927936), by norm_num⟩
  | 4 => ⟨((1497568050880563/36028797018963968), (-1637197745379/4503599627370496)), (141859/36028797018963968), by norm_num⟩
  | 3 => ⟨((748319039118711/4503599627370496), (-16358812786027/9007199254740992)), (88919/4503599627370496), by norm_num⟩
  | 2 => ⟨((1121305144571915/2251799813685248), (-16339008300321/2251799813685248)), (178609/2251799813685248), by norm_num⟩
  | 1 => ⟨((1118925561648737/1125899906842624), (-12229400330837/562949953421312)), (269845/1125899906842624), by norm_num⟩
  | 0 => ⟨((1111623672031021/1125899906842624), (-12179388920375/281474976710656)), (273717/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1111623672031021/1125899906842624), (-12179388920375/281474976710656)), (1044147493602561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1095420454778085/1125899906842624), (-96199649382535/1125899906842624)), (1128361/1125899906842624), by norm_num⟩
  | 2 => ⟨((1057546583820205/1125899906842624), (-93595410245325/562949953421312)), (2388451/1125899906842624), by norm_num⟩
  | 3 => ⟨((120277607171129/140737488355328), (-351652951615457/1125899906842624)), (1320275/281474976710656), by norm_num⟩
  | 4 => ⟨((356252440870067/562949953421312), (-601061963933659/1125899906842624)), (6162803/562949953421312), by norm_num⟩
  | 5 => ⟨((130018415603437/1125899906842624), (-1521483680488147/2251799813685248)), (28760119/1125899906842624), by norm_num⟩
  | 6 => ⟨((-997998766475503/2251799813685248), (-10981265758023/70368744177664)), (22753685/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50687053/67108864), (-257855983/16777216)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-15989985/16777216), (-650756047/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((371321132144209/1125899906842624), (-449702145768731/2251799813685248)), (41516979/2251799813685248), by norm_num⟩
  | 1 => ⟨((-981827529/2147483648), (148634803/536870912)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((85068873/268435456), (-412103179/2147483648)), (21/1073741824), by norm_num⟩
  | 3 => ⟨((-628962661/4294967296), (380864209/4294967296)), (5/536870912), by norm_num⟩
  | 4 => ⟨((435963695/8589934592), (-527989905/17179869184)), (29/8589934592), by norm_num⟩
  | 5 => ⟨((-966998419/68719476736), (292779771/34359738368)), (67/68719476736), by norm_num⟩
  | 6 => ⟨((55856019/17179869184), (-541171927/274877906944)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((-353978899/549755813888), (428699195/1099511627776)), (13/274877906944), by norm_num⟩
  | 8 => ⟨((981437903/8796093022208), (-594303277/8796093022208)), (37/4398046511104), by norm_num⟩
  | 9 => ⟨((-604694147/35184372088832), (732337139/70368744177664)), (93/70368744177664), by norm_num⟩
  | 10 => ⟨((670627269/281474976710656), (-406093939/281474976710656)), (53/281474976710656), by norm_num⟩
  | 11 => ⟨((-42258491/140737488355328), (409429627/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | 12 => ⟨((1249764433/36028797018963968), (-189196661/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582734277411645/10141204801825835211973625643008), (-354626634533/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890249623679381/316912650057057350374175801344), (-210229499193/158456325028528675187087900672)), (23071/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891688405780091/39614081257132168796771975168), (-236487968201/9903520314283042199192993792)), (51913/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472896215443859/618970019642690137449562112), (-502488040293/1237940039285380274899124224)), (6895/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110828174976935/9671406556917033397649408), (-1004866087563/154742504910672534362390528)), (55163/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551484449516837/9671406556917033397649408), (-941945104707/9671406556917033397649408)), (51719/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260477998713113/604462909807314587353088), (-824085131337/604462909807314587353088)), (22629/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472634140355651/18889465931478580854784), (-669459654303/37778931862957161709568)), (73551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299597297385075/4722366482869645213696), (-1003997866695/4722366482869645213696)), (55169/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25379324486899/9223372036854775808), (-690092880415/295147905179352825856)), (75867/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827009109042251/73786976294838206464), (-215595670173/9223372036854775808)), (94849/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114164460034497/576460752303423488), (-1939719320623/9223372036854775808)), (106725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597877568343409/1152921504606846976), (-1938917472257/1152921504606846976)), (53375/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197983422756261/144115188075855872), (-847825553919/72057594037927936)), (93435/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496736226749121/36028797018963968), (-2541674298143/36028797018963968)), (140209/36028797018963968), by norm_num⟩
  | 3 => ⟨((747811091527095/4503599627370496), (-3173940978835/9007199254740992)), (685/35184372088832), by norm_num⟩
  | 2 => ⟨((2240650033758193/4503599627370496), (-6338435240451/4503599627370496)), (175509/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117544578557111/1125899906842624), (-74094276699/17592186044416)), (131819/562949953421312), by norm_num⟩
  | 0 => ⟨((2218434550454717/2251799813685248), (-18873980959257/2251799813685248)), (528775/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2218434550454717/2251799813685248), (-18873980959257/2251799813685248)), (2017116550925826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((546351367202599/562949953421312), (-2324290286051/140737488355328)), (2101489/2251799813685248), by norm_num⟩
  | 2 => ⟨((530088647179397/562949953421312), (-72184273878957/2251799813685248)), (4148467/2251799813685248), by norm_num⟩
  | 3 => ⟨((1994268311600455/2251799813685248), (-135941263892375/2251799813685248)), (8078583/2251799813685248), by norm_num⟩
  | 4 => ⟨((878991562075509/1125899906842624), (-240788149258967/2251799813685248)), (7642365/1125899906842624), by norm_num⟩
  | 5 => ⟨((336677989040825/562949953421312), (-375967259896033/2251799813685248)), (27134455/2251799813685248), by norm_num⟩
  | 6 => ⟨((371321132144209/1125899906842624), (-449702145768731/2251799813685248)), (41516979/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15989985/16777216), (-650756047/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-74255191/67108864), (-377752187/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1289104290755675/4503599627370496), (93256144701549/562949953421312)), (132068193/4503599627370496), by norm_num⟩
  | 1 => ⟨((247327485/536870912), (-572547817/2147483648)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((-398058231/1073741824), (230370041/1073741824)), (85/2147483648), by norm_num⟩
  | 3 => ⟨((854200011/4294967296), (-494355037/4294967296)), (93/4294967296), by norm_num⟩
  | 4 => ⟨((-687390941/8589934592), (397816869/8589934592)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((885050433/34359738368), (-512209241/34359738368)), (101/34359738368), by norm_num⟩
  | 6 => ⟨((-949622481/137438953472), (274789657/68719476736)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((873347671/549755813888), (-15794889/17179869184)), (103/549755813888), by norm_num⟩
  | 8 => ⟨((-351399713/1099511627776), (406734291/2199023255552)), (21/549755813888), by norm_num⟩
  | 9 => ⟨((502716463/8796093022208), (-581878745/17592186044416)), (61/8796093022208), by norm_num⟩
  | 10 => ⟨((-161818187/17592186044416), (374599085/70368744177664)), (159/140737488355328), by norm_num⟩
  | 11 => ⟨((378816473/281474976710656), (-438468341/562949953421312)), (95/562949953421312), by norm_num⟩
  | 12 => ⟨((-812908791/4503599627370496), (470458381/4503599627370496)), (13/562949953421312), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791267221101061/5070602400912917605986812821504), (3408877777757/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780254010301133/633825300114114700748351602688), (1010168849891/158456325028528675187087900672)), (46299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891412044873921/39614081257132168796771975168), (4545289065963/39614081257132168796771975168)), (52099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945645321437595/1237940039285380274899124224), (4828821654505/2475880078570760549798248448)), (27685/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886477961161211/77371252455336267181195264), (2414102512167/77371252455336267181195264)), (55387/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775603651363999/4835703278458516698824704), (1131446736727/2417851639229258349412352)), (25971/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630117398119081/302231454903657293676544), (3959408209589/604462909807314587353088)), (45467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890140047300117/75557863725914323419136), (6432809299769/75557863725914323419136)), (73917/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81206172877781/295147905179352825856), (2411765670201/2361183241434822606848)), (55467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623864425831675/590295810358705651712), (6630607268303/590295810358705651712)), (38157/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913245446604477/36893488147419103232), (1035704483331/9223372036854775808)), (95463/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913022267885941/4611686018427387904), (9317732237815/9223372036854775808)), (107493/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597285958317411/1152921504606846976), (9313220322289/1152921504606846976)), (107615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197460387062805/144115188075855872), (1017998680367/18014398509481984)), (23575/36028797018963968), by norm_num⟩
  | 4 => ⟨((747970467784627/18014398509481984), (12205821421917/36028797018963968)), (141723/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494609314661889/9007199254740992), (15239478390681/9007199254740992)), (177633/9007199254740992), by norm_num⟩
  | 2 => ⟨((279821022439885/562949953421312), (15212753779359/2251799813685248)), (89177/1125899906842624), by norm_num⟩
  | 1 => ⟨((557956648091125/562949953421312), (11376112588229/562949953421312)), (269335/1125899906842624), by norm_num⟩
  | 0 => ⟨((1105676674230069/1125899906842624), (45236269752151/1125899906842624)), (545903/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1105676674230069/1125899906842624), (45236269752151/1125899906842624)), (2082454685691451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1083999190707787/1125899906842624), (88847486335433/1125899906842624)), (1116063/1125899906842624), by norm_num⟩
  | 2 => ⟨((518323326315967/562949953421312), (10692624928147/70368744177664)), (145325/70368744177664), by norm_num⟩
  | 3 => ⟨((464236308098603/562949953421312), (315039694658377/1125899906842624)), (4988385/1125899906842624), by norm_num⟩
  | 4 => ⟨((42344538421093/70368744177664), (259797276585367/562949953421312)), (1377369/140737488355328), by norm_num⟩
  | 5 => ⟨((335811100604625/2251799813685248), (1250668419750627/2251799813685248)), (46863373/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1289104290755675/4503599627370496), (93256144701549/562949953421312)), (132068193/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-74255191/67108864), (-377752187/16777216)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-82667023/67108864), (-841089989/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1311068546438737/4503599627370496), (87059622505781/4503599627370496)), (42597993/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1120147459/2147483648), (-37190891/1073741824)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((2007034817/4294967296), (66637131/2147483648)), (35/2147483648), by norm_num⟩
  | 3 => ⟨((-149838485/536870912), (-39799237/2147483648)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((536949049/4294967296), (17827665/2147483648)), (41/8589934592), by norm_num⟩
  | 5 => ⟨((-1539333669/34359738368), (-12777155/4294967296)), (61/34359738368), by norm_num⟩
  | 6 => ⟨((1838743785/137438953472), (61049569/68719476736)), (75/137438953472), by norm_num⟩
  | 7 => ⟨((-470655227/137438953472), (-125012735/549755813888)), (79/549755813888), by norm_num⟩
  | 8 => ⟨((26353155/34359738368), (13999547/274877906944)), (73/2199023255552), by norm_num⟩
  | 9 => ⟨((-1343104427/8796093022208), (-89186919/8796093022208)), (15/2199023255552), by norm_num⟩
  | 10 => ⟨((1925216061/70368744177664), (127841205/70368744177664)), (11/8796093022208), by norm_num⟩
  | 11 => ⟨((-1254372403/281474976710656), (-20823699/70368744177664)), (59/281474976710656), by norm_num⟩
  | 12 => ⟨((749177877/1125899906842624), (3109255/70368744177664)), (9/281474976710656), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791185582479031/5070602400912917605986812821504), (86371253997/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111254324851795/39614081257132168796771975168), (25589515297/158456325028528675187087900672)), (23053/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891204669198661/39614081257132168796771975168), (115140205759/39614081257132168796771975168)), (51869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891070976453927/2475880078570760549798248448), (30580272993/618970019642690137449562112)), (55111/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886368504842029/77371252455336267181195264), (122303796733/154742504910672534362390528)), (6889/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551002872756079/9671406556917033397649408), (57320718353/4835703278458516698824704)), (12917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260056720338221/604462909807314587353088), (12536611035/75557863725914323419136)), (22605/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236231521741659/9444732965739290427392), (81470755077/37778931862957161709568)), (73467/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299084172853893/4722366482869645213696), (122176011747/4722366482869645213696)), (55101/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811785745363151/295147905179352825856), (83971542619/295147905179352825856)), (75765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114132994876621/4611686018427387904), (209855487289/73786976294838206464)), (94707/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456410144154057/2305843009213693952), (235986584509/9223372036854775808)), (26637/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596887478952931/1152921504606846976), (235860602171/1152921504606846976)), (106551/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197117875350847/144115188075855872), (103118193751/72057594037927936)), (23309/36028797018963968), by norm_num⟩
  | 4 => ⟨((186929933235511/4503599627370496), (309071529133/36028797018963968)), (34965/9007199254740992), by norm_num⟩
  | 3 => ⟨((1494003959297221/9007199254740992), (385844579787/9007199254740992)), (87419/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237421755825937/4503599627370496), (770206700843/4503599627370496)), (174857/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115133560429603/1125899906842624), (143951377651/281474976710656)), (524667/2251799813685248), by norm_num⟩
  | 0 => ⟨((138054483820115/140737488355328), (572117136197/562949953421312)), (8201/17592186044416), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((138054483820115/140737488355328), (572117136197/562949953421312)), (31284332342499489/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((2166759719041499/2251799813685248), (561210355857/281474976710656)), (2061567/2251799813685248), by norm_num⟩
  | 2 => ⟨((260615280623307/281474976710656), (8640256460381/2251799813685248)), (993911/562949953421312), by norm_num⟩
  | 3 => ⟨((1930378574147645/2251799813685248), (15999879551597/2251799813685248)), (1848135/562949953421312), by norm_num⟩
  | 4 => ⟨((1654723222169809/2251799813685248), (6858030737821/562949953421312)), (3194929/562949953421312), by norm_num⟩
  | 5 => ⟨((607815224955215/1125899906842624), (20158350935565/1125899906842624)), (4773397/562949953421312), by norm_num⟩
  | 6 => ⟨((1311068546438737/4503599627370496), (87059622505781/4503599627370496)), (42597993/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-82667023/67108864), (-841089989/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-44889563/33554432), (-1826903191/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-586654644905685/4503599627370496), (-1025942291763735/4503599627370496)), (52250325/2251799813685248), by norm_num⟩
  | 1 => ⟨((544346441/2147483648), (475976829/1073741824)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((-66203079/268435456), (-463104071/1073741824)), (97/2147483648), by norm_num⟩
  | 3 => ⟨((171766991/1073741824), (146673/524288)), (1/33554432), by norm_num⟩
  | 4 => ⟨((-334243131/4294967296), (-1169049515/8589934592)), (63/4294967296), by norm_num⟩
  | 5 => ⟨((520325681/17179869184), (454973063/8589934592)), (25/4294967296), by norm_num⟩
  | 6 => ⟨((-337502341/34359738368), (-1180448935/68719476736)), (33/17179869184), by norm_num⟩
  | 7 => ⟨((750570549/274877906944), (82037413/17179869184)), (149/274877906944), by norm_num⟩
  | 8 => ⟨((-730271425/1099511627776), (-1277099477/1099511627776)), (147/1099511627776), by norm_num⟩
  | 9 => ⟨((631574479/4398046511104), (276124537/1099511627776)), (129/4398046511104), by norm_num⟩
  | 10 => ⟨((-491594875/17592186044416), (-429850831/8796093022208)), (51/8796093022208), by norm_num⟩
  | 11 => ⟨((86963587/17592186044416), (608328069/70368744177664)), (73/70368744177664), by norm_num⟩
  | 12 => ⟨((-112815551/140737488355328), (-394583921/281474976710656)), (3/17592186044416), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582233116007809/10141204801825835211973625643008), (-2722767988223/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((13905469208375/4951760157141521099596496896), (-3226172620717/633825300114114700748351602688)), (46259/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891014083618813/39614081257132168796771975168), (-1814501073735/19807040628566084398385987584)), (13013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890868095511491/2475880078570760549798248448), (-3855287122013/2475880078570760549798248448)), (55317/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886266848601387/77371252455336267181195264), (-481836686531/19342813113834066795298816)), (27665/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550811808989959/9671406556917033397649408), (-1806572221179/4835703278458516698824704)), (25943/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629944540723687/302231454903657293676544), (-3160870708513/604462909807314587353088)), (22707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889578902272759/75557863725914323419136), (-5135232438829/75557863725914323419136)), (2307/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1298878468419517/4722366482869645213696), (-481298716793/590295810358705651712)), (1731/147573952589676412928), by norm_num⟩
  | 9 => ⟨((405821857033241/147573952589676412928), (-5292604780833/590295810358705651712)), (76201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456442753204577/18446744073709551616), (-6613234517877/73786976294838206464)), (95307/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456309137165421/2305843009213693952), (-7436422149925/9223372036854775808)), (53649/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596480317724985/1152921504606846976), (-7432089281885/1152921504606846976)), (107395/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196758089458043/144115188075855872), (-1624551078869/36028797018963968)), (735/1125899906842624), by norm_num⟩
  | 4 => ⟨((1494892760185027/36028797018963968), (-2434390136489/9007199254740992)), (141339/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493308308892567/9007199254740992), (-759681195397/562949953421312)), (5533/281474976710656), by norm_num⟩
  | 2 => ⟨((1117996882474909/2251799813685248), (-12129329488207/2251799813685248)), (177631/2251799813685248), by norm_num⟩
  | 1 => ⟨((557008452638133/562949953421312), (-9065048677413/562949953421312)), (133943/562949953421312), by norm_num⟩
  | 0 => ⟨((275505278407499/281474976710656), (-36004772755875/1125899906842624)), (541547/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((275505278407499/281474976710656), (-36004772755875/1125899906842624)), (2065837864402389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((134687171551861/140737488355328), (-70482321789499/1125899906842624)), (136845/140737488355328), by norm_num⟩
  | 2 => ⟨((513381705980431/562949953421312), (-16863070169101/140737488355328)), (2232459/1125899906842624), by norm_num⟩
  | 3 => ⟨((920191801394769/1125899906842624), (-246052187875443/1125899906842624)), (2303381/562949953421312), by norm_num⟩
  | 4 => ⟨((349147942644671/562949953421312), (-402194199719169/1125899906842624)), (4771835/562949953421312), by norm_num⟩
  | 5 => ⟨((144709563942539/562949953421312), (-249445401890767/562949953421312)), (18656569/1125899906842624), by norm_num⟩
  | 6 => ⟨((-586654644905685/4503599627370496), (-1025942291763735/4503599627370496)), (52250325/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-44889563/33554432), (-1826903191/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-47969955/33554432), (-1952268141/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-92265299062629/562949953421312), (392942759933211/2251799813685248)), (72766651/2251799813685248), by norm_num⟩
  | 1 => ⟨((365944473/1073741824), (-779248713/2147483648)), (147/2147483648), by norm_num⟩
  | 2 => ⟨((-760960139/2147483648), (810201073/2147483648)), (155/2147483648), by norm_num⟩
  | 3 => ⟨((527457375/2147483648), (-561588589/2147483648)), (109/2147483648), by norm_num⟩
  | 4 => ⟨((-548408389/4294967296), (583895321/4294967296)), (29/1073741824), by norm_num⟩
  | 5 => ⟨((912306549/17179869184), (-971340949/17179869184)), (49/4294967296), by norm_num⟩
  | 6 => ⟨((-79045339/4294967296), (10520035/536870912)), (69/17179869184), by norm_num⟩
  | 7 => ⟨((751406453/137438953472), (-800029177/137438953472)), (83/68719476736), by norm_num⟩
  | 8 => ⟨((-781252897/549755813888), (831806953/549755813888)), (175/549755813888), by norm_num⟩
  | 9 => ⟨((722030991/2199023255552), (-768752859/2199023255552)), (41/549755813888), by norm_num⟩
  | 10 => ⟨((-600568495/8796093022208), (159857663/2199023255552)), (69/4398046511104), by norm_num⟩
  | 11 => ⟨((227063105/17592186044416), (-967024481/70368744177664)), (211/70368744177664), by norm_num⟩
  | 12 => ⟨((-157388151/70368744177664), (670290293/281474976710656)), (149/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197764191570597/1267650600228229401496703205376), (3028395288345/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779757058766041/633825300114114700748351602688), (3587763462425/633825300114114700748351602688)), (69415/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890853152922813/39614081257132168796771975168), (4035707496777/39614081257132168796771975168)), (78109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890697033616253/2475880078570760549798248448), (4287311942299/2475880078570760549798248448)), (41505/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772362553206995/154742504910672534362390528), (2143303112773/77371252455336267181195264)), (10379/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775325637160439/4835703278458516698824704), (1004485883317/2417851639229258349412352)), (38933/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629874263252487/302231454903657293676544), (1757475405913/302231454903657293676544)), (68157/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236168792163277/9444732965739290427392), (1427597320507/18889465931478580854784)), (55399/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324676725511991/1180591620717411303424), (4281561947847/4722366482869645213696)), (41569/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623051292834361/590295810358705651712), (5885149000483/590295810358705651712)), (14297/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1825475496848701/73786976294838206464), (7353438400007/73786976294838206464)), (143065/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824903617029687/9223372036854775808), (8268496427039/9223372036854775808)), (161077/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798073396003007/576460752303423488), (8263344621151/1152921504606846976)), (161239/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299116396911561/36028797018963968), (1806157832703/36028797018963968)), (141267/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494452677699575/36028797018963968), (10825358007337/36028797018963968)), (212265/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492755887341907/9007199254740992), (6755710024869/4503599627370496)), (132985/4503599627370496), by norm_num⟩
  | 2 => ⟨((558720500269593/1125899906842624), (13481010500027/2251799813685248)), (266931/2251799813685248), by norm_num⟩
  | 1 => ⟨((278293622951993/281474976710656), (20145515550341/1125899906842624)), (25175/70368744177664), by norm_num⟩
  | 0 => ⟨((1100302286144075/1125899906842624), (39987175831961/1125899906842624)), (815245/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1100302286144075/1125899906842624), (39987175831961/1125899906842624)), (3109912876609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((268466614863985/281474976710656), (78156114441355/1125899906842624)), (825665/562949953421312), by norm_num⟩
  | 2 => ⟨((1018812407345019/1125899906842624), (74544130779205/562949953421312)), (422411/140737488355328), by norm_num⟩
  | 3 => ⟨((225542120896459/281474976710656), (269816117297963/1125899906842624)), (1752675/281474976710656), by norm_num⟩
  | 4 => ⟨((1316470906725831/2251799813685248), (432400066667287/1125899906842624)), (29190633/2251799813685248), by norm_num⟩
  | 5 => ⟨((1709077979209/8796093022208), (1011177111525173/2251799813685248)), (220909/8796093022208), by norm_num⟩
  | 6 => ⟨((-92265299062629/562949953421312), (392942759933211/2251799813685248)), (72766651/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47969955/33554432), (-1952268141/67108864)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile041Terms0
