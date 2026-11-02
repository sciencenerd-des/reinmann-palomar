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
namespace Reinmann.XiRectangle.Tile010Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2961/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2961/640))
  have he : value ((3/4), (2961/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-17862266831/34359738368), (-110187858513/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-668037439958877/1125899906842624), (21841168749161/562949953421312)), (210051/2251799813685248), by norm_num⟩
  | 1 => ⟨((56524446779/137438953472), (-7392160419/274877906944)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((-78359521835/549755813888), (5123855153/549755813888)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((36209787753/1099511627776), (-4735447671/2199023255552)), (17/2199023255552), by norm_num⟩
  | 4 => ⟨((-50197424579/8796093022208), (1641181101/4398046511104)), (13/8796093022208), by norm_num⟩
  | 5 => ⟨((55670725309/70368744177664), (-7280512339/140737488355328)), (31/140737488355328), by norm_num⟩
  | 6 => ⟨((-25725337525/281474976710656), (3364311067/562949953421312)), (31/1125899906842624), by norm_num⟩
  | 7 => ⟨((20378794485/2251799813685248), (-5330200527/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 8 => ⟨((-28251007881/36028797018963968), (3694613467/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 9 => ⟨((8703158427/144115188075855872), (-4552730503/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-9652111561/2305843009213693952), (5049139699/18446744073709551616)), (29/18446744073709551616), by norm_num⟩
  | 11 => ⟨((77851158283/295147905179352825856), (-5090613741/295147905179352825856)), (31/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-71949747823/4722366482869645213696), (4704726083/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (500902466587/1267650600228229401496703205376)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890578448287809/316912650057057350374175801344), (4754504692743/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473106874941365/9903520314283042199192993792), (5348530415569/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236546153220445/309485009821345068724781056), (2841253763831/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887017062441421/77371252455336267181195264), (2841081454465/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388054428363563/2417851639229258349412352), (5326661264421/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261118501364421/604462909807314587353088), (4660461800539/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945787654981901/37778931862957161709568), (3786280968023/37778931862957161709568)), (73/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650187274733241/2361183241434822606848), (177463071713/147573952589676412928)), (55/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50791954668417/18446744073709551616), (7807393659337/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914168464548307/36893488147419103232), (9757767441597/73786976294838206464)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828119099673529/9223372036854775808), (10975456872917/9223372036854775808)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599357737704983/1152921504606846976), (5486455842317/576460752303423488)), (53/288230376151711744), by norm_num⟩
  | 5 => ⟨((599635029749307/72057594037927936), (2399606599619/36028797018963968)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((374662292578971/9007199254740992), (14391876993967/36028797018963968)), (139/18014398509481984), by norm_num⟩
  | 3 => ⟨((93623976119477/562949953421312), (17979716845765/9007199254740992)), (349/9007199254740992), by norm_num⟩
  | 2 => ⟨((140330235776251/281474976710656), (8982216601835/1125899906842624)), (175/1125899906842624), by norm_num⟩
  | 1 => ⟨((35028395290095/35184372088832), (26908127886393/1125899906842624)), (265/562949953421312), by norm_num⟩
  | 0 => ⟨((69718848295293/70368744177664), (13415074008229/281474976710656)), (537/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((69718848295293/70368744177664), (13415074008229/281474976710656)), (2048494579124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1102641827959971/1125899906842624), (53164712292633/562949953421312)), (279/140737488355328), by norm_num⟩
  | 2 => ⟨((1069822501017967/1125899906842624), (104132943237749/562949953421312)), (4795/1125899906842624), by norm_num⟩
  | 3 => ⟨((978013673793499/1125899906842624), (6184151289555/17592186044416)), (10887/1125899906842624), by norm_num⟩
  | 4 => ⟨((355211166982501/562949953421312), (343799486131075/562949953421312)), (26569/1125899906842624), by norm_num⟩
  | 5 => ⟨((28339593729779/1125899906842624), (1735449710005857/2251799813685248)), (131963/2251799813685248), by norm_num⟩
  | 6 => ⟨((-668037439958877/1125899906842624), (21841168749161/562949953421312)), (210051/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-110187858513/34359738368)), (1/17179869184), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-55294967/67108864), (-87321811889/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((357597081489085/2251799813685248), (230212159539939/562949953421312)), (66565/562949953421312), by norm_num⟩
  | 1 => ⟨((-23978304939/137438953472), (-61746559441/137438953472)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((26342860467/274877906944), (67835528985/274877906944)), (3/34359738368), by norm_num⟩
  | 3 => ⟨((-9646863409/274877906944), (-49683297167/549755813888)), (5/137438953472), by norm_num⟩
  | 4 => ⟨((41399073/4294967296), (54582680809/2199023255552)), (3/274877906944), by norm_num⟩
  | 5 => ⟨((-9314617413/4398046511104), (-11993040777/2199023255552)), (45/17592186044416), by norm_num⟩
  | 6 => ⟨((27288408411/70368744177664), (70270410539/70368744177664)), (35/70368744177664), by norm_num⟩
  | 7 => ⟨((-34262149507/562949953421312), (-2757140591/17592186044416)), (23/281474976710656), by norm_num⟩
  | 8 => ⟨((37640818485/4503599627370496), (96928913115/4503599627370496)), (27/2251799813685248), by norm_num⟩
  | 9 => ⟨((-36757925105/36028797018963968), (-11831921675/4503599627370496)), (55/36028797018963968), by norm_num⟩
  | 10 => ⟨((32306166581/288230376151711744), (83191645125/288230376151711744)), (51/288230376151711744), by norm_num⟩
  | 11 => ⟨((-3226541055/288230376151711744), (-66469355381/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | 12 => ⟨((37810321631/36893488147419103232), (97365400855/36893488147419103232)), (33/18446744073709551616), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (195454743579/1267650600228229401496703205376)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((890348613113977/316912650057057350374175801344), (1854303708729/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945955513263585/19807040628566084398385987584), (1042967644285/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945910633535427/1237940039285380274899124224), (2216119598077/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886743529777141/77371252455336267181195264), (69247175775/4835703278458516698824704)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((3030675368695/18889465931478580854784), (2077192184977/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260671516177201/604462909807314587353088), (454330020739/151115727451828646838272)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945425368957347/37778931862957161709568), (2952726881801/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299832676623477/4722366482869645213696), (2214179209921/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406150000608155/147573952589676412928), (1521950889999/295147905179352825856)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456853134157699/18446744073709551616), (1901992670049/36893488147419103232)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827084369343471/9223372036854775808), (4278257272529/9223372036854775808)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598329518741263/1152921504606846976), (2138362319429/576460752303423488)), (419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299594422393325/36028797018963968), (3740410066691/144115188075855872)), (367/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497325249691137/36028797018963968), (1401791916951/9007199254740992)), (275/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496354306610067/9007199254740992), (3501463911931/4503599627370496)), (689/9007199254740992), by norm_num⟩
  | 2 => ⟨((280262729498939/562949953421312), (6993882680149/2251799813685248)), (345/1125899906842624), by norm_num⟩
  | 1 => ⟨((559308954979503/562949953421312), (10468219932299/1125899906842624)), (519/562949953421312), by norm_num⟩
  | 0 => ⟨((555651035838517/562949953421312), (10423038188927/562949953421312)), (261/140737488355328), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555651035838517/562949953421312), (10423038188927/562949953421312)), (995636523199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((34265860582675/35184372088832), (41151593892591/1125899906842624)), (525/140737488355328), by norm_num⟩
  | 2 => ⟨((1066378388815831/1125899906842624), (80154608160591/1125899906842624)), (8489/1125899906842624), by norm_num⟩
  | 3 => ⟨((251074296225633/281474976710656), (151834352924239/1125899906842624)), (8645/562949953421312), by norm_num⟩
  | 4 => ⟨((875352381579855/1125899906842624), (270870993569813/1125899906842624)), (35509/1125899906842624), by norm_num⟩
  | 5 => ⟨((1230785601045217/2251799813685248), (842375304878251/2251799813685248)), (144601/2251799813685248), by norm_num⟩
  | 6 => ⟨((357597081489085/2251799813685248), (230212159539939/562949953421312)), (66565/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-87321811889/17179869184)), (1/8589934592), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-17862266831/17179869184), (-110187858513/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((789352360501815/2251799813685248), (-51836645045365/1125899906842624)), (106821/2251799813685248), by norm_num⟩
  | 1 => ⟨((-16697307225/34359738368), (2193019065/34359738368)), (11/137438953472), by norm_num⟩
  | 2 => ⟨((92589531407/274877906944), (-12160679855/274877906944)), (9/137438953472), by norm_num⟩
  | 3 => ⟨((-85570896859/549755813888), (11238854607/549755813888)), (19/549755813888), by norm_num⟩
  | 4 => ⟨((118626451791/2199023255552), (-15580360767/2199023255552)), (29/2199023255552), by norm_num⟩
  | 5 => ⟨((-65780472479/4398046511104), (4319793255/2199023255552)), (9/2199023255552), by norm_num⟩
  | 6 => ⟨((60794065379/17592186044416), (-3992336687/8796093022208)), (9/8796093022208), by norm_num⟩
  | 7 => ⟨((-1504972679/2199023255552), (6325204385/70368744177664)), (15/70368744177664), by norm_num⟩
  | 8 => ⟨((66762724433/562949953421312), (-2192148793/140737488355328)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((-82269145257/4503599627370496), (10805203593/4503599627370496)), (29/4503599627370496), by norm_num⟩
  | 10 => ⟨((91239401731/36028797018963968), (-11983354249/36028797018963968)), (17/18014398509481984), by norm_num⟩
  | 11 => ⟨((-45994424775/144115188075855872), (12081786489/288230376151711744)), (9/72057594037927936), by norm_num⟩
  | 12 => ⟨((85015748945/2305843009213693952), (-11165941655/2305843009213693952)), (9/576460752303423488), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (-85055459247/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780365797981423/633825300114114700748351602688), (-201661270681/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891538309864977/39614081257132168796771975168), (-113423931279/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945712713692779/1237940039285380274899124224), (-60250070047/618970019642690137449562112)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886545706531891/77371252455336267181195264), (-3765179913/2417851639229258349412352)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551335075409647/9671406556917033397649408), (-225880236003/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157543418394409/75557863725914323419136), (-197614653169/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472581086958975/18889465931478580854784), (-321066535461/75557863725914323419136)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1299438220461623/4722366482869645213696), (-240749796711/4722366482869645213696)), (27/590295810358705651712), by norm_num⟩
  | 9 => ⟨((812029085822939/295147905179352825856), (-330949571709/590295810358705651712)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28542751053659/1152921504606846976), (-413564904397/73786976294838206464)), (371/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913162233710291/4611686018427387904), (-465092746203/9223372036854775808)), (417/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798785511664361/576460752303423488), (-464883124489/1152921504606846976)), (417/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197715587182985/144115188075855872), (-406537036405/144115188075855872)), (365/144115188075855872), by norm_num⟩
  | 4 => ⟨((748167627613591/18014398509481984), (-19041702395/1125899906842624)), (547/36028797018963968), by norm_num⟩
  | 3 => ⟨((373780583772409/2251799813685248), (-760844422277/9007199254740992)), (171/2251799813685248), by norm_num⟩
  | 2 => ⟨((559913607509023/1125899906842624), (-1519220673115/4503599627370496)), (171/562949953421312), by norm_num⟩
  | 1 => ⟨((279200744651291/281474976710656), (-568167635399/562949953421312)), (513/562949953421312), by norm_num⟩
  | 0 => ⟨((1107754412306411/1125899906842624), (-141273715081/70368744177664)), (2053/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1107754412306411/1125899906842624), (-141273715081/70368744177664)), (7831577781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((136237102562509/140737488355328), (-4447900358397/1125899906842624)), (8097/2251799813685248), by norm_num⟩
  | 2 => ⟨((1055027439206107/1125899906842624), (-538208639713/70368744177664)), (15741/2251799813685248), by norm_num⟩
  | 3 => ⟨((1977100691752993/2251799813685248), (-32277107659127/2251799813685248)), (14871/1125899906842624), by norm_num⟩
  | 4 => ⟨((1735449710005865/2251799813685248), (-28339593729785/1125899906842624)), (53081/2251799813685248), by norm_num⟩
  | 5 => ⟨((1336074879917765/2251799813685248), (-87364674996663/2251799813685248)), (21123/562949953421312), by norm_num⟩
  | 6 => ⟨((789352360501815/2251799813685248), (-51836645045365/1125899906842624)), (106821/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-110187858513/17179869184)), (1/8589934592), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-5184362399/4294967296), (-15990517775/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((133546168928769/1125899906842624), (-1236430587293837/4503599627370496)), (358989/2251799813685248), by norm_num⟩
  | 1 => ⟨((-26237093181/137438953472), (30364353383/68719476736)), (37/137438953472), by norm_num⟩
  | 2 => ⟨((21113486239/137438953472), (-48869541521/137438953472)), (31/137438953472), by norm_num⟩
  | 3 => ⟨((-22653896811/274877906944), (26217497629/137438953472)), (35/274877906944), by norm_num⟩
  | 4 => ⟨((4557505049/137438953472), (-84390869307/1099511627776)), (29/549755813888), by norm_num⟩
  | 5 => ⟨((-11736034259/1099511627776), (54328745811/2199023255552)), (39/2199023255552), by norm_num⟩
  | 6 => ⟨((25184557971/8796093022208), (-7286561937/1099511627776)), (11/2199023255552), by norm_num⟩
  | 7 => ⟨((-2895213029/4398046511104), (53610372721/35184372088832)), (21/17592186044416), by norm_num⟩
  | 8 => ⟨((9319331227/70368744177664), (-86282566357/281474976710656)), (35/140737488355328), by norm_num⟩
  | 9 => ⟨((-6666171109/281474976710656), (61718414879/1125899906842624)), (13/281474976710656), by norm_num⟩
  | 10 => ⟨((8583030811/2251799813685248), (-39732782721/4503599627370496)), (69/9007199254740992), by norm_num⟩
  | 11 => ⟨((-40185760555/72057594037927936), (46507234093/36028797018963968)), (83/72057594037927936), by norm_num⟩
  | 12 => ⟨((21558828859/288230376151711744), (-3118771073/18014398509481984)), (23/144115188075855872), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791201706336853/5070602400912917605986812821504), (-1514911016867/10141204801825835211973625643008)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780105700059297/633825300114114700748351602688), (-1795385316087/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236405703581403/4951760157141521099596496896), (-1009794810939/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236389295456883/309485009821345068724781056), (-2145549444179/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((221597531025103/19342813113834066795298816), (-536312970927/38685626227668133590597632)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551043250945633/9671406556917033397649408), (-2010857523427/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630045946699275/302231454903657293676544), (-1759184260945/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889909034313957/75557863725914323419136), (-714520471403/18889465931478580854784)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299126559414073/4722366482869645213696), (-1071521519881/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202953669009267/73786976294838206464), (-2945842002453/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913099807450173/36893488147419103232), (-460129944303/9223372036854775808)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825720370338671/9223372036854775808), (-2069716729875/4611686018427387904)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596966192190133/1152921504606846976), (-4137264184097/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149648191923377/18014398509481984), (-3617666788875/144115188075855872)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((186942316448889/4503599627370496), (-2710812047969/18014398509481984)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((93382722327617/562949953421312), (-1692125736203/2251799813685248)), (43/281474976710656), by norm_num⟩
  | 2 => ⟨((1118824141388661/2251799813685248), (-844465517039/281474976710656)), (2757/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230575356444013/2251799813685248), (-10101681016359/1125899906842624)), (4147/2251799813685248), by norm_num⟩
  | 0 => ⟨((138085168520897/140737488355328), (-20075992227031/1125899906842624)), (8343/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((138085168520897/140737488355328), (-20075992227031/1125899906842624)), (31826027877043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((8464880432189/8796093022208), (-39395285538913/1125899906842624)), (8335/1125899906842624), by norm_num⟩
  | 2 => ⟨((1041327412084145/1125899906842624), (-151647501151657/2251799813685248)), (8313/562949953421312), by norm_num⟩
  | 3 => ⟨((479000633826877/562949953421312), (-280512857250561/2251799813685248)), (16497/562949953421312), by norm_num⟩
  | 4 => ⟨((199417052438973/281474976710656), (-29835209063213/140737488355328)), (128737/2251799813685248), by norm_num⟩
  | 5 => ⟨((257263380405459/562949953421312), (-169099207888805/562949953421312)), (59249/562949953421312), by norm_num⟩
  | 6 => ⟨((133546168928769/1125899906842624), (-1236430587293837/4503599627370496)), (358989/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/4294967296), (-15990517775/2147483648)), (1/4294967296), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-71207870573/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-247902196425065/2251799813685248), (-133124775735965/562949953421312)), (401941/4503599627370496), by norm_num⟩
  | 1 => ⟨((27110663323/137438953472), (29117135927/68719476736)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((-24287893863/137438953472), (-26085452007/68719476736)), (11/68719476736), by norm_num⟩
  | 3 => ⟨((1813252659/17179869184), (31159237095/137438953472)), (7/68719476736), by norm_num⟩
  | 4 => ⟨((-25991300975/549755813888), (-55829858119/549755813888)), (27/549755813888), by norm_num⟩
  | 5 => ⟨((1164253991/68719476736), (10003367695/274877906944)), (41/2199023255552), by norm_num⟩
  | 6 => ⟨((-695354371/137438953472), (-11949085861/1099511627776)), (13/2199023255552), by norm_num⟩
  | 7 => ⟨((5695578417/4398046511104), (48936886263/17592186044416)), (7/4398046511104), by norm_num⟩
  | 8 => ⟨((-20410213123/70368744177664), (-21920782339/35184372088832)), (13/35184372088832), by norm_num⟩
  | 9 => ⟨((32506837895/562949953421312), (4364085481/35184372088832)), (43/562949953421312), by norm_num⟩
  | 10 => ⟨((-23297773845/2251799813685248), (-50044105505/2251799813685248)), (1/70368744177664), by norm_num⟩
  | 11 => ⟨((1897454859/1125899906842624), (8151545447/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 12 => ⟨((-18132174459/72057594037927936), (-77896579965/144115188075855872)), (27/72057594037927936), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-2613692702595/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779891224574241/633825300114114700748351602688), (-387112507737/79228162514264337593543950336)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891004172152701/39614081257132168796771975168), (-3483587286709/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890857598280025/2475880078570760549798248448), (-115650087889/77371252455336267181195264)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443130809467937/38685626227668133590597632), (-3700230547575/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775401021810469/4835703278458516698824704), (-3468358139861/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629940288492991/302231454903657293676544), (-758551352723/151115727451828646838272)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944782578964825/37778931862957161709568), (-4929443943649/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298868226106219/4722366482869645213696), (-3696085668663/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202909181505283/73786976294838206464), (-5080497347745/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825753703219373/73786976294838206464), (-6348191274293/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456304323968535/2305843009213693952), (-7138373792057/9223372036854775808)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596461340282403/1152921504606846976), (-7134197688359/1152921504606846976)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196741793554521/144115188075855872), (-3118862868641/72057594037927936)), (23/9007199254740992), by norm_num⟩
  | 4 => ⟨((1494868934036527/36028797018963968), (-9347196325027/36028797018963968)), (553/36028797018963968), by norm_num⟩
  | 3 => ⟨((746639802460117/4503599627370496), (-2916890970923/2251799813685248)), (693/9007199254740992), by norm_num⟩
  | 2 => ⟨((279492448006643/562949953421312), (-11642926589783/2251799813685248)), (695/2251799813685248), by norm_num⟩
  | 1 => ⟨((556990143754237/562949953421312), (-8701415924199/562949953421312)), (523/562949953421312), by norm_num⟩
  | 0 => ⟨((1101963854326605/1125899906842624), (-1079988893925/35184372088832)), (1057/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101963854326605/1125899906842624), (-1079988893925/35184372088832)), (4032137157249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1077475857164851/1125899906842624), (-33824924349219/562949953421312)), (4269/1125899906842624), by norm_num⟩
  | 2 => ⟨((64191858536689/70368744177664), (-129480566203849/1125899906842624)), (8685/1125899906842624), by norm_num⟩
  | 3 => ⟨((461012129266289/562949953421312), (-118114914315127/562949953421312)), (4461/281474976710656), by norm_num⟩
  | 4 => ⟨((1411003227836487/2251799813685248), (-386907630531553/1125899906842624)), (18357/562949953421312), by norm_num⟩
  | 5 => ⟨((618234375120795/2251799813685248), (-969762786614915/2251799813685248)), (142489/2251799813685248), by norm_num⟩
  | 6 => ⟨((-247902196425065/2251799813685248), (-133124775735965/562949953421312)), (401941/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-71207870573/8589934592)), (1/8589934592), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-12536430677/8589934592), (-77334106737/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-954727210845801/4503599627370496), (-428536033957001/4503599627370496)), (360423/2251799813685248), by norm_num⟩
  | 1 => ⟨((56695964635/137438953472), (25448383109/137438953472)), (11/34359738368), by norm_num⟩
  | 2 => ⟨((-55162626497/137438953472), (-6190033371/34359738368)), (45/137438953472), by norm_num⟩
  | 3 => ⟨((71561009833/274877906944), (32120663359/274877906944)), (15/68719476736), by norm_num⟩
  | 4 => ⟨((-69625647655/549755813888), (-7812990603/137438953472)), (15/137438953472), by norm_num⟩
  | 5 => ⟨((27097050881/549755813888), (12162702167/549755813888)), (3/68719476736), by norm_num⟩
  | 6 => ⟨((-70304568425/4398046511104), (-15778350391/2199023255552)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((78175070413/17592186044416), (35089431041/17592186044416)), (73/17592186044416), by norm_num⟩
  | 8 => ⟨((-19015207865/17592186044416), (-17070219997/35184372088832)), (73/70368744177664), by norm_num⟩
  | 9 => ⟨((65781130615/281474976710656), (29526323857/281474976710656)), (65/281474976710656), by norm_num⟩
  | 10 => ⟨((-1600052121/35184372088832), (-22982229303/1125899906842624)), (13/281474976710656), by norm_num⟩
  | 11 => ⟨((36230489149/4503599627370496), (127049299/35184372088832)), (19/2251799813685248), by norm_num⟩
  | 12 => ⟨((-94001702053/72057594037927936), (-10548331535/18014398509481984)), (101/72057594037927936), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (-1771349690407/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444927128237575/158456325028528675187087900672), (-2098428605981/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945399199289387/19807040628566084398385987584), (-2360414908853/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890638678613163/2475880078570760549798248448), (-626891484265/309485009821345068724781056)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443075999366845/38685626227668133590597632), (-2507144109545/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550596165136399/9671406556917033397649408), (-2349999396477/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629850046453395/302231454903657293676544), (-4111602498699/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889271233466599/75557863725914323419136), (-834959144579/9444732965739290427392)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298647225079233/4722366482869645213696), (-5008284007959/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811484335099051/295147905179352825856), (-1721000059049/147573952589676412928)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825371369161387/73786976294838206464), (-4300707330367/36893488147419103232)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824785306790749/9223372036854775808), (-9671660887619/9223372036854775808)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798013512756707/576460752303423488), (-9665497098575/1152921504606846976)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196359156408525/144115188075855872), (-8450374976087/144115188075855872)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((373572441637583/9007199254740992), (-6330845357097/18014398509481984)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492546551237099/9007199254740992), (-15802833899369/9007199254740992)), (1389/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117223149362885/2251799813685248), (-3941601744969/562949953421312)), (349/562949953421312), by norm_num⟩
  | 1 => ⟨((556413267357943/562949953421312), (-11779258556487/562949953421312)), (2107/1125899906842624), by norm_num⟩
  | 0 => ⟨((549761147245945/562949953421312), (-46752510993953/1125899906842624)), (4273/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((549761147245945/562949953421312), (-46752510993953/1125899906842624)), (16300205710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((267955319888207/281474976710656), (-45657191948337/562949953421312)), (4351/562949953421312), by norm_num⟩
  | 2 => ⟨((1012934215257239/1125899906842624), (-173856839662021/1125899906842624)), (17981/1125899906842624), by norm_num⟩
  | 3 => ⟨((884456529119089/1125899906842624), (-312826283011263/1125899906842624)), (9477/281474976710656), by norm_num⟩
  | 4 => ⟨((607872035870421/1125899906842624), (-30717789255493/70368744177664)), (161247/2251799813685248), by norm_num⟩
  | 5 => ⟨((227287117742777/2251799813685248), (-1061407891266701/2251799813685248)), (78723/562949953421312), by norm_num⟩
  | 6 => ⟨((-954727210845801/4503599627370496), (-428536033957001/4503599627370496)), (360423/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-77334106737/8589934592)), (1/4294967296), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-13396700123/8589934592), (-82640893885/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-116082307877195/562949953421312), (184276408424285/4503599627370496)), (1251509/9007199254740992), by norm_num⟩
  | 1 => ⟨((58932220033/137438953472), (-2923523093/34359738368)), (21/68719476736), by norm_num⟩
  | 2 => ⟨((-7659131655/17179869184), (12158590735/137438953472)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((21235622049/68719476736), (-16855385775/274877906944)), (33/137438953472), by norm_num⟩
  | 4 => ⟨((-88316469305/549755813888), (17524894691/549755813888)), (71/549755813888), by norm_num⟩
  | 5 => ⟨((73459574035/1099511627776), (-7288398807/549755813888)), (61/1099511627776), by norm_num⟩
  | 6 => ⟨((-101836593255/4398046511104), (1262983271/274877906944)), (11/549755813888), by norm_num⟩
  | 7 => ⟨((60503783565/8796093022208), (-12005942309/8796093022208)), (27/4398046511104), by norm_num⟩
  | 8 => ⟨((-62907040487/35184372088832), (1560353449/4398046511104)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((58138450335/140737488355328), (-5768291167/70368744177664)), (7/17592186044416), by norm_num⟩
  | 10 => ⟨((-96716407037/1125899906842624), (4797929711/281474976710656)), (3/35184372088832), by norm_num⟩
  | 11 => ⟨((36566566283/2251799813685248), (-907001305/281474976710656)), (75/4503599627370496), by norm_num⟩
  | 12 => ⟨((-12673006161/4503599627370496), (10058966357/18014398509481984)), (107/36028797018963968), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (3837108814165/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889776176900699/316912650057057350374175801344), (4544878664865/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945311325561805/19807040628566084398385987584), (5112252943745/39614081257132168796771975168)), (409/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472612963938225/618970019642690137449562112), (21214456203/9671406556917033397649408)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772117072103815/154742504910672534362390528), (339370259829/9671406556917033397649408)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48450650430777/302231454903657293676544), (318094761501/604462909807314587353088)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629773275874133/302231454903657293676544), (4452288898735/604462909807314587353088)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889021525429515/75557863725914323419136), (7233023552825/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298459766060337/4722366482869645213696), (5423064892645/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405677656299715/147573952589676412928), (3726973515655/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825048380317419/73786976294838206464), (9313282661983/73786976294838206464)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912210675311887/4611686018427387904), (10471734657997/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595662328849597/1152921504606846976), (1308074804905/144115188075855872)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598019608018209/72057594037927936), (9148494303389/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493808200075405/36028797018963968), (13706680117597/36028797018963968)), (1111/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491941708027629/9007199254740992), (267269326353/140737488355328)), (1391/9007199254740992), by norm_num⟩
  | 2 => ⟨((558307001966499/1125899906842624), (17063055406701/2251799813685248)), (699/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111902149999069/1125899906842624), (12744544986037/562949953421312)), (2113/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097631391778603/1125899906842624), (394968591679/8796093022208)), (67/17592186044416), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1097631391778603/1125899906842624), (394968591679/8796093022208)), (255584783905739/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((266950631629043/281474976710656), (98573292460391/1125899906842624)), (8747/1125899906842624), by norm_num⟩
  | 2 => ⟨((1004072861874617/1125899906842624), (46743413911187/281474976710656)), (4531/281474976710656), by norm_num⟩
  | 3 => ⟨((432189024145623/562949953421312), (333484659475369/1125899906842624)), (19173/562949953421312), by norm_num⟩
  | 4 => ⟨((141206467021955/281474976710656), (16001467878079/35184372088832)), (40797/562949953421312), by norm_num⟩
  | 5 => ⟨((25240325219173/562949953421312), (256876631536765/562949953421312)), (312165/2251799813685248), by norm_num⟩
  | 6 => ⟨((-116082307877195/562949953421312), (184276408424285/4503599627370496)), (1251509/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-82640893885/8589934592)), (1/4294967296), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile010Terms0
