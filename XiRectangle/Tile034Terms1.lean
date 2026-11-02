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
namespace Reinmann.XiRectangle.Tile034Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8319/640))
  have he : value ((7/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-64510795/33554432), (-958330897/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-1263568420268801/9007199254740992), (371776465858775/9007199254740992)), (171407433/9007199254740992), by norm_num⟩
  | 1 => ⟨((1323863787/4294967296), (-48689627/536870912)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-1454413025/4294967296), (427928181/4294967296)), (203/4294967296), by norm_num⟩
  | 3 => ⟨((1065224015/4294967296), (-156709053/2147483648)), (151/4294967296), by norm_num⟩
  | 4 => ⟨((-1170268193/8589934592), (344324983/8589934592)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((1028536815/17179869184), (-151311863/8589934592)), (75/8589934592), by norm_num⟩
  | 6 => ⟨((-1506617579/68719476736), (3463189/536870912)), (223/68719476736), by norm_num⟩
  | 7 => ⟨((472911025/68719476736), (-139143387/68719476736)), (71/68719476736), by norm_num⟩
  | 8 => ⟨((-1039091727/549755813888), (152864635/274877906944)), (79/274877906944), by norm_num⟩
  | 9 => ⟨((507359529/1099511627776), (-298558163/2199023255552)), (39/549755813888), by norm_num⟩
  | 10 => ⟨((-445913131/4398046511104), (262399733/8796093022208)), (139/8796093022208), by norm_num⟩
  | 11 => ⟨((712560939/35184372088832), (-209654961/35184372088832)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((-1043770939/281474976710656), (153553011/140737488355328)), (83/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403057283/10141204801825835211973625643008), (1859764829133/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778993135690829/633825300114114700748351602688), (4402974551707/633825300114114700748351602688)), (69475/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889993676745311/39614081257132168796771975168), (1238120962625/9903520314283042199192993792)), (78181/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944891869833217/1237940039285380274899124224), (5260978904261/2475880078570760549798248448)), (83091/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442862286612485/38685626227668133590597632), (2629907144233/77371252455336267181195264)), (41559/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774897417926575/4835703278458516698824704), (2464919295497/4835703278458516698824704)), (77953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258999023465355/604462909807314587353088), (4312371574627/604462909807314587353088)), (68237/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888132171565223/75557863725914323419136), (3502642155573/37778931862957161709568)), (27735/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297793082889545/4722366482869645213696), (5251933911697/4722366482869645213696)), (20813/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202724309482587/73786976294838206464), (7218111929523/590295810358705651712)), (114549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455976000985579/18446744073709551616), (9017694900373/73786976294838206464)), (143301/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823135041789691/9223372036854775808), (10138108654667/9223372036854775808)), (161373/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594377413889853/1152921504606846976), (1266201618699/144115188075855872)), (40393/288230376151711744), by norm_num⟩
  | 5 => ⟨((298729121107167/36028797018963968), (8853856327053/144115188075855872)), (4425/4503599627370496), by norm_num⟩
  | 4 => ⟨((1492127242793795/36028797018963968), (13261681174621/36028797018963968)), (106425/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489846011478409/9007199254740992), (8271842903109/4503599627370496)), (266849/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114526566993399/2251799813685248), (16493592805515/2251799813685248)), (1047/8796093022208), by norm_num⟩
  | 1 => ⟨((554395838215493/562949953421312), (24615264374505/1125899906842624)), (202505/562949953421312), by norm_num⟩
  | 0 => ⟨((545746682305029/562949953421312), (6091335368301/140737488355328)), (821913/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((545746682305029/562949953421312), (6091335368301/140737488355328)), (3135349277976607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056029117953871/1125899906842624), (94483029558249/1125899906842624)), (416185/281474976710656), by norm_num⟩
  | 2 => ⟨((982565544564485/1125899906842624), (5538726719823/35184372088832)), (425283/140737488355328), by norm_num⟩
  | 3 => ⟨((829577558505591/1125899906842624), (38668887012653/140737488355328)), (3504719/562949953421312), by norm_num⟩
  | 4 => ⟨((1052492892691725/2251799813685248), (911735494301105/2251799813685248)), (14181101/1125899906842624), by norm_num⟩
  | 5 => ⟨((122781641564147/2251799813685248), (1704583368263517/4503599627370496)), (98960561/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1263568420268801/9007199254740992), (371776465858775/9007199254740992)), (171407433/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/33554432), (-958330897/33554432)), (3/67108864), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-67604193/33554432), (-2008568865/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((101827347089645/9007199254740992), (1196805269044709/9007199254740992)), (140981179/9007199254740992), by norm_num⟩
  | 1 => ⟨((-27950541/1073741824), (-657021039/2147483648)), (157/4294967296), by norm_num⟩
  | 2 => ⟨((64358499/2147483648), (756423425/2147483648)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-98793947/4294967296), (-290288217/1073741824)), (71/2147483648), by norm_num⟩
  | 4 => ⟨((113740735/8589934592), (668413321/4294967296)), (83/4294967296), by norm_num⟩
  | 5 => ⟨((-6547443/1073741824), (-1231262839/17179869184)), (155/17179869184), by norm_num⟩
  | 6 => ⟨((160811143/68719476736), (945029153/34359738368)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((-105794669/137438953472), (-1243434309/137438953472)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((60900307/274877906944), (357889163/137438953472)), (93/274877906944), by norm_num⟩
  | 9 => ⟨((-124647235/2199023255552), (-1465013781/2199023255552)), (3/34359738368), by norm_num⟩
  | 10 => ⟨((57402173/4398046511104), (1349327557/8796093022208)), (179/8796093022208), by norm_num⟩
  | 11 => ⟨((-24031525/8796093022208), (-282449229/8796093022208)), (19/4398046511104), by norm_num⟩
  | 12 => ⟨((147559017/281474976710656), (867151179/140737488355328)), (59/70368744177664), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (1935574241359/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778858555795833/633825300114114700748351602688), (143179860523/39614081257132168796771975168)), (8665/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889842732753407/39614081257132168796771975168), (1288389926311/19807040628566084398385987584)), (77995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472405987991971/618970019642690137449562112), (2737265569201/2475880078570760549798248448)), (41441/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771290022416135/154742504910672534362390528), (171039520997/9671406556917033397649408)), (82897/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774823180908237/4835703278458516698824704), (2564920174735/9671406556917033397649408)), (77731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258869812979993/604462909807314587353088), (1121816352001/302231454903657293676544)), (68029/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887923524130555/75557863725914323419136), (3644642708809/75557863725914323419136)), (6911/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((81102359438443/295147905179352825856), (2732379557185/4722366482869645213696)), (82957/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621582767514031/590295810358705651712), (234701945745/36893488147419103232)), (114105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113977635928683/4611686018427387904), (293209631791/4611686018427387904)), (35673/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822844337732833/9223372036854775808), (5274083928243/9223372036854775808)), (160611/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594091519311181/1152921504606846976), (658684421083/144115188075855872)), (160715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149333965861719/18014398509481984), (4605610778113/144115188075855872)), (140743/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491770880852751/36028797018963968), (6898066971221/36028797018963968)), (211347/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489419355562527/9007199254740992), (8604497673139/9007199254740992)), (264593/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114127988753295/2251799813685248), (17154837333229/4503599627370496)), (33151/281474976710656), by norm_num⟩
  | 1 => ⟨((2216527188279541/2251799813685248), (12798605453837/1125899906842624)), (199677/562949953421312), by norm_num⟩
  | 0 => ⟨((1090713891144147/1125899906842624), (25328168771737/1125899906842624)), (1609795/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090713891144147/1125899906842624), (25328168771737/1125899906842624)), (6140880593306731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112115418031871/2251799813685248), (1533539157693/35184372088832)), (1595701/1125899906842624), by norm_num⟩
  | 2 => ⟨((1976818176898569/2251799813685248), (92058249354039/1125899906842624)), (783133/281474976710656), by norm_num⟩
  | 3 => ⟨((1720362172461547/2251799813685248), (40408214697979/281474976710656)), (6012255/1125899906842624), by norm_num⟩
  | 4 => ⟨((1267939211522961/2251799813685248), (493946316901683/2251799813685248)), (21825763/2251799813685248), by norm_num⟩
  | 5 => ⟨((302799314541409/1125899906842624), (139065182388929/562949953421312)), (34154455/2251799813685248), by norm_num⟩
  | 6 => ⟨((101827347089645/9007199254740992), (1196805269044709/9007199254740992)), (140981179/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-2008568865/67108864)), (3/67108864), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-4400157/2097152), (-522927231/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1071476122420371/9007199254740992), (270210906420381/9007199254740992)), (85502361/9007199254740992), by norm_num⟩
  | 1 => ⟨((-306282941/1073741824), (-308960655/4294967296)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((1468868833/4294967296), (370427647/4294967296)), (61/2147483648), by norm_num⟩
  | 3 => ⟨((-36689517/134217728), (-296082235/4294967296)), (25/1073741824), by norm_num⟩
  | 4 => ⟨((703820955/4294967296), (44373387/1073741824)), (61/4294967296), by norm_num⟩
  | 5 => ⟨((-1350151153/17179869184), (-21280547/1073741824)), (119/17179869184), by norm_num⟩
  | 6 => ⟨((1079173689/34359738368), (272152123/34359738368)), (97/34359738368), by norm_num⟩
  | 7 => ⟨((-1478711707/137438953472), (-46613735/17179869184)), (135/137438953472), by norm_num⟩
  | 8 => ⟨((886448953/274877906944), (111774855/137438953472)), (83/274877906944), by norm_num⟩
  | 9 => ⟨((-944716335/1099511627776), (-59560977/274877906944)), (45/549755813888), by norm_num⟩
  | 10 => ⟨((453066167/2199023255552), (28564197/549755813888)), (11/549755813888), by norm_num⟩
  | 11 => ⟨((-1580225775/35184372088832), (-6226723/549755813888)), (39/8796093022208), by norm_num⟩
  | 12 => ⟨((315767993/35184372088832), (39816079/17592186044416)), (127/140737488355328), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681581499/10141204801825835211973625643008), (160895131841/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778732721348867/633825300114114700748351602688), (380807252709/633825300114114700748351602688)), (46119/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472425337386651/9903520314283042199192993792), (107082443919/9903520314283042199192993792)), (103771/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472368491318631/618970019642690137449562112), (455003008831/2475880078570760549798248448)), (110259/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771140297613817/154742504910672534362390528), (28430843785/9671406556917033397649408)), (55131/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774753136456757/4835703278458516698824704), (426346341385/9671406556917033397649408)), (51687/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157343439138629/75557863725914323419136), (93234193781/151115727451828646838272)), (11307/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943862653778071/37778931862957161709568), (605804335393/75557863725914323419136)), (146997/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162186192978557/590295810358705651712), (454162656635/4722366482869645213696)), (110253/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101336232605501/36893488147419103232), (624164102461/590295810358705651712)), (75803/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823389474907495/73786976294838206464), (779741093333/73786976294838206464)), (94761/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822561570834571/9223372036854775808), (219142788641/2305843009213693952)), (213231/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398452662512591/288230376151711744), (437887446591/576460752303423488)), (213253/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194428096949153/144115188075855872), (765408209905/144115188075855872)), (729/562949953421312), by norm_num⟩
  | 4 => ⟨((1491409686810293/36028797018963968), (1146325099793/36028797018963968)), (279989/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488975278587331/9007199254740992), (1429784203947/9007199254740992)), (350079/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227389976699359/4503599627370496), (2850223678467/4503599627370496)), (700439/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107641621672081/1125899906842624), (4252049757915/2251799813685248)), (1051371/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179158165880053/2251799813685248), (4205705724997/1125899906842624)), (2105631/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179158165880053/2251799813685248), (4205705724997/1125899906842624)), (8032344826705168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2108828471882489/2251799813685248), (16280129198371/2251799813685248)), (4091141/2251799813685248), by norm_num⟩
  | 2 => ⟨((123426060516949/140737488355328), (30492941486893/2251799813685248)), (3860965/1125899906842624), by norm_num⟩
  | 3 => ⟨((1731491500707735/2251799813685248), (53484308769229/2251799813685248)), (6876661/1125899906842624), by norm_num⟩
  | 4 => ⟨((1330136998651189/2251799813685248), (41126047480921/1125899906842624)), (21804201/2251799813685248), by norm_num⟩
  | 5 => ⟨((782706800730529/2251799813685248), (194345081761535/4503599627370496)), (54704715/4503599627370496), by norm_num⟩
  | 6 => ⟨((1071476122420371/9007199254740992), (270210906420381/9007199254740992)), (85502361/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4400157/2097152), (-522927231/16777216)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-72957177/33554432), (-1083804925/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((324653971473423/4503599627370496), (-791836641036827/9007199254740992)), (123437687/9007199254740992), by norm_num⟩
  | 1 => ⟨((-769362271/4294967296), (469121965/2147483648)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((955896711/4294967296), (-582862145/2147483648)), (187/4294967296), by norm_num⟩
  | 3 => ⟨((-197942841/1073741824), (965572013/4294967296)), (157/4294967296), by norm_num⟩
  | 4 => ⟨((245934741/2147483648), (-599839079/4294967296)), (99/4294967296), by norm_num⟩
  | 5 => ⟨((-488899899/8589934592), (298108823/4294967296)), (101/8589934592), by norm_num⟩
  | 6 => ⟨((202478435/8589934592), (-987696795/34359738368)), (85/17179869184), by norm_num⟩
  | 7 => ⟨((-287508577/34359738368), (701238381/68719476736)), (123/68719476736), by norm_num⟩
  | 8 => ⟨((714431975/274877906944), (-435627979/137438953472)), (155/274877906944), by norm_num⟩
  | 9 => ⟨((-49313799/68719476736), (962217655/1099511627776)), (87/549755813888), by norm_num⟩
  | 10 => ⟨((784257197/4398046511104), (-239102105/1099511627776)), (175/4398046511104), by norm_num⟩
  | 11 => ⟨((-708656699/17592186044416), (864212961/17592186044416)), (5/549755813888), by norm_num⟩
  | 12 => ⟨((293490957/35184372088832), (-715829511/70368744177664)), (135/70368744177664), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790571753654357/5070602400912917605986812821504), (-143934882163/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778614449291889/633825300114114700748351602688), (-170311429109/79228162514264337593543950336)), (92335/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472392066657319/9903520314283042199192993792), (-766255978317/19807040628566084398385987584)), (103885/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889332527921299/2475880078570760549798248448), (-813966415431/1237940039285380274899124224)), (27597/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885499409483917/77371252455336267181195264), (-813763358487/77371252455336267181195264)), (110399/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549373592851113/9671406556917033397649408), (-762687468379/4835703278458516698824704)), (103511/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258631374269659/604462909807314587353088), (-667135930917/302231454903657293676544)), (90585/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235942062493195/9444732965739290427392), (-541845896223/18889465931478580854784)), (147221/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297347866473263/4722366482869645213696), (-1624830845855/4722366482869645213696)), (27609/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621184799084731/590295810358705651712), (-2232994400581/590295810358705651712)), (151881/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455786411905069/18446744073709551616), (-2789522043847/73786976294838206464)), (189899/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822287026371225/9223372036854775808), (-1567923853973/4611686018427387904)), (106851/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593535807924837/1152921504606846976), (-3132894553219/1152921504606846976)), (213785/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149273409538725/18014398509481984), (-1368981992729/72057594037927936)), (187155/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491047791012939/36028797018963968), (-2050158673719/18014398509481984)), (140459/18014398509481984), by norm_num⟩
  | 3 => ⟨((744260875740201/4503599627370496), (-5113816503437/9007199254740992)), (351473/9007199254740992), by norm_num⟩
  | 2 => ⟨((278309934344801/562949953421312), (-1274121502911/562949953421312)), (703927/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106954478010921/1125899906842624), (-7601541717841/1125899906842624)), (66147/140737488355328), by norm_num⟩
  | 0 => ⟨((2176375960394455/2251799813685248), (-30062330867675/2251799813685248)), (2126597/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176375960394455/2251799813685248), (-30062330867675/2251799813685248)), (8112323769576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051538540074601/1125899906842624), (-58110791035865/2251799813685248)), (1041879/562949953421312), by norm_num⟩
  | 2 => ⟨((245334660421097/281474976710656), (-6784099545291/140737488355328)), (7999633/2251799813685248), by norm_num⟩
  | 3 => ⟨((1705444662359619/2251799813685248), (-47304375761055/562949953421312)), (7358125/1125899906842624), by norm_num⟩
  | 4 => ⟨((1275752051960233/2251799813685248), (-71653789699817/562949953421312)), (12382239/1125899906842624), by norm_num⟩
  | 5 => ⟨((686293266139877/2251799813685248), (-20297645617677/140737488355328)), (34364697/2251799813685248), by norm_num⟩
  | 6 => ⟨((324653971473423/4503599627370496), (-791836641036827/9007199254740992)), (123437687/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72957177/33554432), (-1083804925/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-75307241/33554432), (-1118715967/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-330617918092513/9007199254740992), (-447838696773183/4503599627370496)), (167289875/9007199254740992), by norm_num⟩
  | 1 => ⟨((404366597/4294967296), (547735013/2147483648)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-259294961/2147483648), (-702456285/2147483648)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((443385629/4294967296), (1201176531/4294967296)), (231/4294967296), by norm_num⟩
  | 4 => ⟨((-284315421/4294967296), (-770239243/4294967296)), (299/8589934592), by norm_num⟩
  | 5 => ⟨((291701863/8589934592), (790249861/8589934592)), (155/8589934592), by norm_num⟩
  | 6 => ⟨((-498800337/34359738368), (-675650291/17179869184)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((365542173/68719476736), (990290731/68719476736)), (199/68719476736), by norm_num⟩
  | 8 => ⟨((-468798581/274877906944), (-1270022787/274877906944)), (257/274877906944), by norm_num⟩
  | 9 => ⟨((534419831/1099511627776), (90487337/68719476736)), (295/1099511627776), by norm_num⟩
  | 10 => ⟨((-548303921/4398046511104), (-371352699/1099511627776)), (305/4398046511104), by norm_num⟩
  | 11 => ⟨((127851981/4398046511104), (692727903/8796093022208)), (287/17592186044416), by norm_num⟩
  | 12 => ⟨((-218622571/35184372088832), (-1184541327/70368744177664)), (247/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275821141/10141204801825835211973625643008), (-156672216525/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889251394319449/316912650057057350374175801344), (-2965783855807/633825300114114700748351602688)), (92493/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889442464060159/39614081257132168796771975168), (-1667923671629/19807040628566084398385987584)), (104073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889198618875139/2475880078570760549798248448), (-3543525648425/2475880078570760549798248448)), (110599/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770864635894675/154742504910672534362390528), (-3542612214575/154742504910672534362390528)), (3457/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549247505280875/9671406556917033397649408), (-3320228680137/9671406556917033397649408)), (12967/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314630189236995/151115727451828646838272), (-2904230107943/604462909807314587353088)), (90795/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887356202252337/75557863725914323419136), (-2358777901269/37778931862957161709568)), (73795/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648606083619211/2361183241434822606848), (-3536576597367/4722366482869645213696)), (110735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620997440153805/590295810358705651712), (-1215052447025/147573952589676412928)), (76165/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28482973311103/1152921504606846976), (-379461853927/4611686018427387904)), (47629/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911010331492175/4611686018427387904), (-1706247949135/2305843009213693952)), (107237/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593267463353499/1152921504606846976), (-6818344646443/1152921504606846976)), (214653/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298487562895703/36028797018963968), (-5958580143433/144115188075855872)), (188023/144115188075855872), by norm_num⟩
  | 4 => ⟨((745343910729249/18014398509481984), (-8922943917297/36028797018963968)), (141219/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488064064138873/9007199254740992), (-5563798042119/4503599627370496)), (353755/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225541049211959/4503599627370496), (-22177089462107/4503599627370496)), (354819/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212444127760443/2251799813685248), (-258366386819/17592186044416)), (267447/562949953421312), by norm_num⟩
  | 0 => ⟨((2173220155867235/2251799813685248), (-65365965029213/2251799813685248)), (1080491/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2173220155867235/2251799813685248), (-65365965029213/2251799813685248)), (4121746067527389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2095485179369043/2251799813685248), (-63084929595369/1125899906842624)), (1074151/562949953421312), by norm_num⟩
  | 2 => ⟨((485738039078487/562949953421312), (-117411445018543/1125899906842624)), (2119543/562949953421312), by norm_num⟩
  | 3 => ⟨((1651976907286313/2251799813685248), (-202615542365971/1125899906842624)), (16398929/2251799813685248), by norm_num⟩
  | 4 => ⟨((1139006875560889/2251799813685248), (-594575405880483/2251799813685248)), (29963595/2251799813685248), by norm_num⟩
  | 5 => ⟨((26196177152411/140737488355328), (-1202994104931457/4503599627370496)), (23067929/1125899906842624), by norm_num⟩
  | 6 => ⟨((-330617918092513/9007199254740992), (-447838696773183/4503599627370496)), (167289875/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75307241/33554432), (-1118715967/33554432)), (1/16777216), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-77483061/33554432), (-1151038543/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1732233926428241/18014398509481984), (-449510616010609/18014398509481984)), (310341487/18014398509481984), by norm_num⟩
  | 1 => ⟨((136240263/536870912), (141416107/2147483648)), (197/4294967296), by norm_num⟩
  | 2 => ⟨((-719091729/2147483648), (-186602607/2147483648)), (131/2147483648), by norm_num⟩
  | 3 => ⟨((316287383/1073741824), (164151659/2147483648)), (233/4294967296), by norm_num⟩
  | 4 => ⟨((-104337567/536870912), (-433205639/8589934592)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((881129027/8589934592), (228650903/8589934592)), (165/8589934592), by norm_num⟩
  | 6 => ⟨((-6055599/134217728), (-201140947/17179869184)), (293/34359738368), by norm_num⟩
  | 7 => ⟨((584450667/34359738368), (303327137/68719476736)), (223/68719476736), by norm_num⟩
  | 8 => ⟨((-48199963/8589934592), (-100062213/68719476736)), (37/34359738368), by norm_num⟩
  | 9 => ⟨((904550867/549755813888), (234728815/549755813888)), (11/34359738368), by norm_num⟩
  | 10 => ⟨((-477432319/1099511627776), (-7743285/68719476736)), (187/2199023255552), by norm_num⟩
  | 11 => ⟨((916342735/8796093022208), (237788777/8796093022208)), (181/8796093022208), by norm_num⟩
  | 12 => ⟨((-403046835/17592186044416), (-209179405/35184372088832)), (321/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (-3761545415079/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889198481401731/316912650057057350374175801344), (-4449870205311/633825300114114700748351602688)), (46319/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944661552231825/19807040628566084398385987584), (-2502535570901/19807040628566084398385987584)), (52123/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889071394363663/2475880078570760549798248448), (-5316632500175/2475880078570760549798248448)), (55397/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885368478121729/77371252455336267181195264), (-5315220086309/154742504910672534362390528)), (6927/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774563661192987/4835703278458516698824704), (-9729528123/18889465931478580854784)), (12993/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629207557051215/302231454903657293676544), (-2178664228279/302231454903657293676544)), (45495/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887183628224371/75557863725914323419136), (-1769461647481/18889465931478580854784)), (147931/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297081946233051/4722366482869645213696), (-2652962462559/2361183241434822606848)), (27753/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405204275840697/147573952589676412928), (-911456299879/73786976294838206464)), (76373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455670737351707/18446744073709551616), (-9108570462355/73786976294838206464)), (11943/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821762265208787/9223372036854775808), (-10238905322975/9223372036854775808)), (215189/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593005775684465/1152921504606846976), (-5114307352377/576460752303423488)), (107729/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193717583260739/144115188075855872), (-8938467722973/144115188075855872)), (188829/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490331459517213/36028797018963968), (-13384578326379/36028797018963968)), (141925/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487605786046643/9007199254740992), (-8345147795033/4503599627370496)), (177937/4503599627370496), by norm_num⟩
  | 2 => ⟨((139036639321761/281474976710656), (-4157432887351/562949953421312)), (357471/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105458490977457/1125899906842624), (-24793457253869/1125899906842624)), (270105/562949953421312), by norm_num⟩
  | 0 => ⟨((1084895324979537/1125899906842624), (-6122997550939/140737488355328)), (68531/70368744177664), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1084895324979537/1125899906842624), (-6122997550939/140737488355328)), (261425018578982331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1043252982514079/1125899906842624), (-94400027959905/1125899906842624)), (2208535/1125899906842624), by norm_num⟩
  | 2 => ⟨((958757891074749/1125899906842624), (-683363856603/4398046511104)), (1115795/281474976710656), by norm_num⟩
  | 3 => ⟨((1578492516576855/2251799813685248), (-148970796088497/562949953421312)), (17976387/2251799813685248), by norm_num⟩
  | 4 => ⟨((237206016550449/562949953421312), (-104427260978119/281474976710656)), (34716603/2251799813685248), by norm_num⟩
  | 5 => ⟨((179717331806205/4503599627370496), (-1408055515861051/4503599627370496)), (110032565/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1732233926428241/18014398509481984), (-449510616010609/18014398509481984)), (310341487/18014398509481984), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-1151038543/33554432)), (1/16777216), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-79508701/33554432), (-590565071/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-337104769318693/4503599627370496), (15782074793975/281474976710656)), (153626715/9007199254740992), by norm_num⟩
  | 1 => ⟨((870606077/4294967296), (-326070029/2147483648)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((-1178822481/4294967296), (883014007/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((1064103485/4294967296), (-398541043/2147483648)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-360205707/2147483648), (33727161/268435456)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((390182055/4294967296), (-584543009/8589934592)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((-22013179/536870912), (527657271/17179869184)), (171/17179869184), by norm_num⟩
  | 7 => ⟨((1090062515/68719476736), (-408263537/34359738368)), (267/68719476736), by norm_num⟩
  | 8 => ⟨((-737986003/137438953472), (552799077/137438953472)), (183/137438953472), by norm_num⟩
  | 9 => ⟨((888223619/549755813888), (-332668367/274877906944)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((-240535415/549755813888), (360353055/1099511627776)), (243/2199023255552), by norm_num⟩
  | 11 => ⟨((947464697/8796093022208), (-354856059/4398046511104)), (121/4398046511104), by norm_num⟩
  | 12 => ⟨((-427630327/17592186044416), (160161337/8796093022208)), (55/8796093022208), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171562799/10141204801825835211973625643008), (3254823446855/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889153303004263/316912650057057350374175801344), (1925019734877/316912650057057350374175801344)), (92579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889221624256101/39614081257132168796771975168), (4330385847839/39614081257132168796771975168)), (6511/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888963793937459/2475880078570760549798248448), (4599921109799/2475880078570760549798248448)), (110715/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221328700715753/19342813113834066795298816), (1149667066065/38685626227668133590597632)), (110747/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549026946638959/9671406556917033397649408), (2154960327713/4835703278458516698824704)), (103859/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258327550501467/604462909807314587353088), (3769850075093/604462909807314587353088)), (45455/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943520917093543/37778931862957161709568), (3061756209195/37778931862957161709568)), (147793/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296976035023859/4722366482869645213696), (1147613208825/1180591620717411303424)), (27725/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620672180480225/590295810358705651712), (6308329116631/590295810358705651712)), (152577/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822502852057953/73786976294838206464), (1970024624207/18446744073709551616)), (190857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821561105944601/9223372036854775808), (8857809471577/9223372036854775808)), (53725/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796403213047127/576460752303423488), (2212172162207/288230376151711744)), (215133/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193545183934573/144115188075855872), (3866174842919/72057594037927936)), (188503/144115188075855872), by norm_num⟩
  | 4 => ⟨((93129807054575/2251799813685248), (723627429901/2251799813685248)), (17705/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487294670105263/9007199254740992), (14436743976451/9007199254740992)), (88755/2251799813685248), by norm_num⟩
  | 2 => ⟨((138999068907909/281474976710656), (14383127604941/2251799813685248)), (356401/2251799813685248), by norm_num⟩
  | 1 => ⟨((552516929217073/562949953421312), (21440967564049/1125899906842624)), (269033/562949953421312), by norm_num⟩
  | 0 => ⟨((1084149897061237/1125899906842624), (661702237829/17592186044416)), (1090041/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084149897061237/1125899906842624), (661702237829/17592186044416)), (4158176426414107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042355150021335/1125899906842624), (40778582673937/562949953421312)), (4362485/2251799813685248), by norm_num⟩
  | 2 => ⟨((1918203707085587/2251799813685248), (302021630181663/2251799813685248)), (136087/35184372088832), by norm_num⟩
  | 3 => ⟨((1593520158839867/2251799813685248), (514556406935983/2251799813685248)), (2146861/281474976710656), by norm_num⟩
  | 4 => ⟨((1010097872327161/2251799813685248), (728267230798617/2251799813685248)), (16078685/1125899906842624), by norm_num⟩
  | 5 => ⟨((435140414567289/4503599627370496), (653362857430363/2251799813685248)), (99300569/4503599627370496), by norm_num⟩
  | 6 => ⟨((-337104769318693/4503599627370496), (15782074793975/281474976710656)), (153626715/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-79508701/33554432), (-590565071/16777216)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile034Terms1
