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
namespace Reinmann.XiRectangle.Tile033Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8319/640))
  have he : value ((5/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-7268175/4194304), (-1209278953/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-70757677078381/4503599627370496), (792980860558751/4503599627370496)), (130596833/4503599627370496), by norm_num⟩
  | 1 => ⟨((46773419/1073741824), (-1048378845/2147483648)), (175/2147483648), by norm_num⟩
  | 2 => ⟨((-64841727/1073741824), (1453361681/2147483648)), (61/536870912), by norm_num⟩
  | 3 => ⟨((119852961/2147483648), (-671595701/1073741824)), (227/2147483648), by norm_num⟩
  | 4 => ⟨((-41537871/1073741824), (1862058667/4294967296)), (317/4294967296), by norm_num⟩
  | 5 => ⟨((46066973/2147483648), (-258136143/1073741824)), (177/4294967296), by norm_num⟩
  | 6 => ⟨((-170299693/17179869184), (238568453/2147483648)), (329/17179869184), by norm_num⟩
  | 7 => ⟨((67453001/17179869184), (-377972687/8589934592)), (263/34359738368), by norm_num⟩
  | 8 => ⟨((-93509715/68719476736), (1047962809/68719476736)), (23/8589934592), by norm_num⟩
  | 9 => ⟨((28807109/68719476736), (-1291364385/274877906944)), (229/274877906944), by norm_num⟩
  | 10 => ⟨((-127792425/1099511627776), (358042233/274877906944)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((64421061/2199023255552), (-1443932883/4398046511104)), (65/1099511627776), by norm_num⟩
  | 12 => ⟨((-119075405/17592186044416), (667238671/8796093022208)), (121/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581718513116769/10141204801825835211973625643008), (2162062611011/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779292564264737/633825300114114700748351602688), (2560131832963/633825300114114700748351602688)), (23113/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890330869711827/39614081257132168796771975168), (1439851930765/19807040628566084398385987584)), (104025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890142446719567/2475880078570760549798248448), (3059143864193/2475880078570760549798248448)), (110545/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885904173797171/77371252455336267181195264), (3058534793345/154742504910672534362390528)), (55283/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775066055772389/4835703278458516698824704), (1433364675289/4835703278458516698824704)), (51839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259294663917201/604462909807314587353088), (2507741298051/604462909807314587353088)), (90741/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236076696171449/9444732965739290427392), (2036933494071/37778931862957161709568)), (18437/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324538747428559/1180591620717411303424), (3054339483305/4722366482869645213696)), (55329/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811146745588983/295147905179352825856), (2098996796925/295147905179352825856)), (152215/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824529860474747/73786976294838206464), (5244908136241/73786976294838206464)), (95179/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823841996055075/9223372036854775808), (368560648403/576460752303423488)), (214277/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797543971754527/576460752303423488), (1473133390157/288230376151711744)), (214431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597771105436621/72057594037927936), (643872323893/18014398509481984)), (187801/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493073835425099/36028797018963968), (1929124797439/9007199254740992)), (4407/562949953421312), by norm_num⟩
  | 3 => ⟨((745521602780559/4503599627370496), (1203524553925/1125899906842624)), (353169/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115744587380197/2251799813685248), (19204180836931/4503599627370496)), (354083/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110670410729903/1125899906842624), (28675988372237/2251799813685248)), (66677/140737488355328), by norm_num⟩
  | 0 => ⟨((1095455481326983/1125899906842624), (56832327783941/2251799813685248)), (1076023/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1095455481326983/1125899906842624), (56832327783941/2251799813685248)), (4104702000144576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((532558545351501/562949953421312), (55295576995009/1125899906842624)), (4296339/2251799813685248), by norm_num⟩
  | 2 => ⟨((2009799999442691/2251799813685248), (209241563090031/2251799813685248)), (4275401/1125899906842624), by norm_num⟩
  | 3 => ⟨((1774364657885155/2251799813685248), (93377237804611/562949953421312)), (8426409/1125899906842624), by norm_num⟩
  | 4 => ⟨((334050676288511/562949953421312), (588632327277023/2251799813685248)), (16075019/1125899906842624), by norm_num⟩
  | 5 => ⟨((319511007106459/1125899906842624), (174645211192521/562949953421312)), (6870451/281474976710656), by norm_num⟩
  | 6 => ⟨((-70757677078381/4503599627370496), (792980860558751/4503599627370496)), (130596833/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/4194304), (-1209278953/33554432)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-29708395/16777216), (-1235720697/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((246621974699855/2251799813685248), (1173505469439279/9007199254740992)), (91191991/4503599627370496), by norm_num⟩
  | 1 => ⟨((-666363401/2147483648), (-792692031/2147483648)), (125/2147483648), by norm_num⟩
  | 2 => ⟨((117996855/268435456), (280733205/536870912)), (179/2147483648), by norm_num⟩
  | 3 => ⟨((-445747019/1073741824), (-530251375/1073741824)), (171/2147483648), by norm_num⟩
  | 4 => ⟨((631448201/2147483648), (187789409/536870912)), (123/2147483648), by norm_num⟩
  | 5 => ⟨((-178902747/1073741824), (-851275935/4294967296)), (141/4294967296), by norm_num⟩
  | 6 => ⟨((84478275/1073741824), (200987195/2147483648)), (135/8589934592), by norm_num⟩
  | 7 => ⟨((-547074231/17179869184), (-325394059/8589934592)), (111/17179869184), by norm_num⟩
  | 8 => ⟨((387494503/34359738368), (460955395/34359738368)), (159/68719476736), by norm_num⟩
  | 9 => ⟨((-975870753/274877906944), (-580437767/137438953472)), (203/274877906944), by norm_num⟩
  | 10 => ⟨((69121251/68719476736), (657801611/549755813888)), (117/549755813888), by norm_num⟩
  | 11 => ⟨((-569702547/2199023255552), (-169426573/549755813888)), (123/2199023255552), by norm_num⟩
  | 12 => ⟨((538029619/8796093022208), (640028837/8796093022208)), (59/4398046511104), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581669156673291/10141204801825835211973625643008), (1135571571137/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779236660075959/633825300114114700748351602688), (672281926203/316912650057057350374175801344)), (92333/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890268133451769/39614081257132168796771975168), (1512398236351/39614081257132168796771975168)), (103883/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472518997176749/618970019642690137449562112), (401658198249/618970019642690137449562112)), (110385/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27683470525267/2417851639229258349412352), (100394141131/9671406556917033397649408)), (27599/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550070255106949/9671406556917033397649408), (1505565260069/9671406556917033397649408)), (103509/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314810194328265/151115727451828646838272), (1317022842905/604462909807314587353088)), (90581/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888526449184655/75557863725914323419136), (2139512151939/75557863725914323419136)), (147217/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298090039135105/4722366482869645213696), (802032799325/2361183241434822606848)), (3451/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1622204816623779/590295810358705651712), (551166686955/147573952589676412928)), (151875/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824419965067687/73786976294838206464), (1377224468165/36893488147419103232)), (189891/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823719665380709/9223372036854775808), (1548426233823/4611686018427387904)), (213693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398741809397435/288230376151711744), (3094475883979/1152921504606846976)), (213773/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195438417858905/144115188075855872), (2704995006965/144115188075855872)), (187143/144115188075855872), by norm_num⟩
  | 4 => ⟨((373230446820533/9007199254740992), (2026077692743/18014398509481984)), (280897/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490859499929431/9007199254740992), (5055866980931/9007199254740992)), (175721/4503599627370496), by norm_num⟩
  | 2 => ⟨((2231140755804565/4503599627370496), (2520950753905/1125899906842624)), (351923/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220865424703735/2251799813685248), (15056054690859/2251799813685248)), (1058183/2251799813685248), by norm_num⟩
  | 0 => ⟨((547536901477135/562949953421312), (29834572933873/2251799813685248)), (2126057/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((547536901477135/562949953421312), (29834572933873/2251799813685248)), (8110263833052825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2129788094295987/2251799813685248), (14508864883839/562949953421312)), (4192033/2251799813685248), by norm_num⟩
  | 2 => ⟨((125805732832425/140737488355328), (109781722171041/2251799813685248)), (4072933/1125899906842624), by norm_num⟩
  | 3 => ⟨((1793978775014995/2251799813685248), (196268530449593/2251799813685248)), (7678753/1125899906842624), by norm_num⟩
  | 4 => ⟨((1412131970983425/2251799813685248), (312729022970929/2251799813685248)), (27147383/2251799813685248), by norm_num⟩
  | 5 => ⟨((842134034357925/2251799813685248), (392232603367101/2251799813685248)), (20794683/1125899906842624), by norm_num⟩
  | 6 => ⟨((246621974699855/2251799813685248), (1173505469439279/9007199254740992)), (91191991/4503599627370496), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29708395/16777216), (-1235720697/33554432)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-60615489/33554432), (-1260650635/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((366751905726085/2251799813685248), (94997632344671/4503599627370496)), (12828275/1125899906842624), by norm_num⟩
  | 1 => ⟨((-63183865/134217728), (-130929219/2147483648)), (9/268435456), by norm_num⟩
  | 2 => ⟨((182624859/268435456), (94608529/1073741824)), (53/1073741824), by norm_num⟩
  | 3 => ⟨((-175951245/268435456), (-182302547/2147483648)), (13/268435456), by norm_num⟩
  | 4 => ⟨((1017129019/2147483648), (131730533/2147483648)), (77/2147483648), by norm_num⟩
  | 5 => ⟨((-1175952397/4294967296), (-152300085/4294967296)), (91/4294967296), by norm_num⟩
  | 6 => ⟨((566489933/4294967296), (146734621/8589934592)), (45/4294967296), by norm_num⟩
  | 7 => ⟨((-467819001/8589934592), (-242352917/34359738368)), (151/34359738368), by norm_num⟩
  | 8 => ⟨((1352170829/68719476736), (175122507/68719476736)), (111/68719476736), by norm_num⟩
  | 9 => ⟨((-1737011723/274877906944), (-112482033/137438953472)), (9/17179869184), by norm_num⟩
  | 10 => ⟨((502060963/274877906944), (130045957/549755813888)), (85/549755813888), by norm_num⟩
  | 11 => ⟨((-1055376603/2199023255552), (-136684059/2199023255552)), (91/2199023255552), by norm_num⟩
  | 12 => ⟨((1016810243/8796093022208), (4115289/274877906944)), (89/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197702827769549/1267650600228229401496703205376), (167770128781/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779182508549069/633825300114114700748351602688), (12414692935/39614081257132168796771975168)), (23055/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59068977403679/1237940039285380274899124224), (55857260067/9903520314283042199192993792)), (103749/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890011410240733/2475880078570760549798248448), (237349613969/2475880078570760549798248448)), (55117/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771677626894277/154742504910672534362390528), (118650210325/77371252455336267181195264)), (27559/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193751237029091/1208925819614629174706176), (222416890873/9671406556917033397649408)), (25837/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629594030335693/302231454903657293676544), (194562542247/604462909807314587353088)), (1413/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1888440967099685/75557863725914323419136), (39508277591/9444732965739290427392)), (73477/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298026087104849/4722366482869645213696), (236964028365/4722366482869645213696)), (110219/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622117141604723/590295810358705651712), (162843221563/295147905179352825856)), (151555/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912155379722057/36893488147419103232), (203449761491/36893488147419103232)), (189451/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227949667767251/1152921504606846976), (457475416665/9223372036854775808)), (106571/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594845579768583/1152921504606846976), (228558754051/576460752303423488)), (106577/576460752303423488), by norm_num⟩
  | 5 => ⟨((149416589322869/18014398509481984), (399575549985/144115188075855872)), (46631/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492764723803651/36028797018963968), (37409983039/2251799813685248)), (139907/18014398509481984), by norm_num⟩
  | 3 => ⟨((372666443351633/2251799813685248), (373397742971/4503599627370496)), (349817/9007199254740992), by norm_num⟩
  | 2 => ⟨((557690270637271/1125899906842624), (1489386909261/4503599627370496)), (699783/4503599627370496), by norm_num⟩
  | 1 => ⟨((138769704011029/140737488355328), (1111799882267/1125899906842624)), (525027/1125899906842624), by norm_num⟩
  | 0 => ⟨((136820255236433/140737488355328), (4405454000431/2251799813685248)), (1050827/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((136820255236433/140737488355328), (4405454000431/2251799813685248)), (4008586887839889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064092113572611/1125899906842624), (4282834288257/1125899906842624)), (4094539/2251799813685248), by norm_num⟩
  | 2 => ⟨((125707631359649/140737488355328), (16190889304371/2251799813685248)), (7770679/2251799813685248), by norm_num⟩
  | 3 => ⟨((112275590272415/140737488355328), (7230903321651/562949953421312)), (3498347/562949953421312), by norm_num⟩
  | 4 => ⟨((716371476888825/1125899906842624), (46148553487975/2251799813685248)), (11343191/1125899906842624), by norm_num⟩
  | 5 => ⟨((1821318813642201/4503599627370496), (58725482109991/2251799813685248)), (59598013/4503599627370496), by norm_num⟩
  | 6 => ⟨((366751905726085/2251799813685248), (94997632344671/4503599627370496)), (12828275/1125899906842624), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60615489/33554432), (-1260650635/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-61749361/33554432), (-642116167/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((600458544468185/4503599627370496), (-388267434772493/4503599627370496)), (141565893/9007199254740992), by norm_num⟩
  | 1 => ⟨((-421527277/1073741824), (272567217/1073741824)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((1241161345/2147483648), (-401278769/1073741824)), (151/2147483648), by norm_num⟩
  | 3 => ⟨((-609087307/1073741824), (787693899/2147483648)), (151/2147483648), by norm_num⟩
  | 4 => ⟨((224177551/536870912), (-579829155/2147483648)), (113/2147483648), by norm_num⟩
  | 5 => ⟨((-1056123391/4294967296), (341454313/2147483648)), (135/4294967296), by norm_num⟩
  | 6 => ⟨((518281813/4294967296), (-335130463/4294967296)), (135/8589934592), by norm_num⟩
  | 7 => ⟨((-436014049/8589934592), (70483657/2147483648)), (29/4294967296), by norm_num⟩
  | 8 => ⟨((1283816761/68719476736), (-207534827/17179869184)), (173/68719476736), by norm_num⟩
  | 9 => ⟨((-210006673/34359738368), (135794141/34359738368)), (115/137438953472), by norm_num⟩
  | 10 => ⟨((494681467/274877906944), (-639740099/549755813888)), (137/549755813888), by norm_num⟩
  | 11 => ⟨((-1059315923/2199023255552), (42810811/137438953472)), (149/2199023255552), by norm_num⟩
  | 12 => ⟨((129962129/1099511627776), (-672287043/8796093022208)), (149/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (-373845763207/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889564998034709/316912650057057350374175801344), (-885196270531/633825300114114700748351602688)), (92287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890148187029209/39614081257132168796771975168), (-995684850359/39614081257132168796771975168)), (103829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944974304769225/1237940039285380274899124224), (-1057716557297/2475880078570760549798248448)), (110325/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771614806304015/154742504910672534362390528), (-1057493206045/154742504910672534362390528)), (27583/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549950980814251/9671406556917033397649408), (-123895329325/1208925819614629174706176)), (25861/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259136488582977/604462909807314587353088), (-867030131933/604462909807314587353088)), (90521/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944178561468317/37778931862957161709568), (-704239709429/37778931862957161709568)), (18389/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297963169441013/4722366482869645213696), (-1055970741227/4722366482869645213696)), (110347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622030573757969/590295810358705651712), (-1451328221365/590295810358705651712)), (151747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912101232835703/36893488147419103232), (-1813213461191/73786976294838206464)), (94857/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823475396394477/9223372036854775808), (-1019282047315/4611686018427387904)), (6671/288230376151711744), by norm_num⟩
  | 6 => ⟨((1594723490265599/1152921504606846976), (-1018469507727/576460752303423488)), (213525/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195225724953251/144115188075855872), (-1780495117535/144115188075855872)), (186895/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492603917765181/36028797018963968), (-2667093862919/36028797018963968)), (280463/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490464205393675/9007199254740992), (-3327491408225/9007199254740992)), (350791/9007199254740992), by norm_num⟩
  | 2 => ⟨((557589068600929/1125899906842624), (-51842914145/35184372088832)), (351109/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219703904014171/2251799813685248), (-1238280948829/281474976710656)), (527463/1125899906842624), by norm_num⟩
  | 0 => ⟨((2187884964961765/2251799813685248), (-4905730246621/562949953421312)), (1058141/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2187884964961765/2251799813685248), (-4905730246621/562949953421312)), (4036487583640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2125613268012617/2251799813685248), (-19065946064139/1125899906842624)), (64833/35184372088832), by norm_num⟩
  | 2 => ⟨((1002926125249547/1125899906842624), (-35995053978463/1125899906842624)), (3987057/1125899906842624), by norm_num⟩
  | 3 => ⟨((892233104108049/1125899906842624), (-128254313888363/2251799813685248)), (7358093/1125899906842624), by norm_num⟩
  | 4 => ⟨((1406817098030439/2251799813685248), (-101636694257101/1125899906842624)), (25000403/2251799813685248), by norm_num⟩
  | 5 => ⟨((430281205517411/1125899906842624), (-507982062700953/4503599627370496)), (71503535/4503599627370496), by norm_num⟩
  | 6 => ⟨((600458544468185/4503599627370496), (-388267434772493/4503599627370496)), (141565893/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-642116167/16777216)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-62825059/33554432), (-1306604171/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((448886695974393/9007199254740992), (-655113088820665/4503599627370496)), (197442453/9007199254740992), by norm_num⟩
  | 1 => ⟨((-40076505/268435456), (935813629/2147483648)), (143/2147483648), by norm_num⟩
  | 2 => ⟨((240116959/1073741824), (-1401723545/2147483648)), (27/268435456), by norm_num⟩
  | 3 => ⟨((-479550749/2147483648), (87483093/134217728)), (109/1073741824), by norm_num⟩
  | 4 => ⟨((179575707/1073741824), (-262075925/536870912)), (165/2147483648), by norm_num⟩
  | 5 => ⟨((-430368593/4294967296), (1256174891/4294967296)), (25/536870912), by norm_num⟩
  | 6 => ⟨((429756361/8589934592), (-78399243/536870912)), (101/4294967296), by norm_num⟩
  | 7 => ⟨((-91959643/4294967296), (67103755/1073741824)), (175/17179869184), by norm_num⟩
  | 8 => ⟨((137743235/17179869184), (-402049769/17179869184)), (133/34359738368), by norm_num⟩
  | 9 => ⟨((-45849095/17179869184), (133825941/17179869184)), (179/137438953472), by norm_num⟩
  | 10 => ⟨((109881291/137438953472), (-641450705/274877906944)), (217/549755813888), by norm_num⟩
  | 11 => ⟨((-239399949/1099511627776), (349384469/549755813888)), (239/2199023255552), by norm_num⟩
  | 12 => ⟨((478118769/8796093022208), (-1395549773/8796093022208)), (15/549755813888), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581536844765651/10141204801825835211973625643008), (-101011581721/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779079018915691/633825300114114700748351602688), (-1913309825083/633825300114114700748351602688)), (92389/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890090759068383/39614081257132168796771975168), (-67253687535/1237940039285380274899124224)), (103949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118117968144733/154742504910672534362390528), (-285773554245/309485009821345068724781056)), (27615/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885776786201991/77371252455336267181195264), (-71428031339/4835703278458516698824704)), (27619/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387473363065625/2417851639229258349412352), (-1071159461227/4835703278458516698824704)), (25897/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259086029413195/604462909807314587353088), (-937003591617/302231454903657293676544)), (2833/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((944137449399947/37778931862957161709568), (-3044283464669/75557863725914323419136)), (36837/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297901302028017/4722366482869645213696), (-1141178485921/2361183241434822606848)), (55269/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202743147814701/73786976294838206464), (-392106376929/73786976294838206464)), (152035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824095241880221/73786976294838206464), (-3918980039471/73786976294838206464)), (95055/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823354104053357/9223372036854775808), (-1101497260645/2305843009213693952)), (106983/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594601367366661/1152921504606846976), (-1100603026027/288230376151711744)), (214081/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195117934978547/144115188075855872), (-1924044943359/72057594037927936)), (187451/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492440372768185/36028797018963968), (-5764101793955/36028797018963968)), (70359/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490256529959497/9007199254740992), (-3595544125749/4503599627370496)), (352251/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229931234365665/4503599627370496), (-3585033684619/1125899906842624)), (44117/281474976710656), by norm_num⟩
  | 1 => ⟨((1109521136234343/1125899906842624), (-21405360562329/2251799813685248)), (1062239/2251799813685248), by norm_num⟩
  | 0 => ⟨((546616580247897/562949953421312), (-21196464617391/1125899906842624)), (2138249/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((546616580247897/562949953421312), (-21196464617391/1125899906842624)), (8156772622115325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2122230308102051/2251799813685248), (-41162945061415/1125899906842624)), (4232931/2251799813685248), by norm_num⟩
  | 2 => ⟨((1997106448411405/2251799813685248), (-19397205970345/281474976710656)), (4144123/1125899906842624), by norm_num⟩
  | 3 => ⟨((1760526863812665/2251799813685248), (-34406508863807/281474976710656)), (7921957/1125899906842624), by norm_num⟩
  | 4 => ⟨((671394303634179/1125899906842624), (-26900074676535/140737488355328)), (28647935/2251799813685248), by norm_num⟩
  | 5 => ⟨((718463535466579/2251799813685248), (-128327975127431/562949953421312)), (22558945/1125899906842624), by norm_num⟩
  | 6 => ⟨((448886695974393/9007199254740992), (-655113088820665/4503599627370496)), (197442453/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-62825059/33554432), (-1306604171/33554432)), (1/16777216), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-63848263/33554432), (-663942127/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-402291910513605/9007199254740992), (-1281742141302585/9007199254740992)), (232039091/9007199254740992), by norm_num⟩
  | 1 => ⟨((73002979/536870912), (930379083/2147483648)), (85/1073741824), by norm_num⟩
  | 2 => ⟨((-444518415/2147483648), (-1416279997/2147483648)), (261/2147483648), by norm_num⟩
  | 3 => ⟨((225557715/1073741824), (1437298743/2147483648)), (267/2147483648), by norm_num⟩
  | 4 => ⟨((-171678881/1073741824), (-273493017/536870912)), (205/2147483648), by norm_num⟩
  | 5 => ⟨((104536041/1073741824), (1332249003/4294967296)), (63/1073741824), by norm_num⟩
  | 6 => ⟨((-424349763/8589934592), (-1352020661/8589934592)), (129/4294967296), by norm_num⟩
  | 7 => ⟨((369126393/17179869184), (1176073497/17179869184)), (113/8589934592), by norm_num⟩
  | 8 => ⟨((-280953397/34359738368), (-447572769/17179869184)), (87/17179869184), by norm_num⟩
  | 9 => ⟨((380163965/137438953472), (302810075/34359738368)), (237/137438953472), by norm_num⟩
  | 10 => ⟨((-462967089/549755813888), (-1475059309/549755813888)), (291/549755813888), by norm_num⟩
  | 11 => ⟨((512550433/2199023255552), (1633036787/2199023255552)), (81/549755813888), by norm_num⟩
  | 12 => ⟨((-260078549/4398046511104), (-414318095/2199023255552)), (83/2199023255552), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395374280778559/2535301200456458802993406410752), (-2442296267815/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222378685293549/79228162514264337593543950336), (-2891150126423/633825300114114700748351602688)), (92485/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236254362033537/4951760157141521099596496896), (-406499213887/4951760157141521099596496896)), (813/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((944913981044749/1237940039285380274899124224), (-3454571794521/2475880078570760549798248448)), (110589/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55359182767873/4835703278458516698824704), (-3453816465853/154742504910672534362390528)), (27653/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549837253465655/9671406556917033397649408), (-809287639707/2417851639229258349412352)), (103725/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629518323952191/302231454903657293676544), (-2831704539609/604462909807314587353088)), (90785/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944097132486639/37778931862957161709568), (-2300008066225/37778931862957161709568)), (36893/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648920243347805/2361183241434822606848), (-3448696702363/4722366482869645213696)), (865/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1621861009564367/590295810358705651712), (-4739821157001/590295810358705651712)), (38077/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823989198874869/73786976294838206464), (-1480393119481/18446744073709551616)), (95243/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823233670415689/9223372036854775808), (-6657365603939/9223372036854775808)), (53609/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797239758537245/576460752303423488), (-3325932172871/576460752303423488)), (107305/576460752303423488), by norm_num⟩
  | 5 => ⟨((298752431388865/36028797018963968), (-5814196558537/144115188075855872)), (187981/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492274886085233/36028797018963968), (-4354467888951/18014398509481984)), (70591/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490044138261763/9007199254740992), (-5432282414457/4503599627370496)), (353643/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229489925254087/4503599627370496), (-21664408813689/4503599627370496)), (709353/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109169626980265/1125899906842624), (-16167569747193/1125899906842624)), (267303/562949953421312), by norm_num⟩
  | 0 => ⟨((2184897616062517/2251799813685248), (-16006588508851/562949953421312)), (1079609/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2184897616062517/2251799813685248), (-16006588508851/562949953421312)), (4118381504539107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1059081315682909/1125899906842624), (-124248192443169/2251799813685248)), (2156461/1125899906842624), by norm_num⟩
  | 2 => ⟨((124100044673591/140737488355328), (-233748912002225/2251799813685248)), (8589879/2251799813685248), by norm_num⟩
  | 3 => ⟨((1726606255597627/2251799813685248), (-206116016143763/1125899906842624)), (16932185/2251799813685248), by norm_num⟩
  | 4 => ⟨((1248438647316587/2251799813685248), (-632172008701351/2251799813685248)), (32165565/2251799813685248), by norm_num⟩
  | 5 => ⟨((514680568176903/2251799813685248), (-350487624440687/1125899906842624)), (53726717/2251799813685248), by norm_num⟩
  | 6 => ⟨((-402291910513605/9007199254740992), (-1281742141302585/9007199254740992)), (232039091/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-63848263/33554432), (-663942127/16777216)), (1/16777216), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile033Terms2
