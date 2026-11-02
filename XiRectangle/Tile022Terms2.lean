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
namespace Reinmann.XiRectangle.Tile022Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/128))
  have he : value ((3/4), (1269/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-279097919/134217728), (-922331405/33554432)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-198770399124863/2251799813685248), (-797179941756511/9007199254740992)), (38407513/9007199254740992), by norm_num⟩
  | 1 => ⟨((4204624687/17179869184), (526965169/2147483648)), (205/17179869184), by norm_num⟩
  | 2 => ⟨((-2914423747/8589934592), (-2922115369/8589934592)), (9/536870912), by norm_num⟩
  | 3 => ⟨((2693499471/8589934592), (2700608039/8589934592)), (135/8589934592), by norm_num⟩
  | 4 => ⟨((-3733983129/17179869184), (-7312183/33554432)), (95/8589934592), by norm_num⟩
  | 5 => ⟨((4141119805/34359738368), (2076024435/17179869184)), (213/34359738368), by norm_num⟩
  | 6 => ⟨((-956801839/17179869184), (-3837307957/68719476736)), (199/68719476736), by norm_num⟩
  | 7 => ⟨((3031791987/137438953472), (1519896681/68719476736)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((-525369517/68719476736), (-4214048397/549755813888)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((2589570841/1099511627776), (2596405125/1099511627776)), (35/274877906944), by norm_num⟩
  | 10 => ⟨((-717981491/1099511627776), (-2879505427/4398046511104)), (157/4398046511104), by norm_num⟩
  | 11 => ⟨((723879049/4398046511104), (2903157917/17592186044416)), (5/549755813888), by norm_num⟩
  | 12 => ⟨((-83625787/2199023255552), (-2683087633/70368744177664)), (75/35184372088832), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98829191395547/633825300114114700748351602688), (-3067489761777/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444688649348201/158456325028528675187087900672), (-3630185760793/633825300114114700748351602688)), (17355/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889725560642691/39614081257132168796771975168), (-2041601030703/19807040628566084398385987584)), (19529/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889499169599509/2475880078570760549798248448), (-4337480293267/2475880078570760549798248448)), (10377/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221395614680103/19342813113834066795298816), (-4336443301373/154742504910672534362390528)), (2595/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549528733365967/9671406556917033397649408), (-2032156996827/4835703278458516698824704)), (4867/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629383272906257/302231454903657293676544), (-3555173370613/604462909807314587353088)), (17041/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887755073779323/75557863725914323419136), (-1443773033737/18889465931478580854784)), (13851/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648755426378067/2361183241434822606848), (-2164756533349/2361183241434822606848)), (20787/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101337960790527/36893488147419103232), (-371884160493/36893488147419103232)), (28597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823421568466347/73786976294838206464), (-1858320987449/18446744073709551616)), (17885/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911297142322985/4611686018427387904), (-1044549755321/1152921504606846976)), (40275/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398459783013805/288230376151711744), (-8348843915335/1152921504606846976)), (10079/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194448268216537/144115188075855872), (-1824186340477/36028797018963968)), (35323/144115188075855872), by norm_num⟩
  | 4 => ⟨((372857617110113/9007199254740992), (-42688067363/140737488355328)), (13269/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488984731633555/9007199254740992), (-6815254586175/4503599627370496)), (66507/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113679770627403/2251799813685248), (-1698257583893/281474976710656)), (66751/2251799813685248), by norm_num⟩
  | 1 => ⟨((69222345020293/70368744177664), (-20268180234761/1125899906842624)), (100737/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089168185279489/1125899906842624), (-40093982011909/1125899906842624)), (203925/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089168185279489/1125899906842624), (-40093982011909/1125899906842624)), (777912144187545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052207040103287/1125899906842624), (-77571886032039/1125899906842624)), (409069/1125899906842624), by norm_num⟩
  | 2 => ⟨((1955986053552921/2251799813685248), (-289978475354507/2251799813685248)), (1641915/2251799813685248), by norm_num⟩
  | 3 => ⟨((830845153903993/1125899906842624), (-503769340575349/2251799813685248)), (1637661/1125899906842624), by norm_num⟩
  | 4 => ⟨((1113523109523519/2251799813685248), (-92937727580997/281474976710656)), (1574869/562949953421312), by norm_num⟩
  | 5 => ⟨((610301816316003/4503599627370496), (-1470657301297841/4503599627370496)), (2597541/562949953421312), by norm_num⟩
  | 6 => ⟨((-198770399124863/2251799813685248), (-797179941756511/9007199254740992)), (38407513/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/134217728), (-922331405/33554432)), (3/268435456), by norm_num⟩, -4, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-570401187/268435456), (-7539990691/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-528680252864715/4503599627370496), (-198618240503877/9007199254740992)), (22887193/9007199254740992), by norm_num⟩
  | 1 => ⟨((178559297/536870912), (536659097/8589934592)), (63/8589934592), by norm_num⟩
  | 2 => ⟨((-505896583/1073741824), (-760234857/8589934592)), (91/8589934592), by norm_num⟩
  | 3 => ⟨((1911083933/4294967296), (717969181/8589934592)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((-5414508501/17179869184), (-254269983/4294967296)), (63/8589934592), by norm_num⟩
  | 5 => ⟨((6136183095/34359738368), (576320887/17179869184)), (145/34359738368), by norm_num⟩
  | 6 => ⟨((-5795038609/68719476736), (-544280009/34359738368)), (139/68719476736), by norm_num⟩
  | 7 => ⟨((2345511531/68719476736), (440588967/68719476736)), (57/68719476736), by norm_num⟩
  | 8 => ⟨((-6645334569/549755813888), (-1248282541/549755813888)), (41/137438953472), by norm_num⟩
  | 9 => ⟨((4183922351/1099511627776), (785922389/1099511627776)), (105/1099511627776), by norm_num⟩
  | 10 => ⟨((-2370788927/2199023255552), (-55667145/274877906944)), (121/4398046511104), by norm_num⟩
  | 11 => ⟨((4885055145/17592186044416), (917625589/17592186044416)), (127/17592186044416), by norm_num⟩
  | 12 => ⟨((-144170869/2199023255552), (-108326211/8796093022208)), (121/70368744177664), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (-962601659399/2535301200456458802993406410752)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222335055894277/79228162514264337593543950336), (-2278188933651/316912650057057350374175801344)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889641928512887/39614081257132168796771975168), (-5124944006051/39614081257132168796771975168)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889410030276297/2475880078570760549798248448), (-2722034662713/1237940039285380274899124224)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885537731579877/77371252455336267181195264), (-170085553151/4835703278458516698824704)), (433/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549444535569877/9671406556917033397649408), (-5101151910835/9671406556917033397649408)), (3249/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629346269298807/302231454903657293676544), (-2231046713055/302231454903657293676544)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887634186097759/75557863725914323419136), (-3624125018619/37778931862957161709568)), (18495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297419639843435/4722366482869645213696), (-5433867620321/4722366482869645213696)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202660133352993/73786976294838206464), (-7467798879239/590295810358705651712)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823262355920995/73786976294838206464), (-9329096267615/73786976294838206464)), (5973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822413344405947/9223372036854775808), (-2621865872191/2305843009213693952)), (13453/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593655913635287/1152921504606846976), (-10477754445351/1152921504606846976)), (6735/288230376151711744), by norm_num⟩
  | 5 => ⟨((18660709301551/2251799813685248), (-4578558453565/72057594037927936)), (5903/36028797018963968), by norm_num⟩
  | 4 => ⟨((372795265207835/9007199254740992), (-857115626999/2251799813685248)), (17747/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488664084747393/9007199254740992), (-4276035840645/2251799813685248)), (5563/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113345861642565/2251799813685248), (-17046940118781/2251799813685248)), (11177/562949953421312), by norm_num⟩
  | 1 => ⟨((1107023742507583/1125899906842624), (-12713789956055/562949953421312)), (67573/1125899906842624), by norm_num⟩
  | 0 => ⟨((271992603498555/281474976710656), (-25142456950003/562949953421312)), (8575/70368744177664), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((271992603498555/281474976710656), (-25142456950003/562949953421312)), (32711029321169831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1049072872270805/1125899906842624), (-12147726956225/140737488355328)), (69353/281474976710656), by norm_num⟩
  | 2 => ⟨((242274996962505/281474976710656), (-90550506183209/562949953421312)), (70607/140737488355328), by norm_num⟩
  | 3 => ⟨((805006914258015/1125899906842624), (-77939871838205/281474976710656)), (72131/70368744177664), by norm_num⟩
  | 4 => ⟨((978492227774407/2251799813685248), (-111452421915705/281474976710656)), (572367/281474976710656), by norm_num⟩
  | 5 => ⟨((72147589839683/2251799813685248), (-387442357702921/1125899906842624)), (1901395/562949953421312), by norm_num⟩
  | 6 => ⟨((-528680252864715/4503599627370496), (-198618240503877/9007199254740992)), (22887193/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-7539990691/268435456)), (1/134217728), by norm_num⟩, -4, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-72738587/33554432), (-7692105571/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-956801637655025/9007199254740992), (95815041333459/2251799813685248)), (5706037/2251799813685248), by norm_num⟩
  | 1 => ⟨((5274796355/17179869184), (-2112892833/17179869184)), (1/134217728), by norm_num⟩
  | 2 => ⟨((-3811530603/8589934592), (1526761443/8589934592)), (47/4294967296), by norm_num⟩
  | 3 => ⟨((3672246803/8589934592), (-1470969385/8589934592)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((-663384903/2147483648), (265728023/2147483648)), (17/2147483648), by norm_num⟩
  | 5 => ⟨((3067886381/17179869184), (-1228884437/17179869184)), (5/1073741824), by norm_num⟩
  | 6 => ⟨((-369472173/4294967296), (2367955247/68719476736)), (39/17179869184), by norm_num⟩
  | 7 => ⟨((610235391/17179869184), (-1955505991/137438953472)), (131/137438953472), by norm_num⟩
  | 8 => ⟨((-440951785/34359738368), (706517411/137438953472)), (3/8589934592), by norm_num⟩
  | 9 => ⟨((4531607417/1099511627776), (-1815198197/1099511627776)), (125/1099511627776), by norm_num⟩
  | 10 => ⟨((-5239212039/4398046511104), (1049319521/2199023255552)), (147/4398046511104), by norm_num⟩
  | 11 => ⟨((2753321911/8796093022208), (-275720319/2199023255552)), (157/17592186044416), by norm_num⟩
  | 12 => ⟨((-663176991/8796093022208), (265644741/8796093022208)), (77/35184372088832), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996579415/5070602400912917605986812821504), (3595990084075/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778615789855979/633825300114114700748351602688), (531876625971/79228162514264337593543950336)), (5789/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889569284090905/39614081257132168796771975168), (2392980134755/19807040628566084398385987584)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889332967325335/2475880078570760549798248448), (5083955651099/2475880078570760549798248448)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770998537103445/154742504910672534362390528), (635335964663/19342813113834066795298816)), (13851/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549372562765133/9671406556917033397649408), (2381836381939/4835703278458516698824704)), (6495/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629314853839719/302231454903657293676544), (2083433465727/302231454903657293676544)), (11371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887532358081921/75557863725914323419136), (6768634129725/75557863725914323419136)), (18487/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162167938355563/590295810358705651712), (2537133520419/2361183241434822606848)), (13873/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810588385187339/295147905179352825856), (3486764605859/295147905179352825856)), (19087/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823132564389071/73786976294838206464), (2177882799443/18446744073709551616)), (11939/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28472939439259/144115188075855872), (9793077324933/9223372036854775808)), (26887/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49797240182461/36028797018963968), (9783837233421/1152921504606846976)), (3365/144115188075855872), by norm_num⟩
  | 5 => ⟨((298540077626077/36028797018963968), (8550467982433/144115188075855872)), (23591/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490995657615003/36028797018963968), (6402468283543/18014398509481984)), (35459/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488436211265043/9007199254740992), (499058197741/281474976710656)), (22225/4503599627370496), by norm_num⟩
  | 2 => ⟨((278280946535093/562949953421312), (15915462064689/2251799813685248)), (44641/2251799813685248), by norm_num⟩
  | 1 => ⟨((553352522185365/562949953421312), (23737411182401/1125899906842624)), (67439/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087390199673101/1125899906842624), (5866626553535/140737488355328)), (136795/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1087390199673101/1125899906842624), (5866626553535/140737488355328)), (521831516746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((65515078844753/70368744177664), (90655479133601/1125899906842624)), (137819/562949953421312), by norm_num⟩
  | 2 => ⟨((484319840431541/562949953421312), (21100635419013/140737488355328)), (69705/140737488355328), by norm_num⟩
  | 3 => ⟨((808036016032985/1125899906842624), (72613604936155/281474976710656)), (2253433/2251799813685248), by norm_num⟩
  | 4 => ⟨((504981330757625/1125899906842624), (104226686023885/281474976710656)), (2198575/1125899906842624), by norm_num⟩
  | 5 => ⟨((288462271461035/4503599627370496), (1495906491550119/4503599627370496)), (7200783/2251799813685248), by norm_num⟩
  | 6 => ⟨((-956801637655025/9007199254740992), (95815041333459/2251799813685248)), (5706037/2251799813685248), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72738587/33554432), (-7692105571/268435456)), (1/134217728), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-592793865/268435456), (-7835993903/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-300977274238249/4503599627370496), (392826787347005/4503599627370496)), (22443465/9007199254740992), by norm_num⟩
  | 1 => ⟨((3380619881/17179869184), (-551535847/2147483648)), (1/134217728), by norm_num⟩
  | 2 => ⟨((-1244253619/4294967296), (811981823/2147483648)), (3/268435456), by norm_num⟩
  | 3 => ⟨((2442419237/8589934592), (-3187774573/8589934592)), (3/268435456), by norm_num⟩
  | 4 => ⟨((-1797888601/8589934592), (4693103855/17179869184)), (9/1073741824), by norm_num⟩
  | 5 => ⟨((2117509311/17179869184), (-2763711585/17179869184)), (87/17179869184), by norm_num⟩
  | 6 => ⟨((-1039146159/17179869184), (1356263353/17179869184)), (87/34359738368), by norm_num⟩
  | 7 => ⟨((1748401403/68719476736), (-4563925351/137438953472)), (149/137438953472), by norm_num⟩
  | 8 => ⟨((-2574030621/274877906944), (3359549925/274877906944)), (111/274877906944), by norm_num⟩
  | 9 => ⟨((421059783/137438953472), (-4396439889/1099511627776)), (37/274877906944), by norm_num⟩
  | 10 => ⟨((-495913935/549755813888), (647252449/549755813888)), (89/2199023255552), by norm_num⟩
  | 11 => ⟨((530977571/2199023255552), (-2772065949/8796093022208)), (97/8796093022208), by norm_num⟩
  | 12 => ⟨((-2084574743/35184372088832), (340090793/4398046511104)), (97/35184372088832), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (2897756622525/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222319586170265/79228162514264337593543950336), (857146887613/158456325028528675187087900672)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944751500515979/19807040628566084398385987584), (3856406596601/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889262807966701/2475880078570760549798248448), (2048253868223/1237940039285380274899124224)), (13833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885464338611739/77371252455336267181195264), (4095468137103/154742504910672534362390528)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774653693562335/4835703278458516698824704), (3838397052697/9671406556917033397649408)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258572996767273/604462909807314587353088), (3357493374547/604462909807314587353088)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887440798199135/75557863725914323419136), (1363464309949/18889465931478580854784)), (18463/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648637678694025/2361183241434822606848), (2044291358101/2361183241434822606848)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202635488715241/73786976294838206464), (5618860750361/590295810358705651712)), (9529/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823017754290285/73786976294838206464), (7019167158661/73786976294838206464)), (11919/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822140700582793/9223372036854775808), (7890504146409/9223372036854775808)), (13419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199173303850765/144115188075855872), (3941467629621/576460752303423488)), (1679/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194053146700159/144115188075855872), (6889059880511/144115188075855872)), (23535/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490839767595373/36028797018963968), (10316589195057/36028797018963968)), (35361/36028797018963968), by norm_num⟩
  | 3 => ⟨((744124908474497/4503599627370496), (3216505528029/2251799813685248)), (22151/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225900071474365/4503599627370496), (12821523966301/2251799813685248)), (5557/281474976710656), by norm_num⟩
  | 1 => ⟨((2212951649074501/2251799813685248), (4780324394447/281474976710656)), (134137/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174112324286167/2251799813685248), (75600367211593/2251799813685248)), (135683/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2174112324286167/2251799813685248), (75600367211593/2251799813685248)), (517589573386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096566912564089/2251799813685248), (145984282507147/2251799813685248)), (271115/1125899906842624), by norm_num⟩
  | 2 => ⟨((1942571174193559/2251799813685248), (2123758228021/17592186044416)), (1080007/2251799813685248), by norm_num⟩
  | 3 => ⟨((1642990280985621/2251799813685248), (469020905565001/2251799813685248)), (2124151/2251799813685248), by norm_num⟩
  | 4 => ⟨((1101090975533213/2251799813685248), (42776714915947/140737488355328)), (1992287/1125899906842624), by norm_num⟩
  | 5 => ⟨((82596198504773/562949953421312), (1338692492166337/4503599627370496)), (6318973/2251799813685248), by norm_num⟩
  | 6 => ⟨((-300977274238249/4503599627370496), (392826787347005/4503599627370496)), (22443465/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-7835993903/268435456)), (1/134217728), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-603120569/268435456), (-996562503/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-137852546323797/9007199254740992), (1884731926940507/18014398509481984)), (39946073/18014398509481984), by norm_num⟩
  | 1 => ⟨((98459559/2147483648), (-5384590397/17179869184)), (29/4294967296), by norm_num⟩
  | 2 => ⟨((-589916957/8589934592), (252043613/536870912)), (11/1073741824), by norm_num⟩
  | 3 => ⟨((147269439/2147483648), (-4026960991/8589934592)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((-882359623/17179869184), (3015924251/8589934592)), (137/17179869184), by norm_num⟩
  | 5 => ⟨((33041415/1073741824), (-3613960645/17179869184)), (167/34359738368), by norm_num⟩
  | 6 => ⟨((-1055821155/68719476736), (3608819513/34359738368)), (169/68719476736), by norm_num⟩
  | 7 => ⟨((903702145/137438953472), (-6177746905/137438953472)), (147/137438953472), by norm_num⟩
  | 8 => ⟨((-169203105/68719476736), (4626718945/274877906944)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((225283201/274877906944), (-12031607/2147483648)), (151/1099511627776), by norm_num⟩
  | 10 => ⟨((-1079821049/4398046511104), (7381703351/4398046511104)), (23/549755813888), by norm_num⟩
  | 11 => ⟨((147038853/2199023255552), (-4020655811/8796093022208)), (51/4398046511104), by norm_num⟩
  | 12 => ⟨((-587318717/35184372088832), (1003734031/8796093022208)), (13/4398046511104), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49407783133909/316912650057057350374175801344), (1117673063193/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222312493648655/79228162514264337593543950336), (2644664201063/633825300114114700748351602688)), (5779/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889439324503083/39614081257132168796771975168), (2974660150231/39614081257132168796771975168)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889195354981989/2475880078570760549798248448), (3159851585349/2475880078570760549798248448)), (13821/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770861452803559/154742504910672534362390528), (3159036398089/154742504910672534362390528)), (13823/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549244606926609/9671406556917033397649408), (1480365363559/4835703278458516698824704)), (6481/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629259153307917/302231454903657293676544), (1294886880237/302231454903657293676544)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235919047632813/9444732965739290427392), (4206759886809/75557863725914323419136)), (2305/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648604720865629/2361183241434822606848), (3153650824565/4722366482869645213696)), (13835/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810496960222827/295147905179352825856), (4333964937893/590295810358705651712)), (19031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822906233613963/73786976294838206464), (5414000636321/73786976294838206464)), (2975/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822016565998005/9223372036854775808), (6086002412081/9223372036854775808)), (13395/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398315987750073/288230376151711744), (1520017904407/288230376151711744)), (26811/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74621739653549/9007199254740992), (41510912679/1125899906842624)), (11741/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490685504318077/36028797018963968), (7956779291955/36028797018963968)), (8817/9007199254740992), by norm_num⟩
  | 3 => ⟨((93003965568741/562949953421312), (9922706607705/9007199254740992)), (44163/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112773314538677/2251799813685248), (19775752117087/4503599627370496)), (88563/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212469403012211/2251799813685248), (14744984880509/1125899906842624)), (66719/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173337614563885/2251799813685248), (58288266642747/2251799813685248)), (134631/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2173337614563885/2251799813685248), (58288266642747/2251799813685248)), (513576511863326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096100566384439/2251799813685248), (28128628844473/562949953421312)), (133425/562949953421312), by norm_num⟩
  | 2 => ⟨((1945545088689135/2251799813685248), (209469543408565/2251799813685248)), (523465/1125899906842624), by norm_num⟩
  | 3 => ⟨((830728419944165/1125899906842624), (180980759893363/1125899906842624)), (250483/281474976710656), by norm_num⟩
  | 4 => ⟨((1167698244322235/2251799813685248), (534135795883045/2251799813685248)), (1800629/1125899906842624), by norm_num⟩
  | 5 => ⟨((239412521218977/1125899906842624), (1107930513701467/4503599627370496)), (10886837/4503599627370496), by norm_num⟩
  | 6 => ⟨((-137852546323797/9007199254740992), (1884731926940507/18014398509481984)), (39946073/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-603120569/268435456), (-996562503/33554432)), (1/134217728), by norm_num⟩, -5, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-306471663/134217728), (-1012793075/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((304862111790029/9007199254740992), (866085324221109/9007199254740992)), (8205401/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1770323829/17179869184), (-5029327779/17179869184)), (3/268435456), by norm_num⟩
  | 2 => ⟨((1347447655/8589934592), (3827975317/8589934592)), (37/2147483648), by norm_num⟩
  | 3 => ⟨((-1367444873/8589934592), (-3884785581/8589934592)), (19/1073741824), by norm_num⟩
  | 4 => ⟨((2081608299/17179869184), (2956829217/8589934592)), (117/8589934592), by norm_num⟩
  | 5 => ⟨((-1267500635/17179869184), (-1800426579/8589934592)), (9/1073741824), by norm_num⟩
  | 6 => ⟨((643155687/17179869184), (3654292745/34359738368)), (37/8589934592), by norm_num⟩
  | 7 => ⟨((-1118915383/68719476736), (-3178736073/68719476736)), (65/34359738368), by norm_num⟩
  | 8 => ⟨((1703281495/274877906944), (4838866649/274877906944)), (25/34359738368), by norm_num⟩
  | 9 => ⟨((-1152373051/549755813888), (-3273786241/549755813888)), (137/549755813888), by norm_num⟩
  | 10 => ⟨((350842561/549755813888), (3986846267/2199023255552)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((-776834945/4398046511104), (-1103458447/2199023255552)), (189/8796093022208), by norm_num⟩
  | 12 => ⟨((788363807/17592186044416), (1119834667/8796093022208)), (97/17592186044416), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288773/1267650600228229401496703205376), (200657685889/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889222685456903/316912650057057350374175801344), (949544475787/316912650057057350374175801344)), (23097/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944689019037847/19807040628566084398385987584), (1068024624903/19807040628566084398385987584)), (6497/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889130386941649/2475880078570760549798248448), (1134511821627/1237940039285380274899124224)), (27615/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885398326005611/77371252455336267181195264), (567107272327/38685626227668133590597632)), (27619/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549184033770575/9671406556917033397649408), (1063010378495/4835703278458516698824704)), (25897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258465482562555/604462909807314587353088), (1859636872387/604462909807314587353088)), (22665/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943633437218583/37778931862957161709568), (1510363362643/37778931862957161709568)), (36837/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648572801196519/2361183241434822606848), (2264510226839/4722366482869645213696)), (13817/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620906613119491/590295810358705651712), (778005219121/147573952589676412928)), (38009/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455699451552087/18446744073709551616), (3887506628357/73786976294838206464)), (47527/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910947777749931/4611686018427387904), (1092495806077/2305843009213693952)), (53491/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593144151244619/1152921504606846976), (4365659858141/1152921504606846976)), (3345/72057594037927936), by norm_num⟩
  | 5 => ⟨((596922184385271/72057594037927936), (238443363057/9007199254740992)), (23431/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490533016537195/36028797018963968), (714117077011/4503599627370496)), (70357/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487877566450231/9007199254740992), (7124217895755/9007199254740992)), (22015/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112594489117993/2251799813685248), (14197694169403/4503599627370496)), (176461/4503599627370496), by norm_num⟩
  | 1 => ⟨((552991994980461/562949953421312), (21170095881535/2251799813685248)), (265547/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172473589039023/2251799813685248), (5229606976729/281474976710656)), (534531/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172473589039023/2251799813685248), (5229606976729/281474976710656)), (2039073952681731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1047582281492089/1125899906842624), (80726060772903/2251799813685248)), (8213/17592186044416), by norm_num⟩
  | 2 => ⟨((1946530869421879/2251799813685248), (150221507980225/2251799813685248)), (507913/562949953421312), by norm_num⟩
  | 3 => ⟨((52269520991361/70368744177664), (129856482249219/1125899906842624)), (1891763/1125899906842624), by norm_num⟩
  | 4 => ⟨((606231169382133/1125899906842624), (385826758974295/2251799813685248)), (3246759/1125899906842624), by norm_num⟩
  | 5 => ⟨((1173463668441159/4503599627370496), (415490232924585/2251799813685248)), (9217977/2251799813685248), by norm_num⟩
  | 6 => ⟨((304862111790029/9007199254740992), (866085324221109/9007199254740992)), (8205401/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-306471663/134217728), (-1012793075/33554432)), (1/67108864), by norm_num⟩, -5, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile022Terms2
