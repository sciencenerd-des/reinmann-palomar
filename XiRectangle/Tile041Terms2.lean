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
namespace Reinmann.XiRectangle.Tile041Terms2
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
  | 0 => ⟨((-15989985/8388608), (-650756047/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((620455709562935/9007199254740992), (-1186492041643777/9007199254740992)), (89263421/4503599627370496), by norm_num⟩
  | 1 => ⟨((-102535993/536870912), (784314741/2147483648)), (15/268435456), by norm_num⟩
  | 2 => ⟨((142145069/536870912), (-1087291103/2147483648)), (21/268435456), by norm_num⟩
  | 3 => ⟨((-262739877/1073741824), (502435175/1073741824)), (157/2147483648), by norm_num⟩
  | 4 => ⟨((182117405/1073741824), (-348261525/1073741824)), (55/1073741824), by norm_num⟩
  | 5 => ⟨((-403949331/4294967296), (772468781/4294967296)), (31/1073741824), by norm_num⟩
  | 6 => ⟨((373328453/8589934592), (-89239093/1073741824)), (29/2147483648), by norm_num⟩
  | 7 => ⟨((-295738931/17179869184), (282769489/8589934592)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((102495303/17179869184), (-98000437/8589934592)), (131/68719476736), by norm_num⟩
  | 9 => ⟨((-505204127/274877906944), (966097445/274877906944)), (163/274877906944), by norm_num⟩
  | 10 => ⟨((280144653/549755813888), (-16741193/17179869184)), (183/1099511627776), by norm_num⟩
  | 11 => ⟨((-35305723/274877906944), (1080237217/4398046511104)), (187/4398046511104), by norm_num⟩
  | 12 => ⟨((65258833/2199023255552), (-998351175/17592186044416)), (175/17592186044416), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395373196929477/2535301200456458802993406410752), (-1418506538131/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779027313477011/633825300114114700748351602688), (-839597736529/316912650057057350374175801344)), (46183/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945016312975779/19807040628566084398385987584), (-1888777983731/39614081257132168796771975168)), (51961/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889825768985583/2475880078570760549798248448), (-501609068375/618970019642690137449562112)), (110429/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771491901789627/154742504910672534362390528), (-2005997273323/154742504910672534362390528)), (110443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193729461240199/1208925819614629174706176), (-1880156127369/9671406556917033397649408)), (103555/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314758885299071/151115727451828646838272), (-822335215775/302231454903657293676544)), (45313/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472048239080093/18889465931478580854784), (-1335857826941/37778931862957161709568)), (73647/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297839933371357/4722366482869645213696), (-1001511228763/2361183241434822606848)), (110495/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621860943830505/590295810358705651712), (-2752914462629/590295810358705651712)), (151969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227998769768201/9223372036854775808), (-3439281903811/73786976294838206464)), (47505/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823236179636433/9223372036854775808), (-3866634570239/9223372036854775808)), (213853/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797241905472515/576460752303423488), (-3863439919501/1152921504606846976)), (213955/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195015486437661/144115188075855872), (-3376919126643/144115188075855872)), (187325/144115188075855872), by norm_num⟩
  | 4 => ⟨((186535940618543/4503599627370496), (-2529102512753/18014398509481984)), (281215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490066910180155/9007199254740992), (-788777527411/1125899906842624)), (351919/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229556299863173/4503599627370496), (-12582903562157/4503599627370496)), (705041/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218490581227421/2251799813685248), (-18780762339747/2251799813685248)), (33143/70368744177664), by norm_num⟩
  | 0 => ⟨((2185405468810397/2251799813685248), (-2324290286051/140737488355328)), (266657/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2185405468810397/2251799813685248), (-2324290286051/140737488355328)), (1017215729833507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1060177294358795/1125899906842624), (-72184273878957/2251799813685248)), (4211177/2251799813685248), by norm_num⟩
  | 2 => ⟨((1994268311600459/2251799813685248), (-135941263892375/2251799813685248)), (4100351/1125899906842624), by norm_num⟩
  | 3 => ⟨((1757983124151025/2251799813685248), (-240788149258967/2251799813685248)), (3878945/562949953421312), by norm_num⟩
  | 4 => ⟨((1346711956163311/2251799813685248), (-375967259896035/2251799813685248)), (13772315/1125899906842624), by norm_num⟩
  | 5 => ⟨((742642264288431/2251799813685248), (-449702145768737/2251799813685248)), (21072283/1125899906842624), by norm_num⟩
  | 6 => ⟨((620455709562935/9007199254740992), (-1186492041643777/9007199254740992)), (89263421/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15989985/8388608), (-650756047/16777216)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-65358469/33554432), (-332492645/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-459982823820409/9007199254740992), (-599533931787257/4503599627370496)), (224458459/9007199254740992), by norm_num⟩
  | 1 => ⟨((38839265/268435456), (404979595/1073741824)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((-27509981/134217728), (-1147393593/2147483648)), (221/2147483648), by norm_num⟩
  | 3 => ⟨((415688775/2147483648), (1083603613/2147483648)), (211/2147483648), by norm_num⟩
  | 4 => ⟨((-147216873/1073741824), (-383760027/1073741824)), (301/4294967296), by norm_num⟩
  | 5 => ⟨((333677447/4294967296), (108727403/536870912)), (173/4294967296), by norm_num⟩
  | 6 => ⟨((-315126465/8589934592), (-102682643/1073741824)), (165/8589934592), by norm_num⟩
  | 7 => ⟨((255091573/17179869184), (664964193/17179869184)), (269/34359738368), by norm_num⟩
  | 8 => ⟨((-45170553/8589934592), (-941992713/68719476736)), (193/68719476736), by norm_num⟩
  | 9 => ⟨((227516113/137438953472), (1186162811/274877906944)), (245/274877906944), by norm_num⟩
  | 10 => ⟨((-257840675/549755813888), (-672130461/549755813888)), (35/137438953472), by norm_num⟩
  | 11 => ⟨((531285557/4398046511104), (173117181/549755813888)), (291/4398046511104), by norm_num⟩
  | 12 => ⟨((-501748443/17592186044416), (-653970543/8796093022208)), (277/17592186044416), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790719247815041/5070602400912917605986812821504), (-630822305357/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889479890581823/316912650057057350374175801344), (-373350805097/79228162514264337593543950336)), (46247/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236244559882303/4951760157141521099596496896), (-209973477305/2475880078570760549798248448)), (104075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889744637992501/2475880078570760549798248448), (-3568838944859/2475880078570760549798248448)), (110601/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885705258978535/77371252455336267181195264), (-3568040148393/154742504910672534362390528)), (55313/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96859945256529/604462909807314587353088), (-3344189088297/9671406556917033397649408)), (51869/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258968277821003/604462909807314587353088), (-1462658546519/302231454903657293676544)), (90797/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888083150701647/75557863725914323419136), (-4752050009791/75557863725914323419136)), (73797/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648878569876737/2361183241434822606848), (-3562646431389/4722366482869645213696)), (110739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202718298665719/73786976294838206464), (-306023694257/36893488147419103232)), (152335/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823845896407885/73786976294838206464), (-3058542809231/36893488147419103232)), (190523/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823072417979829/9223372036854775808), (-6877064624871/9223372036854775808)), (107241/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199289777310291/144115188075855872), (-6871247011101/1152921504606846976)), (214663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597434268882767/72057594037927936), (-6005800796241/144115188075855872)), (188033/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492063002364983/36028797018963968), (-1124453963697/4503599627370496)), (282455/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489779107312735/9007199254740992), (-5610846609929/4503599627370496)), (88445/2251799813685248), by norm_num⟩
  | 2 => ⟨((557239835871519/1125899906842624), (-22374947907647/4503599627370496)), (11089/70368744177664), by norm_num⟩
  | 1 => ⟨((2217542113106309/2251799813685248), (-8347919505315/562949953421312)), (267475/562949953421312), by norm_num⟩
  | 0 => ⟨((1091649224715675/1125899906842624), (-66102495387037/2251799813685248)), (2161291/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1091649224715675/1125899906842624), (-66102495387037/2251799813685248)), (8244670876509856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1057470240127355/1125899906842624), (-128183220200083/2251799813685248)), (2158989/1125899906842624), by norm_num⟩
  | 2 => ⟨((1979102347373267/2251799813685248), (-60196266036385/562949953421312)), (8602683/2251799813685248), by norm_num⟩
  | 3 => ⟨((1713681931586743/2251799813685248), (-423251021486647/2251799813685248)), (16961533/2251799813685248), by norm_num⟩
  | 4 => ⟨((1224604566843981/2251799813685248), (-322105732329847/1125899906842624)), (32192613/2251799813685248), by norm_num⟩
  | 5 => ⟨((240840221973603/1125899906842624), (-700687775921259/2251799813685248)), (53434655/2251799813685248), by norm_num⟩
  | 6 => ⟨((-459982823820409/9007199254740992), (-599533931787257/4503599627370496)), (224458459/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65358469/33554432), (-332492645/8388608)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-33338519/16777216), (-1356801955/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1134960567183311/9007199254740992), (-486362545086167/9007199254740992)), (109451863/4503599627370496), by norm_num⟩
  | 1 => ⟨((48882633/134217728), (163653/1048576)), (19/268435456), by norm_num⟩
  | 2 => ⟨((-1130311855/2147483648), (-242185221/1073741824)), (111/1073741824), by norm_num⟩
  | 3 => ⟨((1089007155/2147483648), (466670215/2147483648)), (27/268435456), by norm_num⟩
  | 4 => ⟨((-786908881/2147483648), (-168606301/1073741824)), (79/1073741824), by norm_num⟩
  | 5 => ⟨((454891841/2147483648), (389867913/4294967296)), (185/4294967296), by norm_num⟩
  | 6 => ⟨((-876537687/8589934592), (-93905267/2147483648)), (45/2147483648), by norm_num⟩
  | 7 => ⟨((723862793/17179869184), (310195579/17179869184)), (299/34359738368), by norm_num⟩
  | 8 => ⟨((-1046116287/68719476736), (-448290271/68719476736)), (109/34359738368), by norm_num⟩
  | 9 => ⟨((1343851099/274877906944), (575878017/274877906944)), (141/137438953472), by norm_num⟩
  | 10 => ⟨((-776845853/549755813888), (-332900311/549755813888)), (165/549755813888), by norm_num⟩
  | 11 => ⟨((816499387/2199023255552), (174946483/1099511627776)), (175/2199023255552), by norm_num⟩
  | 12 => ⟨((-49166391/549755813888), (-84276729/2199023255552)), (85/4398046511104), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581387307657611/10141204801825835211973625643008), (-3564906068827/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778894437902291/633825300114114700748351602688), (-4219490148387/633825300114114700748351602688)), (92615/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472470677675791/9903520314283042199192993792), (-2373038244697/19807040628566084398385987584)), (104219/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889665924258129/2475880078570760549798248448), (-2520840669169/1237940039285380274899124224)), (27691/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771331427780157/154742504910672534362390528), (-5040528317815/154742504910672534362390528)), (110799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193710572168593/1208925819614629174706176), (-4724270353665/9671406556917033397649408)), (103911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258902649981919/604462909807314587353088), (-4132511772323/604462909807314587353088)), (90959/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887975757145699/75557863725914323419136), (-1678258872105/18889465931478580854784)), (147877/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297675940418269/4722366482869645213696), (-2516383913519/2361183241434822606848)), (110969/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810816839179391/295147905179352825856), (-6916792107793/590295810358705651712)), (19085/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227962927109459/9223372036854775808), (-270034242313/2305843009213693952)), (95499/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822909944368815/9223372036854775808), (-4857252370749/4611686018427387904)), (53769/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99634563722751/72057594037927936), (-9706097456849/1152921504606846976)), (215331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597360464712197/72057594037927936), (-8483380789847/144115188075855872)), (188701/144115188075855872), by norm_num⟩
  | 4 => ⟨((372958871992459/9007199254740992), (-6353085757469/18014398509481984)), (141813/18014398509481984), by norm_num⟩
  | 3 => ⟨((744742036767723/4503599627370496), (-15849660962537/9007199254740992)), (177769/4503599627370496), by norm_num⟩
  | 2 => ⟨((557084375853099/1125899906842624), (-15800122962823/2251799813685248)), (357049/2251799813685248), by norm_num⟩
  | 1 => ⟨((554132611279117/562949953421312), (-23576487698199/1125899906842624)), (539361/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090481307255495/1125899906842624), (-23329541905939/562949953421312)), (1093921/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1090481307255495/1125899906842624), (-23329541905939/562949953421312)), (4172977451804732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131780410069947/140737488355328), (-90382561364991/1125899906842624)), (1104843/562949953421312), by norm_num⟩
  | 2 => ⟨((979891623137271/1125899906842624), (-169260530922353/1125899906842624)), (1123219/281474976710656), by norm_num⟩
  | 3 => ⟨((1654744724828701/2251799813685248), (-589242348704675/2251799813685248)), (18342655/2251799813685248), by norm_num⟩
  | 4 => ⟨((1061805558518275/2251799813685248), (-866014520686007/2251799813685248)), (36558029/2251799813685248), by norm_num⟩
  | 5 => ⟨((167621425211669/2251799813685248), (-1633429448272391/4503599627370496)), (15649105/562949953421312), by norm_num⟩
  | 6 => ⟨((-1134960567183311/9007199254740992), (-486362545086167/9007199254740992)), (109451863/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33338519/16777216), (-1356801955/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-67924297/33554432), (-691091129/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-279241791944259/2251799813685248), (204835579531107/4503599627370496)), (104639791/4503599627370496), by norm_num⟩
  | 1 => ⟨((784120957/2147483648), (-575185647/4294967296)), (37/536870912), by norm_num⟩
  | 2 => ⟨((-1154398155/2147483648), (26462485/134217728)), (55/536870912), by norm_num⟩
  | 3 => ⟨((283254577/536870912), (-103889563/536870912)), (109/1073741824), by norm_num⟩
  | 4 => ⟨((-417012909/1073741824), (305896479/2147483648)), (81/1073741824), by norm_num⟩
  | 5 => ⟨((982295251/4294967296), (-360277407/4294967296)), (193/4294967296), by norm_num⟩
  | 6 => ⟨((-964102809/8589934592), (353604947/8589934592)), (191/8589934592), by norm_num⟩
  | 7 => ⟨((101383639/2147483648), (-297476625/17179869184)), (163/17179869184), by norm_num⟩
  | 8 => ⟨((-597035877/34359738368), (437950885/68719476736)), (121/34359738368), by norm_num⟩
  | 9 => ⟨((781304759/137438953472), (-573119847/274877906944)), (319/274877906944), by norm_num⟩
  | 10 => ⟨((-920201675/549755813888), (337503283/549755813888)), (95/274877906944), by norm_num⟩
  | 11 => ⟨((985264611/2199023255552), (-361366481/2199023255552)), (205/2199023255552), by norm_num⟩
  | 12 => ⟨((-967017175/8796093022208), (354673851/8796093022208)), (203/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790669444000061/5070602400912917605986812821504), (908589829883/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778836754381697/633825300114114700748351602688), (2150716236497/316912650057057350374175801344)), (5789/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944908903936137/19807040628566084398385987584), (2419114542021/19807040628566084398385987584)), (104229/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889596951584597/2475880078570760549798248448), (5139553990879/2475880078570760549798248448)), (110775/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771262440044445/154742504910672534362390528), (40143410589/1208925819614629174706176)), (55405/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774809942683897/4835703278458516698824704), (1203984285825/2417851639229258349412352)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258846028547805/604462909807314587353088), (2106336519451/302231454903657293676544)), (45485/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471970929366719/18889465931478580854784), (3421604556653/37778931862957161709568)), (18487/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((81100430287569/295147905179352825856), (2565160342597/2361183241434822606848)), (13873/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405384671094235/147573952589676412928), (7050801611927/590295810358705651712)), (152703/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823584611242747/73786976294838206464), (8808419181807/73786976294838206464)), (95515/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911388100754059/4611686018427387904), (9902484575699/9223372036854775808)), (215115/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594019169021187/1152921504606846976), (9893753663801/1152921504606846976)), (215375/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194603689705737/144115188075855872), (8647216097631/144115188075855872)), (94373/72057594037927936), by norm_num⟩
  | 4 => ⟨((11653588976747/281474976710656), (3237799312589/9007199254740992)), (35463/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489263534593981/9007199254740992), (16154671661951/9007199254740992)), (44457/1125899906842624), by norm_num⟩
  | 2 => ⟨((556973798564917/1125899906842624), (16103228822917/2251799813685248)), (357197/2251799813685248), by norm_num⟩
  | 1 => ⟨((553965988455025/562949953421312), (24026392728649/1125899906842624)), (539657/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089808911987313/1125899906842624), (2971245583647/70368744177664)), (1094815/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1089808911987313/1125899906842624), (2971245583647/70368744177664)), (4176387791160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526433749821409/562949953421312), (92032050723715/1125899906842624)), (276487/140737488355328), by norm_num⟩
  | 2 => ⟨((977049617606435/1125899906842624), (86062317390371/562949953421312)), (4498445/1125899906842624), by norm_num⟩
  | 3 => ⟨((1643128416202581/2251799813685248), (37342197910111/140737488355328)), (1147859/140737488355328), by norm_num⟩
  | 4 => ⟨((65028383163645/140737488355328), (871950000338927/2251799813685248)), (4568607/281474976710656), by norm_num⟩
  | 5 => ⟨((143106857399675/2251799813685248), (1611553520933175/4503599627370496)), (124160565/4503599627370496), by norm_num⟩
  | 6 => ⟨((-279241791944259/2251799813685248), (204835579531107/4503599627370496)), (104639791/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67924297/33554432), (-691091129/16777216)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-69107565/33554432), (-1406260421/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-552307916405695/9007199254740992), (503490857116259/4503599627370496)), (102505547/4503599627370496), by norm_num⟩
  | 1 => ⟨((197239715/1073741824), (-719224839/2147483648)), (37/536870912), by norm_num⟩
  | 2 => ⟨((-147719345/536870912), (1077302531/2147483648)), (223/2147483648), by norm_num⟩
  | 3 => ⟨((147509203/536870912), (-1075769987/2147483648)), (225/2147483648), by norm_num⟩
  | 4 => ⟨((-13809315/67108864), (805679717/2147483648)), (85/1073741824), by norm_num⟩
  | 5 => ⟨((66190417/536870912), (-241360073/1073741824)), (205/4294967296), by norm_num⟩
  | 6 => ⟨((-528770049/8589934592), (15063545/134217728)), (207/8589934592), by norm_num⟩
  | 7 => ⟨((452586715/17179869184), (-825167505/17179869184)), (179/17179869184), by norm_num⟩
  | 8 => ⟨((-338957157/34359738368), (1235990463/68719476736)), (135/34359738368), by norm_num⟩
  | 9 => ⟨((451299953/137438953472), (-822821449/137438953472)), (181/137438953472), by norm_num⟩
  | 10 => ⟨((-270394767/274877906944), (246495277/137438953472)), (219/549755813888), by norm_num⟩
  | 11 => ⟨((589112967/2199023255552), (-537042805/1099511627776)), (241/2199023255552), by norm_num⟩
  | 12 => ⟨((-588274909/8796093022208), (536278821/4398046511104)), (243/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395323238131949/2535301200456458802993406410752), (2699624508691/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778786827851371/633825300114114700748351602688), (3194944622301/633825300114114700748351602688)), (92515/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944880951541821/19807040628566084398385987584), (3593655686815/39614081257132168796771975168)), (104099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889537892535587/2475880078570760549798248448), (119295497007/77371252455336267181195264)), (110629/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885601881502917/77371252455336267181195264), (238534525105/9671406556917033397649408)), (110655/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387391320321777/2417851639229258349412352), (1788529053327/4835703278458516698824704)), (103767/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629399327673523/302231454903657293676544), (3128966299951/604462909807314587353088)), (90825/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887807495503781/75557863725914323419136), (5082771575021/75557863725914323419136)), (73821/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297550382100787/4722366482869645213696), (3810505333091/4722366482869645213696)), (110777/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810731035653107/295147905179352825856), (5236889044889/590295810358705651712)), (76197/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227936307475403/9223372036854775808), (1635569800907/18446744073709551616)), (190603/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822672498535565/9223372036854775808), (3677398765083/4611686018427387904)), (26823/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796959116581977/576460752303423488), (7348218163285/1152921504606846976)), (26847/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194518477472521/144115188075855872), (3211147199803/72057594037927936)), (94073/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491537768063859/36028797018963968), (2404665462275/9007199254740992)), (141327/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489122318103409/9007199254740992), (11997492529889/9007199254740992)), (354079/9007199254740992), by norm_num⟩
  | 2 => ⟨((556911261924629/1125899906842624), (5979399960351/1125899906842624)), (710445/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107784475697037/1125899906842624), (35683353654771/2251799813685248)), (1071401/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179345703731459/2251799813685248), (35298512234873/1125899906842624)), (270727/281474976710656), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2179345703731459/2251799813685248), (35298512234873/1125899906842624)), (1032741547704601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((16461012263369/17592186044416), (68325488366823/1125899906842624)), (1082015/562949953421312), by norm_num⟩
  | 2 => ⟨((981618306064569/1125899906842624), (255728696608219/2251799813685248)), (8624833/2251799813685248), by norm_num⟩
  | 3 => ⟨((841304987661075/1125899906842624), (445915251348801/2251799813685248)), (8499071/1125899906842624), by norm_num⟩
  | 4 => ⟨((1168991977737185/2251799813685248), (333200778109955/1125899906842624)), (32135161/2251799813685248), by norm_num⟩
  | 5 => ⟨((51206328615193/281474976710656), (691907041148321/2251799813685248)), (104770713/4503599627370496), by norm_num⟩
  | 6 => ⟨((-552307916405695/9007199254740992), (503490857116259/4503599627370496)), (102505547/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69107565/33554432), (-1406260421/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-35116545/16777216), (-1429163561/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((99904063518635/4503599627370496), (1092494863217709/9007199254740992)), (84182779/4503599627370496), by norm_num⟩
  | 1 => ⟨((-36258717/536870912), (-396505013/1073741824)), (247/4294967296), by norm_num⟩
  | 2 => ⟨((220780955/2147483648), (1207168409/2147483648)), (189/2147483648), by norm_num⟩
  | 3 => ⟨((-56014381/536870912), (-1225083769/2147483648)), (97/1073741824), by norm_num⟩
  | 4 => ⟨((10658565/134217728), (233112189/536870912)), (149/2147483648), by norm_num⟩
  | 5 => ⟨((-103840769/2147483648), (-70971529/268435456)), (183/4294967296), by norm_num⟩
  | 6 => ⟨((210763701/8589934592), (1152396867/8589934592)), (187/8589934592), by norm_num⟩
  | 7 => ⟨((-91667831/8589934592), (-501214017/8589934592)), (41/4294967296), by norm_num⟩
  | 8 => ⟨((8721399/2147483648), (1525957321/68719476736)), (63/17179869184), by norm_num⟩
  | 9 => ⟨((-94408871/68719476736), (-64525157/8589934592)), (43/34359738368), by norm_num⟩
  | 10 => ⟨((229943941/549755813888), (1257269045/549755813888)), (211/549755813888), by norm_num⟩
  | 11 => ⟨((-254570723/2199023255552), (-347980347/549755813888)), (59/549755813888), by norm_num⟩
  | 12 => ⟨((258348759/8796093022208), (1412578633/8796093022208)), (121/4398046511104), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581249258687947/10141204801825835211973625643008), (905252546125/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778738124923269/633825300114114700748351602688), (2142573264141/633825300114114700748351602688)), (92411/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472426823205375/9903520314283042199192993792), (2409951684463/39614081257132168796771975168)), (12997/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889480103157915/2475880078570760549798248448), (80000834919/77371252455336267181195264)), (55245/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771146236711947/154742504910672534362390528), (1279705792667/77371252455336267181195264)), (27627/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549511629743389/9671406556917033397649408), (2398794962183/9671406556917033397649408)), (25905/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258751989412181/604462909807314587353088), (2098292393923/604462909807314587353088)), (45343/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887732186390169/75557863725914323419136), (3408500821071/75557863725914323419136)), (18425/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297494357512017/4722366482869645213696), (319413095459/590295810358705651712)), (55291/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810692889881331/295147905179352825856), (1755902357873/295147905179352825856)), (152099/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823396207444645/73786976294838206464), (17137298021/288230376151711744)), (190199/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822567991573051/9223372036854775808), (4931958652415/9223372036854775808)), (214077/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796907815822849/576460752303423488), (1231870772435/288230376151711744)), (107103/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194430840329857/144115188075855872), (2153258690167/72057594037927936)), (23447/18014398509481984), by norm_num⟩
  | 4 => ⟨((93213161227405/2251799813685248), (6449727127015/36028797018963968)), (35207/4503599627370496), by norm_num⟩
  | 3 => ⟨((372242693857429/2251799813685248), (8044599563975/9007199254740992)), (352581/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227364191535407/4503599627370496), (16036626192885/4503599627370496)), (706697/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215202893137801/2251799813685248), (11961937116483/1125899906842624)), (132987/281474976710656), by norm_num⟩
  | 0 => ⟨((34044256507309/35184372088832), (5915710925099/281474976710656)), (1071625/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((34044256507309/35184372088832), (5915710925099/281474976710656)), (4087924961570357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1053617410731811/1125899906842624), (22896072113913/562949953421312)), (2118845/1125899906842624), by norm_num⟩
  | 2 => ⟨((492056496758863/562949953421312), (171409199485523/2251799813685248)), (8275971/2251799813685248), by norm_num⟩
  | 3 => ⟨((1707315365694755/2251799813685248), (299646566088141/2251799813685248)), (15727473/2251799813685248), by norm_num⟩
  | 4 => ⟨((313653291491467/562949953421312), (227192125805665/1125899906842624)), (28034855/2251799813685248), by norm_num⟩
  | 5 => ⟨((151832896045091/562949953421312), (1012659226658603/4503599627370496)), (85107913/4503599627370496), by norm_num⟩
  | 6 => ⟨((99904063518635/4503599627370496), (1092494863217709/9007199254740992)), (84182779/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-35116545/16777216), (-1429163561/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile041Terms2
